{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module IRTS.CodegenWasm (codegenWasm) where

import Control.Monad (forM_)
import Control.Monad.Reader (Reader, runReader, asks)
import Control.Monad.State (StateT, get, gets, put, modify, runStateT)
import Numeric.Natural (Natural)
import Data.Word (Word8, Word16, Word32, Word64)
import Data.Int (Int32, Int64)
import Data.Bits ((.&.))
import qualified Data.Char as Char
import qualified Data.Map as Map
import Data.Monoid ((<>), mempty)
import Data.Proxy
import Prelude hiding (and)

import qualified Data.Serialize as Serialize
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.UTF8 as UTF8
import qualified Data.ByteString.Builder as BSBuilder

import Idris.Core.TT (Name(..), Const(..), NativeTy(..), IntTy(..), ArithTy(..), isTypeConst)
import IRTS.Bytecode
import IRTS.CodegenCommon
import IRTS.Lang (PrimFn(..))

import Language.Wasm.Structure
import qualified Language.Wasm.Binary as WasmBinary
import Language.Wasm.Builder

codegenWasm :: CodeGenerator
codegenWasm ci = do
    let bc = map toBC $ simpleDecls ci
    let wasmModule = mkWasm bc (1024 * 1024) (128 * 1024)
    LBS.writeFile (outputFile ci) $ WasmBinary.dumpModuleLazy wasmModule

mkWasm :: [(Name, [BC])] -> Int -> Int -> Module
mkWasm defs stackSize heapSize =
    genMod $ do
        gc <- importFunction "rts" "gc" (FuncType [I32] [])
        raiseError <- importFunction "rts" "raiseError" (FuncType [I32] [])
        strEq <- importFunction "rts" "strEq" (FuncType [I32, I32] [I32])
        strHead <- importFunction "rts" "strHead" (FuncType [I32] [I32])
        strConcat <- importFunction "rts" "strConcat" (FuncType [I32, I32] [I32])
        strWrite <- importFunction "rts" "strWrite" (FuncType [I32] [I32])
        intStr <- importFunction "rts" "intStr" (FuncType [I32] [I32])
        exportMemory "mem" =<< memory 20 Nothing
    
        stackStart <- exportGlobal "stackStart" =<< global Const i32 0
        stackEnd <- global Const i32 0
        stackBase <- global Mut i32 0
        stackTop <- global Mut i32 0
    
        retReg <- global Mut i32 0
        tmpReg <- global Mut i32 0
    
        heapStart <- global Mut i32 0
        heapNext <- global Mut i32 0
        heapEnd <- global Mut i32 0
    
        exportFunction "getHeapStart" =<< (fun $ do
            result i32
            ret heapStart)
        exportFunction "setHeapStart" =<< (fun $ do
            val <- param i32
            heapStart .= val)
        exportFunction "getHeapEnd" =<< (fun $ do
            result i32
            ret heapEnd)
        exportFunction "setHeapEnd" =<< (fun $ do
            val <- param i32
            heapEnd .= val)
        
        aligned <- fun $ do
            size <- param i32
            result i32
            (size `add` i32c 3) `and` i32c 0xFFFFFFFC
        alloc <- exportFunction "alloc" =<< (funRec $ \self -> do
            size <- param i32
            result i32
            alignedSize <- local i32
            addr <- local i32
            i <- local i32
            alignedSize .= call i32 aligned [arg size]
            ifExpr i32 ((heapNext `add` alignedSize) `lt_u` heapEnd)
                (const $ do
                    addr .= heapNext
                    heapNext .= (heapNext `add` alignedSize)
                    for (i .= addr) (i `lt_u` heapNext) (i .= (i `add` i32c 4)) $ const $ do
                        store i (i32c 0) 0 2
                    store addr size 4 2
                    ret addr
                )
                (const $ do
                    invoke gc [arg size]
                    call i32 self [arg size]
                )
            )
        slide <- fun $ do
            n <- param i32
            source <- local i32
            dist <- local i32
            end <- local i32
            dist .= stackBase
            end .= (stackTop `add` (n `mul` i32c 4))
            for (source .= stackTop) (source `lt_u` end) (source .= (source `add` i32c 4)) $ const $ do
                store source dist 0 2
                dist .= (dist `add` i32c 4)
        reserve <- fun $ do
            num <- param i32
            i <- local i32
            newStackTop <- local i32
            newStackTop .= (stackTop `add` (num `mul` i32c 4))
            ifStmt (stackEnd `lt_u` newStackTop)
                (const unreachable)
                (const $ for (i .= stackTop) (i `lt_u` newStackTop) (i .= (i `add` i32c 4)) $ const $ do
                    store i (i32c 0) 0 2
                )
        defsStartFrom <- nextFuncIndex
        let bindings = GB {
                stackStartIdx = stackStart,
                stackEndIdx = stackEnd,
                stackBaseIdx = stackBase,
                stackTopIdx = stackTop,
                returnValueIdx = retReg,
                tmpIdx = tmpReg,
                raiseErrorFn = raiseError,
                allocFn = alloc,
                slideFn = slide,
                reserveFn = reserve,
                strEqFn = strEq,
                strHeadFn = strHead,
                strConcatFn = strConcat,
                strWriteFn = strWrite,
                intStrFn = intStr,
                symbols = Map.fromList $ zipWith (,) (map fst defs) [defsStartFrom..]
            }
        let (funcs, st) = runWasmGen emptyState bindings $ mapM (mkFunc . snd) defs
        let GS { constSectionEnd, constSection } = st
        sequence_ funcs
        case Map.lookup (MN 0 "runMain") $ symbols bindings of
            Just idx -> exportFunction "main" idx >> return ()
            Nothing -> return ()
        setGlobalInitializer stackStart $ fromIntegral constSectionEnd
        setGlobalInitializer stackEnd $ fromIntegral constSectionEnd + fromIntegral stackSize
        setGlobalInitializer stackBase $ fromIntegral constSectionEnd
        setGlobalInitializer stackTop $ fromIntegral constSectionEnd
        setGlobalInitializer heapStart $ fromIntegral constSectionEnd + fromIntegral stackSize
        setGlobalInitializer heapNext $ fromIntegral constSectionEnd + fromIntegral stackSize
        setGlobalInitializer heapEnd $ fromIntegral constSectionEnd + fromIntegral (stackSize + heapSize)
        dataSegment (i32c 0) $ BSBuilder.toLazyByteString constSection
        return ()

data GenState = GS {
    constSectionEnd :: Word32,
    constSection :: BSBuilder.Builder,
    strCache :: Map.Map String Word32
}

emptyState :: GenState
emptyState = GS 0 mempty mempty

data GlobalBindings = GB {
    stackBaseIdx :: Glob I32,
    stackTopIdx :: Glob I32,
    stackStartIdx :: Glob I32,
    stackEndIdx :: Glob I32,
    returnValueIdx :: Glob I32,
    tmpIdx :: Glob I32,
    symbols :: Map.Map Name Natural,
    raiseErrorFn :: Natural,
    slideFn :: Natural,
    reserveFn :: Natural,
    allocFn :: Natural,
    strEqFn :: Natural,
    strHeadFn :: Natural,
    strConcatFn :: Natural,
    strWriteFn :: Natural,
    intStrFn :: Natural
}

type WasmGen = StateT GenState (Reader GlobalBindings)

runWasmGen :: GenState -> GlobalBindings -> WasmGen a -> (a, GenState)
runWasmGen st bindings = flip runReader bindings . flip runStateT st

mkFunc :: [BC] -> WasmGen (GenMod Natural)
mkFunc byteCode = do
    body <- mapM bcToInstr byteCode
    return $ fun $ do
        oldBase <- param i32
        myOldBase <- local i32
        sequence_ $ map ($ (oldBase, myOldBase)) body

bcToInstr :: BC -> WasmGen ((Loc I32, Loc I32) -> GenFun ())
bcToInstr (ASSIGN l r) = const <$> (getRegVal r >>= setRegVal l)
bcToInstr (ASSIGNCONST reg c) = const <$> (makeConst c >>= setRegVal reg)
bcToInstr (UPDATE l r) = const <$> (getRegVal r >>= setRegVal l)
bcToInstr (MKCON l _ tag args) = const <$> (genCon tag args >>= setRegVal l)
bcToInstr (CASE safe val branches defaultBranch) = genCase safe val branches defaultBranch
bcToInstr (PROJECT loc offset arity) = genProject loc offset arity
bcToInstr (PROJECTINTO dst src idx) = do
    addr <- getRegVal src
    const <$> setRegVal dst (load i32 addr (12 + idx * 4) 2)
bcToInstr (CONSTCASE val branches defaultBranch) = genConstCase val branches defaultBranch
bcToInstr (CALL n) = do
    Just fnIdx <- Map.lookup n <$> asks symbols
    return $ \(_, myOldBase) -> invoke fnIdx [arg myOldBase]
bcToInstr (TAILCALL n) = do
    Just fnIdx <- Map.lookup n <$> asks symbols
    return $ \(oldBase, _) -> invoke fnIdx [arg oldBase]
bcToInstr (SLIDE n)
    | n == 0 = return $ const $ return ()
    | n <= 4 = genSlide n
    | otherwise = do
        slide <- asks slideFn
        return $ const $ invoke slide [i32c n]
bcToInstr REBASE = do
    stackBase <- asks stackBaseIdx
    return $ \(oldBase, _) -> stackBase .= oldBase
bcToInstr (RESERVE n)
    | n == 0 = return $ const $ return ()
    | n <= 4 = genReserve n
    | otherwise = do
        reserve <- asks reserveFn
        return $ const $ invoke reserve [i32c n]
bcToInstr (ADDTOP 0) = return $ const $ return ()
bcToInstr (ADDTOP n) = do
    stackTop <- asks stackTopIdx
    return $ const $ stackTop .= (stackTop `add` i32c (n * 4))
bcToInstr (TOPBASE 0) = do
    stackBase <- asks stackBaseIdx
    stackTop <- asks stackTopIdx
    return $ const $ stackTop .= stackBase
bcToInstr (TOPBASE n) = do
    stackBase <- asks stackBaseIdx
    stackTop <- asks stackTopIdx
    return $ const $ stackTop .= (stackBase `add` i32c (n * 4))
bcToInstr (BASETOP 0) = do
    stackBase <- asks stackBaseIdx
    stackTop <- asks stackTopIdx
    return $ const $ stackBase .= stackTop
bcToInstr (BASETOP n) = do
    stackBase <- asks stackBaseIdx
    stackTop <- asks stackTopIdx
    return $ const $ stackBase .= (stackTop `add` i32c (n * 4))
bcToInstr STOREOLD = do
    stackBase <- asks stackBaseIdx
    return $ \(_, myOldBase) -> myOldBase .= stackBase
bcToInstr (OP loc op args) = const <$> makeOp loc op args
bcToInstr (NULL reg) = const <$> setRegVal reg (i32c 0)
bcToInstr (ERROR str) = do
    raiseError <- asks raiseErrorFn
    strAddr <- makeConst (Str str)
    return $ const $ invoke raiseError [strAddr]
bcToInstr _ = return $ const $ return ()

getRegVal :: Reg -> WasmGen (GenFun (Proxy I32))
getRegVal RVal = do
    idx <- asks returnValueIdx
    return $ produce idx
getRegVal Tmp = do
    idx <- asks tmpIdx
    return $ produce idx
getRegVal (L offset) = do
    idx <- asks stackBaseIdx
    return $ load i32 idx (offset * 4) 2
getRegVal (T offset) = do
    idx <- asks stackTopIdx
    return $ load i32 idx (offset * 4) 2

setRegVal :: (Producer expr, OutType expr ~ Proxy I32) => Reg -> expr -> WasmGen (GenFun ())
setRegVal RVal val = do
    idx <- asks returnValueIdx
    return $ idx .= val
setRegVal Tmp val = do
    idx <- asks tmpIdx
    return $ idx .= val
setRegVal (L offset) val = do
    idx <- asks stackBaseIdx
    return $ store idx val (offset * 4) 2
setRegVal (T offset) val = do
    idx <- asks stackTopIdx
    return $ store idx val (offset * 4) 2

genCase :: Bool -> Reg -> [(Int, [BC])] -> Maybe [BC] -> WasmGen ((Loc I32, Loc I32) -> GenFun ())
genCase safe reg branches defaultBranch = do
    addr <- getRegVal reg
    branchesBody <- mapM toFunGen branches
    defBody <- case defaultBranch of
        Just code -> mapM bcToInstr code
        Nothing -> return $ [const $ return ()]
    return $ \oldBases -> do
        let defCode = sequence_ $ map ($ oldBases) defBody
        let branchesCode = map (\(tag, code) -> (tag, code oldBases)) branchesBody
        let conCheck = load8u i32 addr 0 0 `eq` i32c (fromEnum Con)
        let conTag = load i32 addr 8 2
        let conGuard body
                | safe = body
                | otherwise = ifStmt conCheck (const body) (const defCode)
        let genSwitch [] = defCode
            genSwitch ((tag, code):rest) = ifStmt (conTag `eq` i32c tag) (const code) $ const $ genSwitch rest
        conGuard $ genSwitch branchesCode
    where
        toFunGen :: (Int, [BC]) -> WasmGen (Int, ((Loc I32, Loc I32) -> GenFun ()))
        toFunGen (tag, code) = do
            instrs <- mapM bcToInstr code
            return $ (tag, (\oldBases -> sequence_ $ map ($ oldBases) instrs))

genProject :: Reg -> Int -> Int -> WasmGen ((Loc I32, Loc I32) -> GenFun ())
genProject reg offset arity = do
    stackBase <- asks stackBaseIdx
    addr <- getRegVal reg
    return $ const $ forM_ [0..arity-1] $ \i -> do
        store stackBase (load i32 addr (12 + i * 4) 2) ((offset + i) * 4) 2

genConstCase :: Reg -> [(Const, [BC])] -> Maybe [BC] -> WasmGen ((Loc I32, Loc I32) -> GenFun ())
genConstCase reg branches defaultBranch = do
    addr <- getRegVal reg
    branchesBody <- mapM (toFunGen addr) branches
    defBody <- case defaultBranch of
        Just code -> mapM bcToInstr code
        Nothing -> return $ [const $ return ()]
    return $ \oldBases -> do
        let defCode = sequence_ $ map ($ oldBases) defBody
        let branchesCode = map (\(cond, code) -> (cond, code oldBases)) branchesBody
        let genSwitch [] = defCode
            genSwitch ((cond, code):rest) = ifStmt cond (const code) (const $ genSwitch rest)
        genSwitch branchesCode
    where
        toFunGen :: GenFun (Proxy I32) -> (Const, [BC]) -> WasmGen (GenFun (Proxy I32), ((Loc I32, Loc I32) -> GenFun ()))
        toFunGen addr (c, code) = do
            instrs <- mapM bcToInstr code
            constCode <- makeConst c
            cond <- mkConstChecker c addr constCode
            return $ (cond, (\oldBases -> sequence_ $ map ($ oldBases) instrs))

        mkConstChecker :: Const -> GenFun (Proxy I32) -> GenFun (Proxy I32) -> WasmGen (GenFun (Proxy I32))
        mkConstChecker c val pat | intConst c = return $ eq (load i32 val 8 2) (load i32 pat 8 2)
        mkConstChecker c val pat | int64Const c = return $ eq (load i64 val 8 2) (load i64 pat 8 2)
        mkConstChecker c val pat | bigIntConst c = return $ eq (load i64 val 8 2) (load i64 pat 8 2)
        mkConstChecker c val pat | strConst c = do
            strEq <- asks strEqFn
            return $ call i32 strEq [val, pat]
        mkConstChecker _ _valAddr _constAddr = return $ i32c 0

        intConst (I _) = True
        intConst (Ch _) = True
        intConst (B8 _) = True
        intConst (B16 _) = True
        intConst (B32 _) = True
        intConst _ = False

        int64Const (B64 _) = True
        int64Const _ = False
    
        bigIntConst (BI _) = True
        bigIntConst _ = False
    
        strConst (Str _) = True
        strConst _ = False

genSlide :: Int -> WasmGen ((Loc I32, Loc I32) -> GenFun ())
genSlide n = do
    stackBase <- asks stackBaseIdx
    stackTop <- asks stackTopIdx
    return $ const $ forM_ [0..n-1] $ \i -> do
        store stackBase (load i32 stackTop (i * 4) 2) (i * 4) 2

genReserve :: Int -> WasmGen ((Loc I32, Loc I32) -> GenFun ())
genReserve n = do
    stackTop <- asks stackTopIdx
    stackEnd <- asks stackEndIdx
    return $ const $ do
        ifStmt (stackEnd `lt_u` (stackTop `add` i32c (n * 4)))
            (const unreachable)
            (const $ forM_ [0..n-1] $ \i -> store stackTop (i32c 0) (i * 4) 2)

{-
data PrimFn = LPlus ArithTy | LMinus ArithTy | LTimes ArithTy
    | LUDiv IntTy | LSDiv ArithTy | LURem IntTy | LSRem ArithTy
    | LAnd IntTy | LOr IntTy | LXOr IntTy | LCompl IntTy
    | LSHL IntTy | LLSHR IntTy | LASHR IntTy
    | LEq ArithTy | LLt IntTy | LLe IntTy | LGt IntTy | LGe IntTy
    | LSLt ArithTy | LSLe ArithTy | LSGt ArithTy | LSGe ArithTy
    | LSExt IntTy IntTy | LZExt IntTy IntTy | LTrunc IntTy IntTy
    | LStrConcat | LStrLt | LStrEq | LStrLen
    | LIntFloat IntTy | LFloatInt IntTy | LIntStr IntTy | LStrInt IntTy
    | LFloatStr | LStrFloat | LChInt IntTy | LIntCh IntTy
    | LBitCast ArithTy ArithTy -- Only for values of equal width

    | LFExp | LFLog | LFSin | LFCos | LFTan | LFASin | LFACos | LFATan
    | LFATan2 | LFSqrt | LFFloor | LFCeil | LFNegate

    | LStrHead | LStrTail | LStrCons | LStrIndex | LStrRev | LStrSubstr
    | LReadStr | LWriteStr

    -- system info
    | LSystemInfo

    | LFork
    | LPar -- evaluate argument anywhere, possibly on another
            -- core or another machine. 'id' is a valid implementation
    | LExternal Name
    | LCrash

    | LNoOp
-}
-- data NativeTy = IT8 | IT16 | IT32 | IT64
-- data IntTy = ITFixed NativeTy | ITNative | ITBig | ITChar
-- data ArithTy = ATInt IntTy | ATFloat
makeOp :: Reg -> PrimFn -> [Reg] -> WasmGen (GenFun ())
makeOp loc (LPlus (ATInt (ITFixed IT8))) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ add l r) args
makeOp loc (LMinus (ATInt (ITFixed IT8))) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ sub l r) args
makeOp loc (LTimes (ATInt (ITFixed IT8))) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ mul l r) args
makeOp loc (LEq (ATInt (ITFixed IT8))) args =
    i32BinOp loc eq args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LSLt (ATInt (ITFixed IT8))) args =
    i32BinOp loc lt_s args -- do not need clipping for relation ops, coz result 0 or 1

makeOp loc (LPlus (ATInt (ITFixed IT16))) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ add l r) args
makeOp loc (LMinus (ATInt (ITFixed IT16))) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ sub l r) args
makeOp loc (LTimes (ATInt (ITFixed IT16))) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ mul l r) args
makeOp loc (LEq (ATInt (ITFixed IT16))) args =
    i32BinOp loc eq args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LSLt (ATInt (ITFixed IT16))) args =
    i32BinOp loc lt_s args -- do not need clipping for relation ops, coz result 0 or 1

makeOp loc (LPlus (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc add args
makeOp loc (LMinus (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc sub args
makeOp loc (LTimes (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc mul args
makeOp loc (LEq (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc eq args
makeOp loc (LSLt (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc lt_s args

makeOp loc (LPlus (ATInt (ITFixed IT64))) args =
    i64BinOp loc add args
makeOp loc (LMinus (ATInt (ITFixed IT64))) args =
    i64BinOp loc sub args
makeOp loc (LTimes (ATInt (ITFixed IT64))) args =
    i64BinOp loc mul args
makeOp loc (LEq (ATInt (ITFixed IT64))) args =
    i64BinOp loc ((extend_u .) . eq) args
makeOp loc (LSLt (ATInt (ITFixed IT64))) args =
    i64BinOp loc ((extend_u .) . lt_s) args

makeOp loc (LPlus (ATInt ITBig)) args =
    bigBinOp loc add args
makeOp loc (LMinus (ATInt ITBig)) args =
    bigBinOp loc sub args
makeOp loc (LTimes (ATInt ITBig)) args =
    bigBinOp loc mul args
makeOp loc (LEq (ATInt ITBig)) args =
    bigBinOp loc ((extend_u .) . eq) args
makeOp loc (LSLt (ATInt ITBig)) args =
    bigBinOp loc ((extend_u .) . lt_s) args

makeOp loc (LPlus (ATInt ITNative)) args =
    i32BinOp loc add args
makeOp loc (LMinus (ATInt ITNative)) args =
    i32BinOp loc sub args
makeOp loc (LTimes (ATInt ITNative)) args =
    i32BinOp loc mul args
makeOp loc (LEq (ATInt ITNative)) args =
    i32BinOp loc eq args
makeOp loc (LSLt (ATInt ITNative)) args =
    i32BinOp loc lt_s args
makeOp loc (LIntStr ITNative) [reg] = do
    val <- getRegVal reg
    intStr <- asks intStrFn
    setRegVal loc $ call i32 intStr [val]

makeOp loc (LPlus (ATInt ITChar)) args =
    i32BinOp loc add args
makeOp loc (LMinus (ATInt ITChar)) args =
    i32BinOp loc sub args
makeOp loc (LTimes (ATInt ITChar)) args =
    i32BinOp loc mul args
makeOp loc (LEq (ATInt ITChar)) args =
    i32BinOp loc eq args
makeOp loc (LSLt (ATInt ITChar)) args =
    i32BinOp loc lt_s args

makeOp loc (LPlus ATFloat) args = f64BinOp loc add args
makeOp loc (LMinus ATFloat) args = f64BinOp loc sub args
makeOp loc (LTimes ATFloat) args = f64BinOp loc mul args

makeOp loc LStrEq [l, r] = do
    a <- getRegVal l
    b <- getRegVal r
    strEq <- asks strEqFn
    setRegVal loc $ call i32 strEq [a, b]
makeOp loc LStrConcat [l, r] = do
    a <- getRegVal l
    b <- getRegVal r
    strConcat <- asks strConcatFn
    setRegVal loc $ call i32 strConcat [a, b]
makeOp loc LStrHead [reg] = do
    str <- getRegVal reg
    strHead <- asks strHeadFn
    setRegVal loc $ call i32 strHead [str]
makeOp loc LWriteStr [_, reg] = do
    str <- getRegVal reg
    strWrite <- asks strWriteFn
    setRegVal loc $ call i32 strWrite [str]

makeOp _ _ _ = return $ return ()

i32BinOp :: Reg
    -> (GenFun (Proxy I32) -> GenFun (Proxy I32) -> GenFun (Proxy I32))
    -> [Reg]
    -> WasmGen (GenFun ())
i32BinOp loc op [l, r] = do
    left <- getRegVal l
    right <- getRegVal r
    ctor <- genInt
    setRegVal loc $ ctor $ op (load i32 left 8 2) (load i32 right 8 2)

i32BitBinOp :: Reg
    -> (GenFun (Proxy I32) -> GenFun (Proxy I32) -> GenFun (Proxy I32))
    -> [Reg]
    -> WasmGen (GenFun ())
i32BitBinOp loc op [l, r] = do
    left <- getRegVal l
    right <- getRegVal r
    ctor <- genBit32
    setRegVal loc $ ctor $ op (load i32 left 8 2) (load i32 right 8 2)

i64BinOp :: Reg
    -> (GenFun (Proxy I64) -> GenFun (Proxy I64) -> GenFun (Proxy I64))
    -> [Reg]
    -> WasmGen (GenFun ())
i64BinOp loc op [l, r] = do
    left <- getRegVal l
    right <- getRegVal r
    ctor <- genBit64
    setRegVal loc $ ctor $ op (load i64 left 8 2) (load i64 right 8 2)

bigBinOp :: Reg
    -> (GenFun (Proxy I64) -> GenFun (Proxy I64) -> GenFun (Proxy I64))
    -> [Reg]
    -> WasmGen (GenFun ())
bigBinOp loc op [l, r] = do
    left <- getRegVal l
    right <- getRegVal r
    ctor <- genBigInt
    setRegVal loc $ ctor $ op (load i64 left 8 2) (load i64 right 8 2)

f64BinOp :: Reg
    -> (GenFun (Proxy F64) -> GenFun (Proxy F64) -> GenFun (Proxy F64))
    -> [Reg]
    -> WasmGen (GenFun ())
f64BinOp loc op [l, r] = do
    left <- getRegVal l
    right <- getRegVal r
    ctor <- genFloat
    setRegVal loc $ ctor $ op (load f64 left 8 2) (load f64 right 8 2)

asAddr :: WasmGen Word32 -> WasmGen (GenFun (Proxy I32))
asAddr expr = do
    addr <- expr
    return $ i32c addr

makeConst :: Const -> WasmGen (GenFun (Proxy I32))
makeConst (I i) = asAddr $ addToConstSection (mkInt i)
makeConst (BI i) = asAddr $ addToConstSection (mkBigInt i)
makeConst (Fl f) = asAddr $ addToConstSection (mkFloat f)
makeConst (Ch c) = asAddr $ addToConstSection (mkInt $ Char.ord c)
makeConst (Str s) = do
    cache <- gets strCache
    case Map.lookup s cache of
        Just addr -> return $ i32c addr
        Nothing -> asAddr $ addToConstSection (mkStr s)
makeConst (B8 w) = asAddr $ addToConstSection (mkInt w)
makeConst (B16 w) = asAddr $ addToConstSection (mkInt w)
makeConst (B32 w) = asAddr $ addToConstSection (mkBit32 w)
makeConst (B64 w) = asAddr $ addToConstSection (mkBit64 w)
makeConst c
    | isTypeConst c = asAddr $ addToConstSection (mkInt 42424242)
    | otherwise = error $ "mkConst of (" ++ show c ++ ") not implemented"

aligned :: (Integral i) => i -> Word32
aligned sz = (fromIntegral sz + 3) .&. 0xFFFFFFFC

addToConstSection :: (Serialize.Serialize val) => val -> WasmGen Word32
addToConstSection val = do
    let bytes = Serialize.encodeLazy val
    let sz = fromIntegral $ LBS.length bytes
    let asz = aligned sz
    let alignmentGap = BSBuilder.lazyByteString $ LBS.replicate (fromIntegral $ asz - sz) 0
    addr <- gets constSectionEnd
    modify $ \st -> st {
        constSectionEnd = addr + asz,
        constSection = constSection st <> BSBuilder.lazyByteString bytes <> alignmentGap
    }
    return addr

data ValType
    = Con
    | Int
    | BigInt
    | Float
    | String
    | StrOffset
    | Bit32
    | Bit64
    deriving (Eq, Show, Enum)

data ValHeader = VH {
    ty :: ValType,
    slot8 :: Word8,
    slot16 :: Word16,
    sz :: Word32
} deriving (Show, Eq)

mkHdr :: (Integral i) => ValType -> i -> ValHeader
mkHdr ty sz = VH { ty, slot8 = 0, slot16 = 0, sz = fromIntegral sz }

instance Serialize.Serialize ValHeader where
    put VH { ty, slot8, slot16, sz } = do
        Serialize.putWord8 $ fromIntegral $ fromEnum ty
        Serialize.putWord8 slot8
        Serialize.putWord16le slot16
        Serialize.putWord32le sz
    get = do
        ty <- toEnum . fromIntegral <$> Serialize.getWord8
        slot8 <- Serialize.getWord8
        slot16 <- Serialize.getWord16le
        sz <- Serialize.getWord32le
        return $ VH { ty, slot8, slot16, sz }

data IntVal = IV { hdr :: ValHeader, val :: Int } deriving (Show, Eq)

mkInt :: (Integral i) => i -> IntVal
mkInt val = IV { hdr = mkHdr Int 12, val = fromIntegral val }

genInt :: (Producer val, OutType val ~ Proxy I32) => WasmGen (val -> GenFun (Proxy I32))
genInt = do
    alloc <- asks allocFn
    tmp <- asks tmpIdx
    return $ \val -> do
        tmp .= call i32 alloc [arg $ i32c (8 + 4)]
        store8 tmp (i32c $ fromEnum Int) 0 0
        store tmp val 8 2
        ret tmp

instance Serialize.Serialize IntVal where
    put IV { hdr, val } = do
        Serialize.put hdr
        Serialize.putWord32le $ asWord32 $ fromIntegral val
    get = IV <$> Serialize.get <*> (fromIntegral . asInt32 <$> Serialize.getWord32le)

data FloatVal = FV { hdr :: ValHeader, val :: Double } deriving (Show, Eq)

mkFloat :: Double -> FloatVal
mkFloat val = FV { hdr = mkHdr Float 16, val }

genFloat :: (Producer val, OutType val ~ Proxy F64) => WasmGen (val -> GenFun (Proxy I32))
genFloat = do
    alloc <- asks allocFn
    tmp <- asks tmpIdx
    return $ \val -> do
        tmp .= call i32 alloc [arg $ i32c (8 + 8)]
        store8 tmp (i32c $ fromEnum Float) 0 0
        store tmp val 8 2
        ret tmp

instance Serialize.Serialize FloatVal where
    put FV { hdr, val } = do
        Serialize.put hdr
        Serialize.putFloat64le val
    get = FV <$> Serialize.get <*> Serialize.getFloat64le

data StrVal = SV { hdr :: ValHeader, len :: Word32, val :: LBS.ByteString } deriving (Show, Eq)

mkStr :: String -> StrVal
mkStr str =
    let val = UTF8.fromString str in
    let header = mkHdr String (8 + 4 + LBS.length val) in
    SV {
        hdr = header { slot8 = if null str then 1 else 0 },
        len = fromIntegral (length str),
        val
    }

instance Serialize.Serialize StrVal where
    put SV { hdr, len, val } = do
        Serialize.put hdr
        Serialize.putWord32le len
    get = do
        hdr <- Serialize.get
        len <- Serialize.getWord32le
        val <- Serialize.getLazyByteString (fromIntegral $ sz hdr - 8 - 4)
        return $ SV { hdr, len, val }

data Bit32Val = B32V { hdr :: ValHeader, val :: Word32 } deriving (Show, Eq)

mkBit32 :: Word32 -> Bit32Val
mkBit32 val = B32V { hdr = mkHdr Bit32 12, val }

genBit32 :: (Producer val, OutType val ~ Proxy I32) => WasmGen (val -> GenFun (Proxy I32))
genBit32 = do
    alloc <- asks allocFn
    tmp <- asks tmpIdx
    return $ \val -> do
        tmp .= call i32 alloc [arg $ i32c (8 + 4)]
        store8 tmp (i32c $ fromEnum Bit32) 0 0
        store tmp val 8 2
        ret tmp

instance Serialize.Serialize Bit32Val where
    put B32V { hdr, val } = do
        Serialize.put hdr
        Serialize.putWord32le val
    get = B32V <$> Serialize.get <*> Serialize.getWord32le

data Bit64Val = B64V { hdr :: ValHeader, val :: Word64 } deriving (Show, Eq)

mkBit64 :: Word64 -> Bit64Val
mkBit64 val = B64V { hdr = mkHdr Bit64 16, val }

genBit64 :: (Producer val, OutType val ~ Proxy I64) => WasmGen (val -> GenFun (Proxy I32))
genBit64 = do
    alloc <- asks allocFn
    tmp <- asks tmpIdx
    return $ \val -> do
        tmp .= call i32 alloc [arg $ i32c (8 + 8)]
        store8 tmp (i32c $ fromEnum Bit64) 0 0
        store tmp val 8 2
        ret tmp

instance Serialize.Serialize Bit64Val where
    put B64V { hdr, val } = do
        Serialize.put hdr
        Serialize.putWord64le val
    get = B64V <$> Serialize.get <*> Serialize.getWord64le

-- TODO: emulate Big Nums as i64 for now. Add runtime support for real big numbers
data BigIntVal = BIV { hdr :: ValHeader, val :: Word64 } deriving (Show, Eq)

mkBigInt :: Integer -> BigIntVal
mkBigInt val = BIV { hdr = mkHdr BigInt 16, val = fromIntegral val }

genBigInt :: (Producer val, OutType val ~ Proxy I64) => WasmGen (val -> GenFun (Proxy I32))
genBigInt = do
    alloc <- asks allocFn
    tmp <- asks tmpIdx
    return $ \val -> do
        tmp .= call i32 alloc [arg $ i32c (8 + 8)]
        store8 tmp (i32c $ fromEnum Bit64) 0 0
        store tmp val 8 2
        ret tmp

instance Serialize.Serialize BigIntVal where
    put BIV { hdr, val } = do
        Serialize.put hdr
        Serialize.putWord64le val
    get = BIV <$> Serialize.get <*> Serialize.getWord64le

data ConVal = CV { hdr :: ValHeader, tag :: Word32, args :: [Word32] } deriving (Show, Eq)

mkCon :: Word32 -> [Word32] -> ConVal
mkCon tag args =
    let header = mkHdr Con (8 + 4 + 4 * length args) in
    CV { hdr = header { slot16 = fromIntegral $ length args }, tag, args }

genCon :: (Integral tag) => tag -> [Reg] -> WasmGen (GenFun (Proxy I32))
genCon tag args = do
    let arity = length args
    alloc <- asks allocFn
    tmp <- asks tmpIdx
    args' <- mapM getRegVal args
    return $ do
        tmp .= call i32 alloc [arg $ i32c (8 + 4 + 4 * fromIntegral arity)]
        store8 tmp (i32c $ fromEnum Con) 0 0
        store16 tmp (i32c arity) 2 1
        store tmp (i32c tag) 8 2
        forM_ (zip args' [0..]) $ \(arg, i) -> store tmp arg (8 + 4 + 4 * i) 2
        ret tmp

instance Serialize.Serialize ConVal where
    put CV { hdr, tag, args } = do
        Serialize.put hdr
        Serialize.putWord32le tag
        mapM_ Serialize.putWord32le args
    get = do
        hdr <- Serialize.get
        tag <- Serialize.getWord32le
        args <- sequence $ replicate (fromIntegral $ slot16 hdr) Serialize.getWord32le
        return $ CV { hdr, tag, args }

asWord32 :: Int32 -> Word32
asWord32 i
    | i >= 0 = fromIntegral i
    | otherwise = 0xFFFFFFFF - (fromIntegral (abs i)) + 1

asWord64 :: Int64 -> Word64
asWord64 i
    | i >= 0 = fromIntegral i
    | otherwise = 0xFFFFFFFFFFFFFFFF - (fromIntegral (abs i)) + 1

asInt32 :: Word32 -> Int32
asInt32 w =
    if w < 0x80000000
    then fromIntegral w
    else -1 * fromIntegral (0xFFFFFFFF - w + 1)

asInt64 :: Word64 -> Int64
asInt64 w =
    if w < 0x8000000000000000
    then fromIntegral w
    else -1 * fromIntegral (0xFFFFFFFFFFFFFFFF - w + 1)