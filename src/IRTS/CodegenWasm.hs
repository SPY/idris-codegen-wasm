{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module IRTS.CodegenWasm (codegenWasm) where

import Control.Monad (forM_)
import Control.Monad.Reader (Reader, runReader, asks)
import Control.Monad.State (StateT, get, put, runStateT)
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

import Idris.Core.TT (Name, Const(..), NativeTy(..), IntTy(..), ArithTy(..), isTypeConst)
import IRTS.Bytecode
import IRTS.CodegenCommon
import IRTS.Lang (PrimFn(..))

import Language.Wasm.Structure
import qualified Language.Wasm.Binary as WasmBinary
import Language.Wasm.Builder

type TypeIndex = Natural

codegenWasm :: CodeGenerator
codegenWasm ci = do
    let bc = map toBC $ simpleDecls ci
    let wasmModule = mkWasm bc (1024 * 1024)
    LBS.writeFile (outputFile ci) $ WasmBinary.dumpModuleLazy wasmModule

mkWasm :: [(Name, [BC])] -> Int -> Module
mkWasm defs stackSize =
    genMod $ do
        gc <- importFunction "rts" "gc" (FuncType [I32] [])
        memory 10 Nothing
    
        stackStart <- global Const i32 0
        stackEnd <- global Const i32 0
        stackBase <- global Mut i32 0
        stackTop <- global Mut i32 0
    
        retReg <- global Mut i32 0
        tmpReg <- global Mut i32 0
    
        heapStart <- global Mut i32 0
        heapNext <- global Mut i32 0
        heapEnd <- global Mut i32 0
    
        aligned <- fun $ do
            size <- param i32
            (size `add` i32c 3) `and` i32c 0xFFFFFFFC
        alloc <- funRec $ \self -> do
            size <- param i32
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
                    invoke gc []
                    call i32 self [arg size]
                )
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
        slide <- fun $ do
            n <- param i32
            i <- local i32
            for (i .= i32c 0) (i `lt_u` n) (i .= (i `add` i32c 1)) $ const $ do
                let source = load i32 (stackTop `add` (i `mul` i32c 4)) 0 2
                let dist = stackBase `add` (i `mul` i32c 4)
                store source dist 0 2
        defsStartFrom <- nextFuncIndex
        let bindings = GB {
                stackStartIdx = stackStart,
                stackEndIdx = stackEnd,
                stackBaseIdx = stackBase,
                stackTopIdx = stackTop,
                returnValueIdx = retReg,
                tmpIdx = tmpReg,
                allocFn = alloc,
                reserveFn = reserve,
                slideFn = slide,
                symbols = Map.fromList $ zipWith (,) (map fst defs) [defsStartFrom..]
            }
        let (funcs, st) = runWasmGen emptyState bindings $ mapM (mkFunc . snd) defs
        let GS { constSectionEnd, constSection } = st
        sequence_ funcs
        setGlobalInitializer stackStart $ fromIntegral constSectionEnd
        setGlobalInitializer stackEnd $ fromIntegral constSectionEnd + fromIntegral stackSize
        setGlobalInitializer stackBase $ fromIntegral constSectionEnd
        setGlobalInitializer stackTop $ fromIntegral constSectionEnd
        dataSegment (i32c 0) $ BSBuilder.toLazyByteString constSection
        return ()

data GenState = GS {
    constSectionEnd :: Word32,
    constSection :: BSBuilder.Builder
}

emptyState :: GenState
emptyState = GS 0 mempty

data GlobalBindings = GB {
    stackBaseIdx :: Glob I32,
    stackTopIdx :: Glob I32,
    stackStartIdx :: Glob I32,
    stackEndIdx :: Glob I32,
    returnValueIdx :: Glob I32,
    tmpIdx :: Glob I32,
    symbols :: Map.Map Name Natural,
    reserveFn :: Natural,
    allocFn :: Natural,
    slideFn :: Natural
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
bcToInstr (CALL n) = do
    Just fnIdx <- Map.lookup n <$> asks symbols
    return $ \(_, myOldBase) -> invoke fnIdx [arg myOldBase]
bcToInstr (TAILCALL n) = do
    Just fnIdx <- Map.lookup n <$> asks symbols
    return $ \(oldBase, _) -> invoke fnIdx [arg oldBase]
bcToInstr (SLIDE 0) = return $ const $ return ()
bcToInstr (SLIDE n) = do
    slide <- asks slideFn
    return $ const $ invoke slide [i32c n]
bcToInstr REBASE = do
    stackBase <- asks stackBaseIdx
    return $ \(oldBase, _) -> stackBase .= oldBase
bcToInstr (RESERVE 0) = return $ const $ return ()
bcToInstr (RESERVE n) = do
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

-- data NativeTy = IT8 | IT16 | IT32 | IT64
-- data IntTy = ITFixed NativeTy | ITNative | ITBig | ITChar
-- data ArithTy = ATInt IntTy | ATFloat
makeOp :: Reg -> PrimFn -> [Reg] -> WasmGen (GenFun ())
makeOp loc (LPlus (ATInt (ITFixed IT32))) [l, r] = do
    left <- getRegVal l
    right <- getRegVal r
    setRegVal loc $ add (load i32 left 8 2) (load i32 right 8 2)
-- makeOp loc (LPlus ATFloat) [l, r] = do
--     left <- getRegVal l
--     right <- getRegVal r
--     setRegVal loc $ add (load f64 left 8 2) (load f64 right 8 2)
makeOp _ _ _ = return $ return ()

asAddr :: WasmGen Word32 -> WasmGen (GenFun (Proxy I32))
asAddr expr = do
    addr <- expr
    return $ i32c addr

makeConst :: Const -> WasmGen (GenFun (Proxy I32))
makeConst (I i) = asAddr $ addToConstSection (mkInt i)
makeConst (BI i) = asAddr $ addToConstSection (mkBigInt i)
makeConst (Fl f) = asAddr $ addToConstSection (mkFloat f)
makeConst (Ch c) = asAddr $ addToConstSection (mkInt $ Char.ord c)
makeConst (Str s) = asAddr $ addToConstSection (mkStr s)
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
    GS addr builder <- get
    let sz = fromIntegral $ LBS.length bytes
    let asz = aligned sz
    -- alignment gap
    let gap = BSBuilder.lazyByteString $ LBS.replicate (fromIntegral $ asz - sz) 0
    put $ GS (addr + asz) (builder <> BSBuilder.lazyByteString bytes <> gap)
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

instance Serialize.Serialize IntVal where
    put IV { hdr, val } = do
        Serialize.put hdr
        Serialize.putWord32le $ asWord32 $ fromIntegral val
    get = IV <$> Serialize.get <*> (fromIntegral . asInt32 <$> Serialize.getWord32le)

data FloatVal = FV { hdr :: ValHeader, val :: Double } deriving (Show, Eq)

mkFloat :: Double -> FloatVal
mkFloat val = FV { hdr = mkHdr Float 16, val }

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
mkBit32 val = B32V { hdr = mkHdr Int 12, val }

instance Serialize.Serialize Bit32Val where
    put B32V { hdr, val } = do
        Serialize.put hdr
        Serialize.putWord32le val
    get = B32V <$> Serialize.get <*> Serialize.getWord32le

data Bit64Val = B64V { hdr :: ValHeader, val :: Word64 } deriving (Show, Eq)

mkBit64 :: Word64 -> Bit64Val
mkBit64 val = B64V { hdr = mkHdr Int 16, val }

instance Serialize.Serialize Bit64Val where
    put B64V { hdr, val } = do
        Serialize.put hdr
        Serialize.putWord64le val
    get = B64V <$> Serialize.get <*> Serialize.getWord64le

-- TODO: emulate Big Nums as i64 for now. Add runtime support for real big numbers
data BigIntVal = BIV { hdr :: ValHeader, val :: Word64 } deriving (Show, Eq)

mkBigInt :: Integer -> BigIntVal
mkBigInt val = BIV { hdr = mkHdr Int 16, val = fromIntegral val }

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
        store8 tmp (i32c $ fromEnum Con) 0 2
        store16 tmp (i32c tag) 2 1
        store tmp (i32c arity) 8 2
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