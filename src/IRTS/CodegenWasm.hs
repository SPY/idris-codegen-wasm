{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
module IRTS.CodegenWasm (codegenWasm) where

import Control.Monad.Reader (Reader, runReader, asks)
import Control.Monad.State (StateT, get, put, runStateT)
import Numeric.Natural (Natural)
import Data.Word (Word8, Word16, Word32, Word64)
import Data.Int (Int32, Int64)
import Data.Bits ((.&.))
import qualified Data.Char as Char
import Data.Monoid ((<>), mempty)

import qualified Data.Serialize as Serialize
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.UTF8 as UTF8
import qualified Data.ByteString.Builder as Builder

import Idris.Core.TT (Name, Const(..), isTypeConst)
import IRTS.Bytecode
import IRTS.CodegenCommon

import Language.Wasm.Structure
import qualified Language.Wasm.Binary as WasmBinary

type TypeIndex = Natural

codegenWasm :: CodeGenerator
codegenWasm ci = do
    let bc = map toBC $ simpleDecls ci
    let wasmModule = mkWasm bc (1024 * 1024)
    LBS.writeFile (outputFile ci) $ WasmBinary.dumpModuleLazy wasmModule

mkWasm :: [(Name, [BC])] -> Int -> Module
mkWasm defs stackSize = 
    let (funcs, st) = runWasmGen emptyState bindings $ mapM (mkFunc entryPointTypeIdx . snd) defs in
    let GS { constSectionEnd, constSection } = st in
    emptyModule {
        mems = [
            Memory $ Limit 10 Nothing
        ],
        datas = [
            DataSegment 0 [I32Const 0] $ Builder.toLazyByteString constSection
        ],
        types = [
            FuncType [I32] [] -- def type: (stackbase: i32) => void
        ],
        globals = [
            Global (Const I32) [I32Const $ fromIntegral constSectionEnd], -- stack start
            Global (Const I32) [I32Const $ constSectionEnd + fromIntegral stackSize], -- stack end
            Global (Mut I32) [I32Const $ fromIntegral constSectionEnd], -- stack base
            Global (Mut I32) [I32Const $ fromIntegral constSectionEnd], -- stack top
            Global (Mut I32) [I32Const 0], -- return value
            Global (Mut I32) [I32Const 0] -- tmp
        ],
        functions = funcs
    }
    where
        entryPointTypeIdx = 0
        bindings = GB {
            stackStartIdx = 0,
            stackEndIdx = 1,
            stackBaseIdx = 2,
            stackTopIdx = 3,
            returnValueIdx = 4,
            tmpIdx = 5
        }

data GenState = GS {
    constSectionEnd :: Word32,
    constSection :: Builder.Builder
}

emptyState :: GenState
emptyState = GS 0 mempty

data GlobalBindings = GB {
    stackBaseIdx :: GlobalIndex,
    stackTopIdx :: GlobalIndex,
    stackStartIdx :: GlobalIndex,
    stackEndIdx :: GlobalIndex,
    returnValueIdx :: GlobalIndex,
    tmpIdx :: GlobalIndex
}

type WasmGen = StateT GenState (Reader GlobalBindings)

runWasmGen :: GenState -> GlobalBindings -> WasmGen a -> (a, GenState)
runWasmGen st bindings = flip runReader bindings . flip runStateT st

mkFunc :: TypeIndex -> [BC] -> WasmGen Function
mkFunc typeIdx byteCode = Function typeIdx [I32] <$> concat <$> mapM bcToInstr byteCode

bcToInstr :: BC -> WasmGen [Instruction]
bcToInstr (ASSIGN l r) = getRegVal r >>= setRegVal l
bcToInstr (ASSIGNCONST reg c) = makeConst c >>= setRegVal reg
bcToInstr (UPDATE l r) = getRegVal r >>= setRegVal l
bcToInstr _ = return []

getRegVal :: Reg -> WasmGen [Instruction]
getRegVal RVal = do
    idx <- asks returnValueIdx
    return [GetGlobal idx]
getRegVal Tmp = do
    idx <- asks tmpIdx
    return [GetGlobal idx]
getRegVal (L offset) = do
    idx <- asks stackBaseIdx
    return [GetGlobal idx, I32Load (MemArg (fromIntegral offset * 4) 2)]
getRegVal (T offset) = do
    idx <- asks stackTopIdx
    return [GetGlobal idx, I32Load (MemArg (fromIntegral offset * 4) 2)]

setRegVal :: Reg -> [Instruction] -> WasmGen [Instruction]
setRegVal RVal val = do
    idx <- asks returnValueIdx
    return $ val ++ [SetGlobal idx]
setRegVal Tmp val = do
    idx <- asks tmpIdx
    return $ val ++ [SetGlobal idx]
setRegVal (L offset) val = do
    idx <- asks stackBaseIdx
    return $ [GetGlobal idx] ++ val ++ [I32Store (MemArg (fromIntegral offset * 4) 2)]
setRegVal (T offset) val = do
    idx <- asks stackTopIdx
    return $ [GetGlobal idx] ++ val ++ [I32Store (MemArg (fromIntegral offset * 4) 2)]

asAddr :: WasmGen Word32 -> WasmGen [Instruction]
asAddr expr = do
    addr <- expr
    return [I32Const addr]

makeConst :: Const -> WasmGen [Instruction]
makeConst (I i) = asAddr $ addToConstSection (mkInt i)
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
    let gap = Builder.lazyByteString $ LBS.replicate (fromIntegral $ asz - sz) 0
    put $ GS (addr + asz) (builder <> Builder.lazyByteString bytes <> gap)
    return addr

data ValType
    = Int
    | BigInt
    | Float
    | String
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