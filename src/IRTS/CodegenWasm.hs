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
import Data.Bits ((.&.), shift)
import qualified Data.Char as Char
import qualified Data.Map as Map
import Data.Monoid ((<>), mempty)
import Data.Proxy
import Prelude hiding (and, or)
import Data.Maybe (fromMaybe)

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
    let wasmModule = mkWasm bc (64 * 1024) (256 * 1024)
    LBS.writeFile (outputFile ci) $ WasmBinary.dumpModuleLazy wasmModule

mkWasm :: [(Name, [BC])] -> Int -> Int -> Module
mkWasm defs stackSize heapSize =
    genMod $ do
        -- gc <- importFunction "rts" "gc" () [I32]
        raiseError <- importFunction "rts" "raiseError" () [I32]
        strWrite <- importFunction "rts" "strWrite" i32 [I32]
        strRead <- importFunction "rts" "strRead" i32 []
        printVal <- importFunction "rts" "printVal" () [I32]
        strDouble <- importFunction "rts" "strDouble" i32 [I32]
        doubleStr <- importFunction "rts" "doubleStr" i32 [I32]
        expFn <- importFunction "rts" "exp" f64 [F64]
        logFn <- importFunction "rts" "log" f64 [F64]
        sinFn <- importFunction "rts" "sin" f64 [F64]
        cosFn <- importFunction "rts" "cos" f64 [F64]
        tanFn <- importFunction "rts" "tan" f64 [F64]
        asinFn <- importFunction "rts" "asin" f64 [F64]
        acosFn <- importFunction "rts" "acos" f64 [F64]
        atanFn <- importFunction "rts" "atan" f64 [F64]
        atan2Fn <- importFunction "rts" "atan2" f64 [F64]
        systemInfoFn <- importFunction "rts" "systemInfo" i32 [I32]
        export "mem" $ memory 20 Nothing
    
        stackStart <- export "stackStart" $ global Const i32 0
        stackEnd <- export "stackEnd" $ global Const i32 0
        stackBase <- global Mut i32 0
        stackTop <- global Mut i32 0
    
        retReg <- global Mut i32 0
        tmpReg <- global Mut i32 0

        export "getStackTop" $ fun i32 $ ret stackTop
    
        heapStart <- global Mut i32 0
        heapNext <- global Mut i32 0
        heapEnd <- global Mut i32 0
    
        export "getHeapStart" $ fun i32 $ ret heapStart
        export "setHeapStart" $ fun () $ do
            val <- param i32
            heapStart .= val
        export "getHeapNext" $ fun i32 $ ret heapNext
        export "setHeapNext" $ fun () $ do
            val <- param i32
            heapNext .= val
        export "getHeapEnd" $ fun i32 $ ret heapEnd
        export "setHeapEnd" $ fun () $ do
            val <- param i32
            heapEnd .= val
        gc <- declare () [I32]
        aligned <- fun i32 $ do
            size <- param i32
            (size `add` i32c 3) `and` i32c 0xFFFFFFFC
        alloc <- export "alloc" $ funRec i32 $ \self -> do
            size <- param i32
            alignedSize <- local i32
            addr <- local i32
            i <- local i32
            alignedSize .= call aligned [arg size]
            if' i32 ((heapNext `add` alignedSize) `lt_u` heapEnd)
                (do
                    addr .= heapNext
                    heapNext .= heapNext `add` alignedSize
                    for (i .= addr) (i `lt_u` heapNext) (inc 4 i) $ do
                        store i (i32c 0) 0 2
                    store addr size 4 2
                    ret addr
                )
                (do
                    call gc [arg size]
                    call self [arg size]
                )
        memcpy <- fun () $ do
            dst <- param i32
            src <- param i32
            len <- param i32
            i <- local i32
            for (i .= i32c 0) (i `lt_u` len) (inc 1 i) $ do
                store8 (dst `add` i) (load8_u i32 (src `add` i) 0 0) 0 0
        copy <- fun i32 $ do
            addr <- param i32
            newAddr <- local i32
            typeTag <- local i32
            size <- local i32
            when (addr `lt_u` stackStart) $ do
                -- constant section
                finish addr
            when ((addr `and` i32c 1) `eq` i32c 1) $ do
                -- native int
                finish addr
            typeTag .= load8_u i32 addr 0 0
            let isTag tag = typeTag `eq` i32c (fromEnum tag)
            when (isTag Fwd) $ finish $ load i32 addr 8 2
            size .= load i32 addr 4 2
            newAddr .= call alloc [arg size]
            call memcpy [arg newAddr, arg addr, arg size]
            store8 addr (i32c $ fromEnum Fwd) 0 0
            store addr newAddr 8 2
            ret newAddr
        copyNestedValues <- fun () $ do
            arity <- local i32
            i <- local i32
            j <- local i32
            offset <- local i32
            i .= heapStart
            while (i `lt_u` heapNext) $ do
                when (load8_u i32 i 0 0 `eq` i32c (fromEnum Con)) $ do
                    arity .= load16_u i32 i 2 1
                    for (j .= i32c 0) (j `lt_u` arity) (inc 1 j) $ do
                        offset .= i `add` (j `mul` i32c 4)
                        store offset (call copy [load i32 offset 12 2]) 12 2
                i .= i `add` call aligned [load i32 i 4 2]
        implement gc $ do
            requestedSize <- param i32
            heapSize <- local i32
            i <- local i32
            heapSize .= heapEnd `sub` heapStart
            if' () (heapSize `le_u` (heapStart `sub` stackEnd))
                (do
                    heapStart .= stackEnd
                    heapNext .= stackEnd
                    heapEnd .= stackEnd `add` heapSize
                )
                (do
                    heapStart .= heapEnd
                    heapNext .= heapEnd
                    heapEnd .= heapEnd `add` heapSize
                )
            for (i .= stackStart) (i `lt_u` stackTop) (inc 4 i) $ do
                store i (call copy [load i32 i 0 2]) 0 2
            retReg .= call copy [arg retReg]
            tmpReg .= call copy [arg tmpReg]
            call copyNestedValues []
            when (((heapEnd `sub` heapNext) `sub` requestedSize) `lt_u` (heapSize `div_u` i32c 2)) $ do
                -- if less than half heap left after GC double heap size
                heapEnd .= heapEnd `add` heapSize
        slide <- fun () $ do
            n <- param i32
            source <- local i32
            dist <- local i32
            end <- local i32
            dist .= stackBase
            end .= stackTop `add` (n `mul` i32c 4)
            for (source .= stackTop) (source `lt_u` end) (inc 4 source) $ do
                store dist (load i32 source 0 2) 0 2
                inc 4 dist
        reserve <- fun () $ do
            num <- param i32
            i <- local i32
            newStackTop <- local i32
            newStackTop .= stackTop `add` (num `mul` i32c 4)
            if' () (stackEnd `lt_u` newStackTop)
                (unreachable)
                (for (i .= stackTop) (i `lt_u` newStackTop) (inc 4 i) $ do
                    store i (i32c 0) 0 2
                )
        let packString :: (Producer size, OutType size ~ Proxy I32, Producer len, OutType len ~ Proxy I32)
                => size
                -> len
                -> GenFun (Proxy I32)
            packString size len = do
                tmpReg .= call alloc [arg size]
                store8 tmpReg (i32c $ fromEnum String) 0 0
                store tmpReg len 8 2
                ret tmpReg
        let packInt :: (Producer a, OutType a ~ Proxy I32) => a -> GenFun (Proxy I32)
            packInt val = (val `shl` i32c 1) `add` i32c 1
        strConcat <- fun i32 $ do
            a <- param i32
            b <- param i32
            aSize <- local i32
            bSize <- local i32
            addr <- local i32
            len <- local i32
            aSize .= load i32 a 4 2
            bSize .= load i32 b 4 2
            len .= load i32 a 8 2 `add` load i32 b 8 2
            addr .= packString (aSize `add` bSize `sub` i32c 12) len
            call memcpy [arg (addr `add` i32c 12), arg (a `add` i32c 12), arg (aSize `sub` i32c 12)]
            call memcpy [arg (addr `add` aSize), arg (b `add` i32c 12), arg (bSize `sub` i32c 12)]
            ret addr
        readChar <- fun i32 $ do
            addr <- param i32
            byte <- local i32
            res <- local i32
            byte .= load8_u i32 addr 0 0
            if' i32 (eqz $ byte `and` i32c 0x80)
                (packInt byte)
                (if' i32 ((byte `and` i32c 0xE0) `eq` i32c 0xC0)
                    (packInt
                        $ ((byte `and` i32c 0x1F) `shl` i32c 6)
                        `or` (load8_u i32 addr 1 0 `and` i32c 0x3F)
                    )
                    (if' i32 ((byte `and` i32c 0xF0) `eq` i32c 0xE0)
                        (packInt
                            $ ((byte `and` i32c 0x0F) `shl` i32c 12)
                            `or` ((load8_u i32 addr 1 0 `and` i32c 0x3F) `shl` i32c 6)
                            `or` (load8_u i32 addr 2 0 `and` i32c 0x3F)
                        )
                        (packInt
                            $ ((byte `and` i32c 0x07) `shl` i32c 18)
                            `or` ((load8_u i32 addr 1 0 `and` i32c 0x3F) `shl` i32c 12)
                            `or` ((load8_u i32 addr 2 0 `and` i32c 0x3F) `shl` i32c 6)
                            `or` (load8_u i32 addr 3 0 `and` i32c 0x3F)
                        )
                    )
                )
        strOffset <- fun i32 $ do
            addr <- param i32
            idx <- param i32
            while (idx `ne` i32c 0) $ do
                when ((load8_u i32 addr 0 0 `and` i32c 0xC0) `ne` i32c 0x80) $ dec 1 idx
                inc 1 addr
            while ((load8_u i32 addr 0 0 `and` i32c 0xC0) `eq` i32c 0x80) $ inc 1 addr
            ret addr
        strIndex <- fun i32 $ do
            addr <- param i32
            idx <- param i32
            call readChar [call strOffset [arg $ addr `add` i32c 12, arg idx]]
        strSubstr <- fun i32 $ do
            addr <- param i32
            offset <- param i32
            length <- param i32
            start <- local i32
            end <- local i32
            size <- local i32
            start .= call strOffset [arg $ addr `add` i32c 12, arg offset]
            end .= call strOffset [arg start, arg length]
            size .= end `sub` start
            addr .= packString (size `add` i32c 12) length
            call memcpy [arg (addr `add` i32c 12), arg start, arg size]
            ret addr
        strEq <- fun i32 $ do
            a <- param i32
            b <- param i32
            size <- local i32
            curA <- local i32
            curB <- local i32
            end <- local i32
            size .= load i32 a 4 2
            if' i32 (a `eq` b)
                (i32c 1)
                (if' i32 (size `ne` load i32 b 4 2)
                    (i32c 0)
                    (do
                        curA .= a `add` i32c 12
                        curB .= b `add` i32c 12
                        end .= a `add` size
                        while (curA `lt_u` end) $ do
                            when (load8_u i32 curA 0 0 `ne` load8_u i32 curB 0 0)
                                (finish $ i32c 0)
                            inc 1 curA
                            inc 1 curB
                        i32c 1
                    )
                )
        strLt <- fun i32 $ do
            a <- param i32
            b <- param i32
            i <- local i32
            j <- local i32
            end <- local i32
            i .= load i32 a 4 2
            j .= load i32 b 4 2
            end .= a `add` (if' i32 (i `lt_u` j) (ret i) (ret j))
            for (i .= a `add` i32c 12 >> j .= b `add` i32c 12) (i `lt_u` end) (inc 1 i >> inc 1 j) $ do
                when (load8_u i32 i 0 0 `lt_u` load8_u i32 j 0 0) $ finish $ i32c 1
                when (load8_u i32 i 0 0 `gt_u` load8_u i32 j 0 0) $ finish $ i32c 0
            load i32 a 4 2 `lt_u` load i32 b 4 2
        charWidth <- fun i32 $ do
            code <- param i32
            if' i32 (code `lt_u` i32c 0x80)
                (i32c 1)
                (if' i32 ((code `ge_u` i32c 0x80) `and` (code `lt_u` i32c 0x800))
                    (i32c 2)
                    (if' i32 ((code `ge_u` i32c 0x800) `and` (code `lt_u` i32c 0x8000))
                        (i32c 3)
                        (i32c 4)
                    )
                )
        storeChar <- fun () $ do
            addr <- param i32
            code <- param i32
            if' () (code `lt_u` i32c 0x80)
                (store8 addr code 0 0)
                (if' () ((code `ge_u` i32c 0x80) `and` (code `lt_u` i32c 0x800))
                    (do
                        store8 addr ((code `shr_u` i32c 6) `or` i32c 0xC0) 0 0
                        store8 addr ((code `and` i32c 0x3F) `or` i32c 0x80) 1 0
                    )
                    (if' () ((code `ge_u` i32c 0x800) `and` (code `lt_u` i32c 0x8000))
                        (do
                            store8 addr ((code `shr_u` i32c 12) `or` i32c 0xE0) 0 0
                            store8 addr (((code `shr_u` i32c 6) `and` i32c 0x3F) `or` i32c 0x80) 1 0
                            store8 addr ((code `and` i32c 0x3F) `or` i32c 0x80) 2 0
                        )
                        (do
                            store8 addr ((code `shr_u` i32c 18) `or` i32c 0xF0) 0 0
                            store8 addr (((code `shr_u` i32c 12) `and` i32c 0x3F) `or` i32c 0x80) 1 0
                            store8 addr (((code `shr_u` i32c 6) `and` i32c 0x3F) `or` i32c 0x80) 2 0
                            store8 addr ((code `and` i32c 0x3F) `or` i32c 0x80) 3 0
                        )
                    )
                )
        strCons <- fun i32 $ do
            char <- param i32
            tail <- param i32
            res <- local i32
            width <- local i32
            size <- local i32
            len <- local i32
            width .= call charWidth [arg char]
            size .= load i32 tail 4 2
            len .= load i32 tail 8 2 `add` i32c 1
            res .= packString (size `add` width) len
            call storeChar [arg $ res `add` i32c 12, arg char]
            call memcpy [res `add` i32c 12 `add` width, tail `add` i32c 12, size `sub` i32c 12]
            ret res
        strRev <- fun i32 $ do
            addr <- param i32
            len <- local i32
            res <- local i32
            width <- local i32
            next <- local i32
            len .= load i32 addr 8 2
            res .= packString (load i32 addr 4 2) len
            store8 res (load i32 addr 1 2) 1 0
            next .= res `add` load i32 addr 4 2
            addr .= addr `add` i32c 12
            while (len `ne` i32c 0) $ do
                width .= call strOffset [arg addr, arg $ i32c 1] `sub` addr
                next .= next `sub` width
                call memcpy [arg next, arg addr, arg width]
                addr .= addr `add` width
                dec 1 len
            ret res
        intStr <- fun i32 $ do
            -- intAddr <- param i32
            val <- param i32
            len <- local i32
            res <- local i32
            i <- local i32
            let zeroCode = i32c 48
            let minusCode = i32c 45
            when (eqz val) $ do
                res .= packString (i32c 13) (i32c 1)
                store8 res zeroCode 12 0
                finish res
            len .= if' i32 (val `lt_s` i32c 0) (i32c 1) (i32c 0)
            for (i .= val) (i `ne` i32c 0) (i .= i `div_s` i32c 10) $ inc 1 len
            res .= packString (i32c 12 `add` len) len
            when (val `lt_s` i32c 0) $ do
                store8 res minusCode 12 0
                val .= val `mul` i32c (-1)
            for (i .= res `add` len) (val `ne` i32c 0) (dec 1 i) $ do
                store8 i (zeroCode `add` (val `rem_s` i32c 10)) 11 0
                val .= val `div_s` i32c 10
            ret res
        int64Str <- fun i32 $ do
            -- intAddr <- param i32
            val <- param i64
            len <- local i32
            res <- local i32
            i <- local i64
            addr <- local i32
            let zeroCode = i64c 48
            let minusCode = i64c 45
            when (eqz val) $ do
                res .= packString (i32c 13) (i32c 1)
                store8 res zeroCode 12 0
                finish res
            len .= if' i32 (val `lt_s` i64c 0) (i32c 1) (i32c 0)
            for (i .= val) (i `ne` i64c 0) (i .= i `div_s` i64c 10) $ inc 1 len
            res .= packString (i32c 12 `add` len) len
            when (val `lt_s` i64c 0) $ do
                store8 res minusCode 12 0
                val .= val `mul` i64c (-1)
            for (addr .= res `add` len) (val `ne` i64c 0) (dec 1 addr) $ do
                store8 addr (zeroCode `add` (val `rem_s` i64c 10)) 11 0
                val .= val `div_s` i64c 10
            ret res
        strInt <- fun i32 $ do
            strAddr <- param i32
            len <- local i32
            char <- local i32
            next <- local i32
            val <- local i32
            len .= load i32 strAddr 8 2
            when (len `le_s` i32c 0) $ finish $ packInt (i32c 0)
            let (zero, nine, plus, minus) = (i32c 48, i32c 57, i32c 43, i32c 45)
            char .= load8_u i32 strAddr 12 0
            let isSign ch = (ch `eq` minus) `or` (ch `eq` plus)
            val .= i32c 0
            for (next .= if' i32 (isSign char) (i32c 1) (i32c 0)) (next `lt_u` len) (inc 1 next) $ do
                char .= load8_u i32 (strAddr `add` next) 12 0
                when ((char `lt_u` zero) `or` (char `gt_u` nine)) $ finish $ packInt $ i32c 0
                val .= (val `mul` i32c 10) `add` (char `sub` zero)
            let sign = if' i32 (load8_u i32 strAddr 12 0 `eq` minus) (i32c (-1)) (i32c 1)
            packInt (sign `mul` val)
        strInt64 <- fun i64 $ do
            strAddr <- param i32
            len <- local i32
            char <- local i64
            next <- local i32
            val <- local i64
            len .= load i32 strAddr 8 2
            when (len `le_s` i32c 0) $ finish $ i64c 0
            let (zero, nine, plus, minus) = (i64c 48, i64c 57, i64c 43, i64c 45)
            char .= load8_u i64 strAddr 12 0
            let isSign ch = (ch `eq` minus) `or` (ch `eq` plus)
            val .= i64c 0
            for (next .= if' i32 (isSign char) (i32c 1) (i32c 0)) (next `lt_u` len) (inc 1 next) $ do
                char .= load8_u i64 (strAddr `add` next) 12 0
                when ((char `lt_u` zero) `or` (char `gt_u` nine)) $ finish $ i64c 0
                val .= (val `mul` i64c 10) `add` (char `sub` zero)
            let sign = if' i64 (load8_u i64 strAddr 12 0 `eq` minus) (i64c (-1)) (i64c 1)
            sign `mul` val
        symbols <- Map.fromList <$> mapM (\(name, _) -> declare () [I32] >>= (\fn -> return (name, fn))) defs
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
                strLtFn = strLt,
                strIndexFn = strIndex,
                strConcatFn = strConcat,
                strConsFn = strCons,
                strSubstrFn = strSubstr,
                strRevFn = strRev,
                strWriteFn = strWrite,
                strReadFn = strRead,
                strIntFn = strInt,
                strInt64Fn = strInt64,
                intStrFn = intStr,
                int64StrFn = int64Str,
                strDoubleFn = strDouble,
                doubleStrFn = doubleStr,
                readCharFn = readChar,
                printValFn = printVal,
                expFn,
                logFn,
                sinFn,
                cosFn,
                tanFn,
                asinFn,
                acosFn,
                atanFn,
                atan2Fn,
                systemInfoFn,
                symbols
            }
        let (funcs, st) = runWasmGen emptyState bindings $ mapM mkFunc defs
        let GS { constSectionEnd, constSection } = st
        sequence_ funcs
        case Map.lookup (MN 0 "runMain") symbols of
            Just idx -> export "main" idx >> return ()
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
    strCache :: Map.Map String Word32,
    intCache :: Map.Map Int Word32,
    bigCache :: Map.Map Integer Word32,
    doubleCache :: Map.Map Double Word32
}

emptyState :: GenState
emptyState = GS 0 mempty mempty mempty mempty mempty

data GlobalBindings = GB {
    stackBaseIdx :: Glob I32,
    stackTopIdx :: Glob I32,
    stackStartIdx :: Glob I32,
    stackEndIdx :: Glob I32,
    returnValueIdx :: Glob I32,
    tmpIdx :: Glob I32,
    symbols :: Map.Map Name (Fn ()),
    raiseErrorFn :: Fn (),
    slideFn :: Fn (),
    reserveFn :: Fn (),
    allocFn :: Fn (Proxy I32),
    strEqFn :: Fn (Proxy I32),
    strLtFn :: Fn (Proxy I32),
    strIndexFn :: Fn (Proxy I32),
    strConcatFn :: Fn (Proxy I32),
    strConsFn :: Fn (Proxy I32),
    strSubstrFn :: Fn (Proxy I32),
    strRevFn :: Fn (Proxy I32),
    strWriteFn :: Fn (Proxy I32),
    strReadFn :: Fn (Proxy I32),
    strIntFn :: Fn (Proxy I32),
    strInt64Fn :: Fn (Proxy I64),
    strDoubleFn :: Fn (Proxy I32),
    doubleStrFn :: Fn (Proxy I32),
    readCharFn :: Fn (Proxy I32),
    intStrFn :: Fn (Proxy I32),
    int64StrFn :: Fn (Proxy I32),
    expFn :: Fn (Proxy F64),
    logFn :: Fn (Proxy F64),
    sinFn :: Fn (Proxy F64),
    cosFn :: Fn (Proxy F64),
    tanFn :: Fn (Proxy F64),
    asinFn :: Fn (Proxy F64),
    acosFn :: Fn (Proxy F64),
    atanFn :: Fn (Proxy F64),
    atan2Fn :: Fn (Proxy F64),
    printValFn :: Fn (),
    systemInfoFn :: Fn (Proxy I32)
}

type WasmGen = StateT GenState (Reader GlobalBindings)

runWasmGen :: GenState -> GlobalBindings -> WasmGen a -> (a, GenState)
runWasmGen st bindings = flip runReader bindings . flip runStateT st

mkFunc :: (Name, [BC]) -> WasmGen (GenMod (Fn ()))
mkFunc (name, byteCode) = do
    body <- mapM bcToInstr byteCode
    Just fn <- Map.lookup name <$> asks symbols
    return $ implement fn $ do
        oldBase <- param i32
        myOldBase <- local i32
        if any (hasTailCallOf name) byteCode
        then do
            loop () $ do
                lbl <- label
                sequence_ $ map ($ BCCtx { oldBase, myOldBase, selfName = name, tailCallLoop = Just lbl }) body
        else sequence_ $ map ($ BCCtx { oldBase, myOldBase, selfName = name, tailCallLoop = Nothing }) body

data BCCtx = BCCtx {
    oldBase :: Loc I32,
    myOldBase :: Loc I32,
    selfName :: Name,
    tailCallLoop :: Maybe (Label ())
}

hasTailCallOf :: Name -> BC -> Bool
hasTailCallOf name (CASE _ _ branches defaultBranch) =
    let tailCallInBranches = any (any (hasTailCallOf name) . snd) branches in
    let tailCallInDefault = any (hasTailCallOf name) $ fromMaybe [] defaultBranch in
    tailCallInBranches || tailCallInDefault
hasTailCallOf name (CONSTCASE _ branches defaultBranch) =
    let tailCallInBranches = any (any (hasTailCallOf name) . snd) branches in
    let tailCallInDefault = any (hasTailCallOf name) $ fromMaybe [] defaultBranch in
    tailCallInBranches || tailCallInDefault
hasTailCallOf name (TAILCALL callee) = name == callee
hasTailCallOf _ _ = False

bcToInstr :: BC -> WasmGen (BCCtx -> GenFun ())
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
    return $ \BCCtx { myOldBase } -> call fnIdx [arg myOldBase]
bcToInstr (TAILCALL n) = do
    Just fnIdx <- Map.lookup n <$> asks symbols
    return $ \BCCtx { oldBase, selfName, tailCallLoop } ->
        if selfName == n
        then let Just lbl = tailCallLoop in br lbl
        else call fnIdx [arg oldBase]
bcToInstr (SLIDE n)
    | n == 0 = return $ const $ return ()
    | n <= 4 = genSlide n
    | otherwise = do
        slide <- asks slideFn
        return $ const $ call slide [i32c n]
bcToInstr REBASE = do
    stackBase <- asks stackBaseIdx
    return $ \BCCtx { oldBase } -> stackBase .= oldBase
bcToInstr (RESERVE n)
    | n == 0 = return $ const $ return ()
    | n <= 4 = genReserve n
    | otherwise = do
        reserve <- asks reserveFn
        return $ const $ call reserve [i32c n]
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
    return $ \BCCtx { myOldBase } -> myOldBase .= stackBase
bcToInstr (OP loc op args) = const <$> makeOp loc op args
bcToInstr (NULL reg) = const <$> setRegVal reg (i32c 0)
bcToInstr (ERROR str) = do
    raiseError <- asks raiseErrorFn
    strAddr <- makeConst (Str str)
    return $ const $ call raiseError [strAddr]
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

genCase :: Bool -> Reg -> [(Int, [BC])] -> Maybe [BC] -> WasmGen (BCCtx -> GenFun ())
genCase safe reg branches defaultBranch = do
    addr <- getRegVal reg
    branchesBody <- mapM toFunGen branches
    defBody <- case defaultBranch of
        Just code -> mapM bcToInstr code
        Nothing -> return $ [const $ return ()]
    return $ \ctx -> do
        let defCode = sequence_ $ map ($ ctx) defBody
        let branchesCode = map (\(tag, code) -> (tag, code ctx)) branchesBody
        let conCheck = load8_u i32 addr 0 0 `eq` i32c (fromEnum Con)
        let conTag = load i32 addr 8 2
        let conGuard body
                | safe = body
                | otherwise = if' () conCheck body defCode
        let genSwitch [] = defCode
            genSwitch ((tag, code):rest) = if' () (conTag `eq` i32c tag) code (genSwitch rest)
        conGuard $ genSwitch branchesCode
    where
        toFunGen :: (Int, [BC]) -> WasmGen (Int, (BCCtx -> GenFun ()))
        toFunGen (tag, code) = do
            instrs <- mapM bcToInstr code
            return $ (tag, (\ctx -> sequence_ $ map ($ ctx) instrs))

genProject :: Reg -> Int -> Int -> WasmGen (BCCtx -> GenFun ())
genProject reg offset arity = do
    stackBase <- asks stackBaseIdx
    addr <- getRegVal reg
    return $ const $ forM_ [0..arity-1] $ \i -> do
        store stackBase (load i32 addr (12 + i * 4) 2) ((offset + i) * 4) 2

genConstCase :: Reg -> [(Const, [BC])] -> Maybe [BC] -> WasmGen (BCCtx -> GenFun ())
genConstCase reg branches defaultBranch = do
    addr <- getRegVal reg
    branchesBody <- mapM (toFunGen addr) branches
    defBody <- case defaultBranch of
        Just code -> mapM bcToInstr code
        Nothing -> return $ [const $ return ()]
    return $ \ctx -> do
        let defCode = sequence_ $ map ($ ctx) defBody
        let branchesCode = map (\(cond, code) -> (cond, code ctx)) branchesBody
        let genSwitch [] = defCode
            genSwitch ((cond, code):rest) = if' () cond code (genSwitch rest)
        genSwitch branchesCode
    where
        toFunGen :: GenFun (Proxy I32) -> (Const, [BC]) -> WasmGen (GenFun (Proxy I32), (BCCtx -> GenFun ()))
        toFunGen addr (c, code) = do
            instrs <- mapM bcToInstr code
            constCode <- makeConst c
            cond <- mkConstChecker c addr constCode
            return $ (cond, (\ctx -> sequence_ $ map ($ ctx) instrs))

        mkConstChecker :: Const -> GenFun (Proxy I32) -> GenFun (Proxy I32) -> WasmGen (GenFun (Proxy I32))
        mkConstChecker c val pat | intConst c = return $ eq val pat
        mkConstChecker c val pat | int32Const c = return $ eq (load i32 val 8 2) (load i32 pat 8 2)
        mkConstChecker c val pat | int64Const c = return $ eq (load i64 val 8 2) (load i64 pat 8 2)
        mkConstChecker c val pat | bigIntConst c = return $ eq (load i64 val 8 2) (load i64 pat 8 2)
        mkConstChecker c val pat | strConst c = do
            strEq <- asks strEqFn
            return $ call strEq [val, pat]
        mkConstChecker _ _valAddr _constAddr = return $ i32c 0

        intConst (I _) = True
        intConst (Ch _) = True
        intConst (B8 _) = True
        intConst (B16 _) = True
        intConst _ = False

        int32Const (B32 _) = True
        int32Const _ = False

        int64Const (B64 _) = True
        int64Const _ = False
    
        bigIntConst (BI _) = True
        bigIntConst _ = False
    
        strConst (Str _) = True
        strConst _ = False

genSlide :: Int -> WasmGen (BCCtx -> GenFun ())
genSlide n = do
    stackBase <- asks stackBaseIdx
    stackTop <- asks stackTopIdx
    return $ const $ forM_ [0..n-1] $ \i -> do
        store stackBase (load i32 stackTop (i * 4) 2) (i * 4) 2

genReserve :: Int -> WasmGen (BCCtx -> GenFun ())
genReserve n = do
    stackTop <- asks stackTopIdx
    stackEnd <- asks stackEndIdx
    return $ const $ do
        if' () (stackEnd `lt_u` (stackTop `add` i32c (n * 4)))
            unreachable
            (forM_ [0..n-1] $ \i -> store stackTop (i32c 0) (i * 4) 2)

{-
Left to implement:
    | LExternal Name
-}
makeOp :: Reg -> PrimFn -> [Reg] -> WasmGen (GenFun ())
makeOp loc (LPlus (ATInt (ITFixed IT8))) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ add l r) args
makeOp loc (LMinus (ATInt (ITFixed IT8))) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ sub l r) args
makeOp loc (LTimes (ATInt (ITFixed IT8))) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ mul l r) args
makeOp loc (LUDiv (ITFixed IT8)) args =
    i32BinOp loc div_u args
makeOp loc (LSDiv (ATInt (ITFixed IT8))) args =
    i32BinOp loc (onInt8 $ \a b -> (a `div_s` b) `and` i32c 0xFF) args
makeOp loc (LURem (ITFixed IT8)) args =
    i32BinOp loc rem_u args
makeOp loc (LSRem (ATInt (ITFixed IT8))) args =
    i32BinOp loc (onInt8 $ \a b -> (a `rem_s` b) `and` i32c 0xFF) args
makeOp loc (LAnd (ITFixed IT8)) args =
    i32BinOp loc and args
makeOp loc (LOr (ITFixed IT8)) args =
    i32BinOp loc or args
makeOp loc (LXOr (ITFixed IT8)) args =
    i32BinOp loc xor args
makeOp loc (LSHL (ITFixed IT8)) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ shl l r) args
makeOp loc (LLSHR (ITFixed IT8)) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ shr_u l r) args
makeOp loc (LASHR (ITFixed IT8)) args =
    i32BinOp loc (\l r -> and (i32c 0xFF) $ shr_s l r) args
makeOp loc (LCompl (ITFixed IT8)) [x] = do
    val <- getRegVal x
    ctor <- genInt
    setRegVal loc $ ctor $ load i32 val 8 2 `xor` i32c 0xFF
makeOp loc (LEq (ATInt (ITFixed IT8))) args =
    i32BinOp loc eq args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LSLt (ATInt (ITFixed IT8))) args =
    i32BinOp loc (onInt8 lt_s) args
makeOp loc (LSLe (ATInt (ITFixed IT8))) args =
    i32BinOp loc (onInt8 le_s) args
makeOp loc (LSGt (ATInt (ITFixed IT8))) args =
    i32BinOp loc (onInt8 gt_s) args
makeOp loc (LSGe (ATInt (ITFixed IT8))) args =
    i32BinOp loc (onInt8 ge_s) args
makeOp loc (LLt (ITFixed IT8)) args =
    i32BinOp loc lt_u args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LLe (ITFixed IT8)) args =
    i32BinOp loc le_u args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LGt (ITFixed IT8)) args =
    i32BinOp loc gt_u args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LGe (ITFixed IT8)) args =
    i32BinOp loc ge_u args -- do not need clipping for relation ops, coz result 0 or 1

makeOp loc (LPlus (ATInt (ITFixed IT16))) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ add l r) args
makeOp loc (LMinus (ATInt (ITFixed IT16))) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ sub l r) args
makeOp loc (LTimes (ATInt (ITFixed IT16))) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ mul l r) args
makeOp loc (LUDiv (ITFixed IT16)) args =
    i32BinOp loc div_u args
makeOp loc (LSDiv (ATInt (ITFixed IT16))) args =
    i32BinOp loc (onInt16 $ \a b -> (a `div_s` b) `and` i32c 0xFFFF) args
makeOp loc (LURem (ITFixed IT16)) args =
    i32BinOp loc rem_u args
makeOp loc (LSRem (ATInt (ITFixed IT16))) args =
    i32BinOp loc (onInt16 $ \a b -> (a `rem_s` b) `and` i32c 0xFFFF) args
makeOp loc (LAnd (ITFixed IT16)) args =
    i32BinOp loc and args
makeOp loc (LOr (ITFixed IT16)) args =
    i32BinOp loc or args
makeOp loc (LXOr (ITFixed IT16)) args =
    i32BinOp loc xor args
makeOp loc (LSHL (ITFixed IT16)) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ shl l r) args
makeOp loc (LLSHR (ITFixed IT16)) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ shr_u l r) args
makeOp loc (LASHR (ITFixed IT16)) args =
    i32BinOp loc (\l r -> and (i32c 0xFFFF) $ shr_s l r) args
makeOp loc (LCompl (ITFixed IT16)) [x] = do
    val <- getRegVal x
    ctor <- genInt
    setRegVal loc $ ctor $ load i32 val 8 2 `xor` i32c 0xFFFF
makeOp loc (LEq (ATInt (ITFixed IT16))) args =
    i32BinOp loc eq args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LSLt (ATInt (ITFixed IT16))) args =
    i32BinOp loc (onInt16 lt_s) args
makeOp loc (LSLe (ATInt (ITFixed IT16))) args =
    i32BinOp loc (onInt16 le_s) args
makeOp loc (LSGt (ATInt (ITFixed IT16))) args =
    i32BinOp loc (onInt16 gt_s) args
makeOp loc (LSGe (ATInt (ITFixed IT16))) args =
    i32BinOp loc (onInt16 ge_s) args
makeOp loc (LLt (ITFixed IT16)) args =
    i32BinOp loc lt_u args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LLe (ITFixed IT16)) args =
    i32BinOp loc le_u args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LGt (ITFixed IT16)) args =
    i32BinOp loc gt_u args -- do not need clipping for relation ops, coz result 0 or 1
makeOp loc (LGe (ITFixed IT16)) args =
    i32BinOp loc ge_u args -- do not need clipping for relation ops, coz result 0 or 1

makeOp loc (LPlus (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc add args
makeOp loc (LMinus (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc sub args
makeOp loc (LTimes (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc mul args
makeOp loc (LUDiv (ITFixed IT32)) args =
    i32BitBinOp loc div_u args
makeOp loc (LSDiv (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc div_s args
makeOp loc (LURem (ITFixed IT32)) args =
    i32BitBinOp loc rem_u args
makeOp loc (LSRem (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc rem_s args
makeOp loc (LAnd (ITFixed IT32)) args =
    i32BitBinOp loc and args
makeOp loc (LOr (ITFixed IT32)) args =
    i32BitBinOp loc or args
makeOp loc (LXOr (ITFixed IT32)) args =
    i32BitBinOp loc xor args
makeOp loc (LSHL (ITFixed IT32)) args =
    i32BitBinOp loc shl args
makeOp loc (LLSHR (ITFixed IT32)) args =
    i32BitBinOp loc shr_u args
makeOp loc (LASHR (ITFixed IT32)) args =
    i32BitBinOp loc shr_s args
makeOp loc (LCompl (ITFixed IT32)) [x] = do
    val <- getRegVal x
    ctor <- genBit32
    setRegVal loc $ ctor $ load i32 val 8 2 `xor` i32c (-1)
makeOp loc (LEq (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc eq args
makeOp loc (LSLt (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc lt_s args
makeOp loc (LSLe (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc le_s args
makeOp loc (LSGt (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc gt_s args
makeOp loc (LSGe (ATInt (ITFixed IT32))) args =
    i32BitBinOp loc ge_s args
makeOp loc (LLt (ITFixed IT32)) args =
    i32BitBinOp loc lt_u args
makeOp loc (LLe (ITFixed IT32)) args =
    i32BitBinOp loc le_u args
makeOp loc (LGt (ITFixed IT32)) args =
    i32BitBinOp loc gt_u args
makeOp loc (LGe (ITFixed IT32)) args =
    i32BitBinOp loc ge_u args

makeOp loc (LPlus (ATInt (ITFixed IT64))) args =
    i64BinOp loc add args
makeOp loc (LMinus (ATInt (ITFixed IT64))) args =
    i64BinOp loc sub args
makeOp loc (LTimes (ATInt (ITFixed IT64))) args =
    i64BinOp loc mul args
makeOp loc (LUDiv (ITFixed IT64)) args =
    i64BinOp loc div_u args
makeOp loc (LSDiv (ATInt (ITFixed IT64))) args =
    i64BinOp loc div_s args
makeOp loc (LURem (ITFixed IT64)) args =
    i64BinOp loc rem_u args
makeOp loc (LSRem (ATInt (ITFixed IT64))) args =
    i64BinOp loc rem_s args
makeOp loc (LAnd (ITFixed IT64)) args =
    i64BinOp loc and args
makeOp loc (LOr (ITFixed IT64)) args =
    i64BinOp loc or args
makeOp loc (LXOr (ITFixed IT64)) args =
    i64BinOp loc xor args
makeOp loc (LSHL (ITFixed IT64)) args =
    i64BinOp loc shl args
makeOp loc (LLSHR (ITFixed IT64)) args =
    i64BinOp loc shr_u args
makeOp loc (LASHR (ITFixed IT64)) args =
    i64BinOp loc shr_s args
makeOp loc (LCompl (ITFixed IT64)) [x] = do
    val <- getRegVal x
    ctor <- genBit64
    setRegVal loc $ ctor $ load i64 val 8 2 `xor` i64c (-1)
makeOp loc (LEq (ATInt (ITFixed IT64))) args =
    i64BinOp loc ((extend_u .) . eq) args
makeOp loc (LSLt (ATInt (ITFixed IT64))) args =
    i64BinOp loc ((extend_u .) . lt_s) args
makeOp loc (LSLe (ATInt (ITFixed IT64))) args =
    i64BinOp loc ((extend_u .) . le_s) args
makeOp loc (LSGt (ATInt (ITFixed IT64))) args =
    i64BinOp loc ((extend_u .) . gt_s) args
makeOp loc (LSGe (ATInt (ITFixed IT64))) args =
    i64BinOp loc ((extend_u .) . ge_s) args
makeOp loc (LLt (ITFixed IT64)) args =
    i64BinOp loc ((extend_u .) . lt_u) args
makeOp loc (LLe (ITFixed IT64)) args =
    i64BinOp loc ((extend_u .) . le_u) args
makeOp loc (LGt (ITFixed IT64)) args =
    i64BinOp loc ((extend_u .) . gt_u) args
makeOp loc (LGe (ITFixed IT64)) args =
    i64BinOp loc ((extend_u .) . ge_u) args

makeOp loc (LPlus (ATInt ITBig)) args =
    bigBinOp loc add args
makeOp loc (LMinus (ATInt ITBig)) args =
    bigBinOp loc sub args
makeOp loc (LTimes (ATInt ITBig)) args =
    bigBinOp loc mul args
makeOp loc (LUDiv ITBig) args =
    bigBinOp loc div_u args
makeOp loc (LSDiv (ATInt ITBig)) args =
    bigBinOp loc div_s args
makeOp loc (LURem ITBig) args =
    bigBinOp loc rem_u args
makeOp loc (LSRem (ATInt ITBig)) args =
    bigBinOp loc rem_s args
makeOp loc (LAnd ITBig) args =
    bigBinOp loc and args
makeOp loc (LOr ITBig) args =
    bigBinOp loc or args
makeOp loc (LXOr ITBig) args =
    bigBinOp loc xor args
makeOp loc (LSHL ITBig) args =
    bigBinOp loc shl args
makeOp loc (LLSHR ITBig) args =
    bigBinOp loc shr_u args
makeOp loc (LASHR ITBig) args =
    bigBinOp loc shr_s args
makeOp loc (LCompl ITBig) [x] = do
    val <- getRegVal x
    ctor <- genBit64
    setRegVal loc $ ctor $ load i64 val 8 2 `xor` i64c (-1)
makeOp loc (LEq (ATInt ITBig)) args =
    bigBinOp loc ((extend_u .) . eq) args
makeOp loc (LSLt (ATInt ITBig)) args =
    bigBinOp loc ((extend_u .) . lt_s) args
makeOp loc (LSLe (ATInt ITBig)) args =
    bigBinOp loc ((extend_u .) . le_s) args
makeOp loc (LSGt (ATInt ITBig)) args =
    bigBinOp loc ((extend_u .) . gt_s) args
makeOp loc (LSGe (ATInt ITBig)) args =
    bigBinOp loc ((extend_u .) . ge_s) args
makeOp loc (LLt ITBig) args =
    bigBinOp loc ((extend_u .) . lt_u) args
makeOp loc (LLe ITBig) args =
    bigBinOp loc ((extend_u .) . le_u) args
makeOp loc (LGt ITBig) args =
    bigBinOp loc ((extend_u .) . gt_u) args
makeOp loc (LGe ITBig) args =
    bigBinOp loc ((extend_u .) . ge_u) args

makeOp loc (LPlus (ATInt ITNative)) args =
    i32BinOp loc add args
makeOp loc (LMinus (ATInt ITNative)) args =
    i32BinOp loc sub args
makeOp loc (LTimes (ATInt ITNative)) args =
    i32BinOp loc mul args
makeOp loc (LUDiv ITNative) args =
    i32BinOp loc div_u args
makeOp loc (LSDiv (ATInt ITNative)) args =
    i32BinOp loc div_s args
makeOp loc (LURem ITNative) args =
    i32BinOp loc rem_u args
makeOp loc (LSRem (ATInt ITNative)) args =
    i32BinOp loc rem_s args
makeOp loc (LAnd ITNative) args =
    i32BinOp loc and args
makeOp loc (LOr ITNative) args =
    i32BinOp loc or args
makeOp loc (LXOr ITNative) args =
    i32BinOp loc xor args
makeOp loc (LSHL ITNative) args =
    i32BinOp loc shl args
makeOp loc (LLSHR ITNative) args =
    i32BinOp loc shr_u args
makeOp loc (LASHR ITNative) args =
    i32BinOp loc shr_s args
makeOp loc (LCompl ITNative) [x] = do
    val <- getRegVal x
    ctor <- genInt
    setRegVal loc $ ctor $ unpackInt val `xor` i32c (-1)
makeOp loc (LEq (ATInt ITNative)) args =
    i32BinOp loc eq args
makeOp loc (LSLt (ATInt ITNative)) args =
    i32BinOp loc lt_s args
makeOp loc (LSLe (ATInt ITNative)) args =
    i32BinOp loc le_s args
makeOp loc (LSGt (ATInt ITNative)) args =
    i32BinOp loc gt_s args
makeOp loc (LSGe (ATInt ITNative)) args =
    i32BinOp loc ge_s args
makeOp loc (LLt ITNative) args =
    i32BinOp loc lt_u args
makeOp loc (LLe ITNative) args =
    i32BinOp loc le_u args
makeOp loc (LGt ITNative) args =
    i32BinOp loc gt_u args
makeOp loc (LGe ITNative) args =
    i32BinOp loc ge_u args

makeOp loc (LIntFloat ITNative) [reg] = do
    val <- getRegVal reg
    ctor <- genFloat
    setRegVal loc $ ctor $ convert_s f64 $ unpackInt val
makeOp loc (LFloatInt ITNative) [reg] = do
    val <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ trunc_s i32 $ load f64 val 8 2
makeOp loc (LIntFloat ITBig) [reg] = do
    val <- getRegVal reg
    ctor <- genFloat
    setRegVal loc $ ctor $ convert_s f64 $ load i64 val 8 2
makeOp loc (LFloatInt ITBig) [reg] = do
    val <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ trunc_s i64 $ load f64 val 8 2
makeOp loc (LSExt ITNative ITBig) [reg] = do
    val <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ extend_s $ unpackInt val
makeOp loc (LTrunc ITBig ITNative) [reg] = do
    val <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ wrap $ load i64 val 8 2
makeOp loc (LStrInt ITBig) [reg] = do
    str <- getRegVal reg
    strInt64 <- asks strInt64Fn
    ctor <- genBigInt
    setRegVal loc $ ctor $ call strInt64 [str]
makeOp loc (LIntStr ITBig) [reg] = do
    val <- getRegVal reg
    int64Str <- asks int64StrFn
    setRegVal loc $ call int64Str [load i32 val 8 2]
makeOp loc (LIntStr ITNative) [reg] = do
    addr <- getRegVal reg
    intStr <- asks intStrFn
    setRegVal loc $ call intStr [unpackInt addr]
makeOp loc (LStrInt ITNative) [reg] = do
    val <- getRegVal reg
    strInt <- asks strIntFn
    setRegVal loc $ call strInt [val]
makeOp loc (LIntStr (ITFixed IT8)) [reg] = do
    addr <- getRegVal reg
    intStr <- asks intStrFn
    setRegVal loc $ do
        let val = unpackInt addr
        call intStr [if' i32 (val `ge_u` i32c 128) (i32c 0xFFFFFF00 `or` val) val]
makeOp loc (LIntStr (ITFixed IT16)) [reg] = do
    addr <- getRegVal reg
    intStr <- asks intStrFn
    setRegVal loc $ do
        let val = unpackInt addr
        call intStr [if' i32 (val `ge_u` i32c (2^15)) (i32c 0xFFFF0000 `or` val) val]
makeOp loc (LIntStr (ITFixed IT32)) [reg] = do
    val <- getRegVal reg
    intStr <- asks intStrFn
    setRegVal loc $ call intStr [load i32 val 8 2]
makeOp loc (LIntStr (ITFixed IT64)) [reg] = do
    val <- getRegVal reg
    int64Str <- asks int64StrFn
    setRegVal loc $ call int64Str [load i32 val 8 2]
makeOp loc LFloatStr [reg] = do
    val <- getRegVal reg
    doubleStr <- asks doubleStrFn
    setRegVal loc $ call doubleStr [val]
makeOp loc LStrFloat [reg] = do
    val <- getRegVal reg
    strDouble <- asks strDoubleFn
    setRegVal loc $ call strDouble [val]
makeOp loc (LChInt ITNative) args = getRegVal (last args) >>= setRegVal loc
makeOp loc (LChInt ITChar) args = makeOp loc (LChInt ITNative) args
makeOp loc (LIntCh ITNative) args = getRegVal (last args) >>= setRegVal loc
makeOp loc (LIntCh ITChar) args = makeOp loc (LIntCh ITNative) args

makeOp loc (LPlus (ATInt ITChar)) [l, r] = makeOp loc (LPlus (ATInt ITNative)) [l, r]
makeOp loc (LMinus (ATInt ITChar)) [l, r] = makeOp loc (LMinus (ATInt ITNative)) [l, r]
makeOp loc (LTimes (ATInt ITChar)) [l, r] = makeOp loc (LTimes (ATInt ITNative)) [l, r]
makeOp loc (LUDiv ITChar) [l, r] = makeOp loc (LUDiv ITNative) [l, r]
makeOp loc (LSDiv (ATInt ITChar)) [l, r] = makeOp loc (LSDiv (ATInt ITNative)) [l, r]
makeOp loc (LURem ITChar) [l, r] = makeOp loc (LURem ITNative) [l, r]
makeOp loc (LSRem (ATInt ITChar)) [l, r] = makeOp loc (LSRem (ATInt ITNative)) [l, r]
makeOp loc (LAnd ITChar) [l, r] = makeOp loc (LAnd ITNative) [l, r]
makeOp loc (LOr ITChar) [l, r] = makeOp loc (LOr ITNative) [l, r]
makeOp loc (LXOr ITChar) [l, r] = makeOp loc (LXOr ITNative) [l, r]
makeOp loc (LSHL ITChar) [l, r] = makeOp loc (LSHL ITNative) [l, r]
makeOp loc (LLSHR ITChar) [l, r] = makeOp loc (LLSHR ITNative) [l, r]
makeOp loc (LASHR ITChar) [l, r] = makeOp loc (LASHR ITNative) [l, r]
makeOp loc (LCompl ITChar) [x] = makeOp loc (LCompl ITNative) [x]
makeOp loc (LEq (ATInt ITChar)) [l, r] = makeOp loc (LEq (ATInt ITNative)) [l, r]
makeOp loc (LSLt (ATInt ITChar)) [l, r] = makeOp loc (LSLt (ATInt ITNative)) [l, r]
makeOp loc (LSLe (ATInt ITChar)) [l, r] = makeOp loc (LSLe (ATInt ITNative)) [l, r]
makeOp loc (LSGt (ATInt ITChar)) [l, r] = makeOp loc (LSGt (ATInt ITNative)) [l, r]
makeOp loc (LSGe (ATInt ITChar)) [l, r] = makeOp loc (LSGe (ATInt ITNative)) [l, r]
makeOp loc (LLt ITChar) [l, r] = makeOp loc (LLt ITNative) [l, r]
makeOp loc (LLe ITChar) [l, r] = makeOp loc (LLe ITNative) [l, r]
makeOp loc (LGt ITChar) [l, r] = makeOp loc (LGt ITNative) [l, r]
makeOp loc (LGe ITChar) [l, r] = makeOp loc (LGe ITNative) [l, r]

makeOp loc (LPlus ATFloat) args = f64BinOp loc add args
makeOp loc (LMinus ATFloat) args = f64BinOp loc sub args
makeOp loc (LTimes ATFloat) args = f64BinOp loc mul args
makeOp loc (LSDiv ATFloat) args = f64BinOp loc div_f args
makeOp loc (LEq ATFloat) args = f64RelOp loc eq args
makeOp loc (LSLt ATFloat) args = f64RelOp loc lt_f args
makeOp loc (LSLe ATFloat) args = f64RelOp loc le_f args
makeOp loc (LSGt ATFloat) args = f64RelOp loc gt_f args
makeOp loc (LSGe ATFloat) args = f64RelOp loc ge_f args
makeOp loc LFExp args = do
    op <- asks expFn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFLog args = do
    op <- asks logFn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFSin args = do
    op <- asks sinFn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFCos args = do
    op <- asks cosFn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFTan args = do
    op <- asks tanFn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFASin args = do
    op <- asks asinFn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFACos args = do
    op <- asks acosFn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFATan args = do
    op <- asks atanFn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFATan2 args = do
    op <- asks atan2Fn
    f64UnOp loc (\x -> call op [x]) args
makeOp loc LFSqrt args = f64UnOp loc sqrt_f args
makeOp loc LFFloor args = f64UnOp loc floor_f args
makeOp loc LFCeil args = f64UnOp loc ceil_f args
makeOp loc LFNegate args = f64UnOp loc (\x -> x `mul` f64c (-1)) args

makeOp loc (LSExt (ITFixed IT8) ITBig) [reg] = do
    addr <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        extend_s $ if' i32 (val `ge_u` i32c 128) (i32c 0xFFFFFF00 `or` val) val
makeOp loc (LSExt (ITFixed IT16) ITBig) [reg] = do
    addr <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        extend_s $ if' i32 (val `ge_u` i32c (2^15)) (i32c 0xFFFF0000 `or` val) val
makeOp loc (LSExt (ITFixed IT32) ITBig) [reg] = do
    val <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ extend_s $ load i32 val 8 2
makeOp loc (LSExt (ITFixed IT64) ITBig) [reg] = do
    val <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ load i64 val 8 2
makeOp loc (LSExt ITNative (ITFixed IT8)) [reg] = do
    val <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ i32c 0xFF `and` unpackInt val
makeOp loc (LSExt ITNative (ITFixed IT16)) [reg] = do
    val <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ i32c 0xFFFF `and` unpackInt val
makeOp loc (LSExt ITNative (ITFixed IT32)) [reg] = do
    val <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ unpackInt val
makeOp loc (LSExt ITNative (ITFixed IT64)) [reg] = do
    val <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ extend_s $ unpackInt val
makeOp loc (LSExt ITChar (ITFixed to)) args = makeOp loc (LSExt ITNative (ITFixed to)) args
makeOp loc (LSExt (ITFixed IT8) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        if' i32 (val `ge_u` i32c 128) (i32c 0xFFFFFF00 `or` val) val
makeOp loc (LSExt (ITFixed IT16) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        if' i32 (val `ge_u` i32c (2^15)) (i32c 0xFFFF0000 `or` val) val
makeOp loc (LSExt (ITFixed IT32) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ load i32 addr 8 2
makeOp loc (LSExt (ITFixed IT64) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ wrap $ load i64 addr 8 2
makeOp loc (LSExt (ITFixed from) ITChar) args = makeOp loc (LSExt (ITFixed from) ITNative) args
makeOp loc (LSExt (ITFixed IT8) (ITFixed IT8)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LSExt (ITFixed IT8) (ITFixed IT16)) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        if' i32 (val `ge_u` i32c 128) (i32c 0xFF00 `or` val) val
makeOp loc (LSExt (ITFixed IT8) (ITFixed IT32)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        if' i32 (val `ge_u` i32c 128) (i32c 0xFFFFFF00 `or` val) val
makeOp loc (LSExt (ITFixed IT8) (ITFixed IT64)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        extend_s $ if' i32 (val `ge_u` i32c 128) (i32c 0xFFFFFF00 `or` val) val
makeOp loc (LSExt (ITFixed IT16) (ITFixed IT16)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LSExt (ITFixed IT16) (ITFixed IT32)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        if' i32 (val `ge_u` i32c (2^15)) (i32c 0xFFFF0000 `or` val) val
makeOp loc (LSExt (ITFixed IT16) (ITFixed IT64)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        extend_s $ if' i32 (val `ge_u` i32c (2^15)) (i32c 0xFFFF0000 `or` val) val
makeOp loc (LSExt (ITFixed IT32) (ITFixed IT32)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LSExt (ITFixed IT32) (ITFixed IT64)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ extend_s $ load i32 addr 8 2
makeOp loc (LSExt (ITFixed IT64) (ITFixed IT64)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LZExt ITNative (ITFixed IT8)) [reg] = do
    val <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ i32c 0xFF `and` unpackInt val
makeOp loc (LZExt ITNative (ITFixed IT16)) [reg] = do
    val <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ i32c 0xFFFF `and` unpackInt val
makeOp loc (LZExt ITNative (ITFixed IT32)) [reg] = do
    val <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ unpackInt val
makeOp loc (LZExt ITNative (ITFixed IT64)) [reg] = do
    val <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ extend_u $ unpackInt val
makeOp loc (LZExt ITChar (ITFixed to)) args = makeOp loc (LZExt ITNative (ITFixed to)) args
makeOp loc (LZExt (ITFixed IT8) ITNative) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LZExt (ITFixed IT16) ITNative) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LZExt (ITFixed IT32) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ load i32 addr 8 2
makeOp loc (LZExt (ITFixed IT64) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ wrap $ load i64 addr 8 2
makeOp loc (LZExt (ITFixed from) ITChar) args = makeOp loc (LZExt (ITFixed from) ITNative) args
makeOp loc (LZExt (ITFixed IT8) ITBig) [reg] = do
    addr <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ extend_u $ load i32 addr 8 2
makeOp loc (LZExt (ITFixed IT16) ITBig) [reg] = do
    addr <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ extend_u $ unpackInt addr
makeOp loc (LZExt (ITFixed IT32) ITBig) [reg] = do
    addr <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ extend_u $ load i32 addr 8 2
makeOp loc (LZExt (ITFixed IT64) ITBig) [reg] = do
    addr <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ load i64 addr 8 2
makeOp loc (LZExt ITNative ITBig) [reg] = do
    addr <- getRegVal reg
    ctor <- genBigInt
    setRegVal loc $ ctor $ extend_u $ unpackInt addr
makeOp loc (LZExt (ITFixed IT8) (ITFixed IT8)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LZExt (ITFixed IT8) (ITFixed IT16)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LZExt (ITFixed IT8) (ITFixed IT32)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ unpackInt addr
makeOp loc (LZExt (ITFixed IT8) (ITFixed IT64)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ extend_u $ unpackInt addr
makeOp loc (LZExt (ITFixed IT16) (ITFixed IT16)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LZExt (ITFixed IT16) (ITFixed IT32)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ unpackInt addr
makeOp loc (LZExt (ITFixed IT16) (ITFixed IT64)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ extend_u $ unpackInt addr
makeOp loc (LZExt (ITFixed IT32) (ITFixed IT32)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LZExt (ITFixed IT32) (ITFixed IT64)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ extend_u $ load i32 addr 8 2
makeOp loc (LZExt (ITFixed IT64) (ITFixed IT64)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LTrunc ITNative (ITFixed IT8)) [reg] = do
    val <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ i32c 0xFF `and` unpackInt val
makeOp loc (LTrunc ITNative (ITFixed IT16)) [reg] = do
    val <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ i32c 0xFFFF `and` unpackInt val
makeOp loc (LTrunc ITNative (ITFixed IT32)) [reg] = do
    val <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ unpackInt val
makeOp loc (LTrunc ITNative (ITFixed IT64)) [reg] = do
    val <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ extend_s $ unpackInt val
makeOp loc (LTrunc ITChar (ITFixed to)) args = makeOp loc (LTrunc ITNative (ITFixed to)) args
makeOp loc (LTrunc (ITFixed IT8) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        if' i32 (val `ge_u` i32c 128) (i32c 0xFFFFFF00 `or` val) val
makeOp loc (LTrunc (ITFixed IT16) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ do
        let val = unpackInt addr
        if' i32 (val `ge_u` i32c (2^15)) (i32c 0xFFFF0000 `or` val) val
makeOp loc (LTrunc (ITFixed IT32) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ load i32 addr 8 2
makeOp loc (LTrunc (ITFixed IT64) ITNative) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ wrap $ load i64 addr 8 2
makeOp loc (LTrunc (ITFixed from) ITChar) args = makeOp loc (LTrunc (ITFixed from) ITNative) args
makeOp loc (LTrunc (ITFixed IT8) (ITFixed IT8)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LTrunc (ITFixed IT16) (ITFixed IT8)) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ and (i32c 0xFF) $ unpackInt addr
makeOp loc (LTrunc (ITFixed IT32) (ITFixed IT8)) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ and (i32c 0xFF) $ load i32 addr 8 2
makeOp loc (LTrunc (ITFixed IT64) (ITFixed IT8)) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ and (i32c 0xFF) $ wrap $ load i64 addr 8 2
makeOp loc (LTrunc (ITFixed IT16) (ITFixed IT16)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LTrunc (ITFixed IT32) (ITFixed IT16)) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ and (i32c 0xFFFF) $ load i32 addr 8 2
makeOp loc (LTrunc (ITFixed IT64) (ITFixed IT16)) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ and (i32c 0xFFFF) $ wrap $ load i64 addr 8 2
makeOp loc (LTrunc (ITFixed IT32) (ITFixed IT32)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LTrunc (ITFixed IT64) (ITFixed IT32)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ wrap $ load i64 addr 8 2
makeOp loc (LTrunc (ITFixed IT64) (ITFixed IT64)) [reg] = getRegVal reg >>= setRegVal loc
makeOp loc (LTrunc ITBig (ITFixed IT8)) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ and (i32c 0xFF) $ wrap $ load i64 addr 8 2
makeOp loc (LTrunc ITBig (ITFixed IT16)) [reg] = do
    addr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ and (i32c 0xFFFF) $ wrap $ load i64 addr 8 2
makeOp loc (LTrunc ITBig (ITFixed IT32)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit32
    setRegVal loc $ ctor $ wrap $ load i64 addr 8 2
makeOp loc (LTrunc ITBig (ITFixed IT64)) [reg] = do
    addr <- getRegVal reg
    ctor <- genBit64
    setRegVal loc $ ctor $ load i64 addr 8 2

makeOp loc LStrConcat [l, r] = do
    a <- getRegVal l
    b <- getRegVal r
    strConcat <- asks strConcatFn
    setRegVal loc $ call strConcat [a, b]
makeOp loc LStrLt [l, r] = do
    a <- getRegVal l
    b <- getRegVal r
    strLt <- asks strLtFn
    intCtor <- genInt
    setRegVal loc $ intCtor $ call strLt [a, b]
makeOp loc LStrEq [l, r] = do
    a <- getRegVal l
    b <- getRegVal r
    strEq <- asks strEqFn
    intCtor <- genInt
    setRegVal loc $ intCtor $ call strEq [a, b]
makeOp loc LStrLen [reg] = do
    strAddr <- getRegVal reg
    ctor <- genInt
    setRegVal loc $ ctor $ load i32 strAddr 8 2
makeOp loc LStrHead [reg] = do
    str <- getRegVal reg
    readChar <- asks readCharFn
    setRegVal loc $ call readChar [str `add` i32c 12]
makeOp loc LStrTail [reg] = do
    str <- getRegVal reg
    strSubstr <- asks strSubstrFn
    setRegVal loc $ call strSubstr [str, i32c 1, load i32 str 8 2 `sub` i32c 1]
makeOp loc LStrCons [charReg, tailReg] = do
    char <- getRegVal charReg
    tail <- getRegVal tailReg
    strCons <- asks strConsFn
    setRegVal loc $ call strCons [unpackInt char, tail]
makeOp loc LStrIndex [strReg, idxReg] = do
    str <- getRegVal strReg
    idx <- getRegVal idxReg
    strIndex <- asks strIndexFn
    setRegVal loc $ call strIndex [str, unpackInt idx]
makeOp loc LStrRev [strReg] = do
    str <- getRegVal strReg
    strRev <- asks strRevFn
    setRegVal loc $ call strRev [str]
makeOp loc LStrSubstr [offsetReg, lengthReg, strReg] = do
    str <- getRegVal strReg
    off <- getRegVal offsetReg
    len <- getRegVal lengthReg
    strSubstr <- asks strSubstrFn
    setRegVal loc $ call strSubstr [str, unpackInt off, unpackInt len]
makeOp loc LWriteStr [_, reg] = do
    str <- getRegVal reg
    strWrite <- asks strWriteFn
    setRegVal loc $ call strWrite [str]
makeOp loc LReadStr [_] = do
    strRead <- asks strReadFn
    setRegVal loc $ call strRead []

makeOp loc LSystemInfo [reg] = do
    val <- getRegVal reg
    systemInfo <- asks systemInfoFn
    setRegVal loc $ call systemInfo [arg val]
makeOp loc LCrash [reg] = do
    str <- getRegVal reg
    raiseError <- asks raiseErrorFn
    return $ do
        call raiseError [str]
        unreachable

makeOp _ LNoOp _ = return $ return ()

makeOp _ (LExternal _) _ = return $ return ()

makeOp _ op args = error $ "makeOp not implemented (" ++ show (op, args) ++ ")"

i32BinOp :: Reg
    -> (GenFun (Proxy I32) -> GenFun (Proxy I32) -> GenFun (Proxy I32))
    -> [Reg]
    -> WasmGen (GenFun ())
i32BinOp loc op [l, r] = do
    left <- getRegVal l
    right <- getRegVal r
    ctor <- genInt
    setRegVal loc $ ctor $ op (unpackInt left) (unpackInt right)

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

f64UnOp :: Reg
    -> (GenFun (Proxy F64) -> GenFun (Proxy F64))
    -> [Reg]
    -> WasmGen (GenFun ())
f64UnOp loc op [x] = do
    val <- getRegVal x
    ctor <- genFloat
    setRegVal loc $ ctor $ op (load f64 val 8 2)

f64RelOp :: Reg
    -> (GenFun (Proxy F64) -> GenFun (Proxy F64) -> GenFun (Proxy I32))
    -> [Reg]
    -> WasmGen (GenFun ())
f64RelOp loc op [l, r] = do
    left <- getRegVal l
    right <- getRegVal r
    ctor <- genInt
    setRegVal loc $ ctor $ op (load f64 left 8 2) (load f64 right 8 2)

onInt8 ::
    (GenFun (Proxy I32) -> GenFun (Proxy I32) -> GenFun (Proxy I32))
    -> GenFun (Proxy I32)
    -> GenFun (Proxy I32)
    -> GenFun (Proxy I32)
onInt8 op l r =
    let a = if' i32 (l `ge_u` i32c 128) (i32c 0xFFFFFF00 `or` l) (l) in
    let b = if' i32 (r `ge_u` i32c 128) (i32c 0xFFFFFF00 `or` r) (r) in
    a `op` b

onInt16 ::
    (GenFun (Proxy I32) -> GenFun (Proxy I32) -> GenFun (Proxy I32))
    -> GenFun (Proxy I32)
    -> GenFun (Proxy I32)
    -> GenFun (Proxy I32)
onInt16 op l r =
    let a = if' i32 (l `ge_u` i32c (2 ^ 15)) (i32c 0xFFFF0000 `or` l) (l) in
    let b = if' i32 (r `ge_u` i32c (2 ^ 15)) (i32c 0xFFFF0000 `or` r) (r) in
    a `op` b

asAddr :: WasmGen Word32 -> WasmGen (GenFun (Proxy I32))
asAddr expr = do
    addr <- expr
    return $ i32c addr

makeConst :: Const -> WasmGen (GenFun (Proxy I32))
makeConst (I i) = makeIntConst i
makeConst (BI i) = do
    cache <- gets bigCache
    case Map.lookup i cache of
        Just addr -> return $ i32c addr
        Nothing -> do
            addr <- addToConstSection (mkBigInt i)
            modify $ \st -> st { bigCache = Map.insert i addr cache }
            return $ i32c addr
makeConst (Fl f) = do
    cache <- gets doubleCache
    case Map.lookup f cache of
        Just addr -> return $ i32c addr
        Nothing -> do
            addr <- addToConstSection (mkFloat f)
            modify $ \st -> st { doubleCache = Map.insert f addr cache }
            return $ i32c addr
makeConst (Ch c) = makeIntConst $ Char.ord c
makeConst (Str s) = do
    cache <- gets strCache
    case Map.lookup s cache of
        Just addr -> return $ i32c addr
        Nothing -> do
            addr <- addToConstSection (mkStr s)
            modify $ \st -> st { strCache = Map.insert s addr cache }
            return $ i32c addr
makeConst (B8 w) = makeIntConst w
makeConst (B16 w) = makeIntConst w
makeConst (B32 w) = asAddr $ addToConstSection (mkBit32 w)
makeConst (B64 w) = asAddr $ addToConstSection (mkBit64 w)
makeConst c
    | isTypeConst c = makeIntConst 42424242
    | otherwise = error $ "mkConst of (" ++ show c ++ ") not implemented"

makeIntConst :: (Integral i) => i -> WasmGen (GenFun (Proxy I32))
makeIntConst val = return $ do
    appendExpr [I32Const $ ((asWord32 $ fromIntegral val) `shift` 1) + 1]
    return Proxy

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
    | BigInt
    | Float
    | String
    | StrOffset
    | Bit32
    | Bit64
    | Fwd
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

genInt :: (Producer val, OutType val ~ Proxy I32) => WasmGen (val -> GenFun (Proxy I32))
genInt = return $ \val -> (val `shl` i32c 1) `add` i32c 1

unpackInt :: GenFun (Proxy I32) -> GenFun (Proxy I32)
unpackInt val = val `shr_s` i32c 1

data FloatVal = FV { hdr :: ValHeader, val :: Double } deriving (Show, Eq)

mkFloat :: Double -> FloatVal
mkFloat val = FV { hdr = mkHdr Float 16, val }

genFloat :: (Producer val, OutType val ~ Proxy F64) => WasmGen (val -> GenFun (Proxy I32))
genFloat = do
    alloc <- asks allocFn
    tmp <- asks tmpIdx
    return $ \val -> do
        tmp .= call alloc [arg $ i32c (8 + 8)]
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
        Serialize.putLazyByteString val
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
        tmp .= call alloc [arg $ i32c (8 + 4)]
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
        tmp .= call alloc [arg $ i32c (8 + 8)]
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
        tmp .= call alloc [arg $ i32c (8 + 8)]
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
        tmp .= call alloc [arg $ i32c (8 + 4 + 4 * fromIntegral arity)]
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