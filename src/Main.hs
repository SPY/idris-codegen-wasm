module Main where

import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.Main
import Idris.Options

import IRTS.Compiler
import IRTS.CodegenWasm

import System.Environment
import System.Exit

import Paths_idris_codegen_wasm

data Opts = Opts {
    inputs :: [FilePath],
    output :: FilePath
}

showUsage = do
    putStrLn "Usage: idris-codegen-wasm <ibc-files> [-o <output-file>]"
    exitWith ExitSuccess

getOpts :: IO Opts
getOpts = do
    xs <- getArgs
    return $ process (Opts [] "a.wasm") xs
    where
        process opts ("-o":o:xs) = process (opts { output = o }) xs
        process opts (x:xs) = process (opts { inputs = x:inputs opts }) xs
        process opts [] = opts

cg_main :: Opts -> Idris ()
cg_main opts = do
    elabPrims
    loadInputs (inputs opts) Nothing
    mainProg <- elabMain
    ir <- compile (Via IBCFormat "wasm") (output opts) (Just mainProg)
    runIO $ codegenWasm ir

main :: IO ()
main = do
    opts <- getOpts
    if (null (inputs opts)) 
    then showUsage
    else runMain (cg_main opts)
