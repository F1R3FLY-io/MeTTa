-- | Main module: entry point for the compiler.
-- This module handles command-line arguments, file input, parsing,
-- transformation, and error reporting.
module Main where

import Prelude
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )
import System.IO          ( readFile )

import MettaVenus.Abs
import MettaVenus.Lex   ( Token )
import MettaVenus.Par   ( pModule, myLexer )
import MettaVenus.Print ( Print, printTree )

import Transform ( transformModule )
import Check     ( checkModule )

--------------------------------------------------------------------------------
-- * Type Synonyms for Clarity
--------------------------------------------------------------------------------

-- | Parser error type.
type Err        = Either String

-- | Type for parser functions that consume a list of tokens.
type ParseFun a = [Token] -> Err a

-- | Verbosity level for printing messages.
type Verbosity  = Int

--------------------------------------------------------------------------------
-- * Running the Parser and Transformer
--------------------------------------------------------------------------------

-- | Reads a file, parses it, checks the module, applies transformation, and prints output.
runFile :: (Print Module, Show Module) => Verbosity -> ParseFun Module -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

-- | Parses the input string, checks the module for errors, transforms it, and prints results.
run :: (Print Module, Show Module) => Verbosity -> ParseFun Module -> String -> IO ()
run v p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse Failed...\n"
      putStrLn err
      exitFailure
    Right mod -> do
      putStrLn "\nParse Successful!"
      case checkModule mod of
        Left errMsg -> do
          putStrLn $ "\nError: " ++ errMsg
          exitFailure
        Right () -> return ()
      let transformedModule = transformModule mod
      putStrLn "\nTransformed Module:"
      putStrLn (printTree transformedModule)
  where
    ts = myLexer s

--------------------------------------------------------------------------------
-- * Usage Information and Main Entry Point
--------------------------------------------------------------------------------

-- | Prints usage instructions.
usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely as a Module."
    , "  (files)         Parse content of files verbosely as a Module."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]

-- | Main entry point.
-- It processes command-line arguments and dispatches to runFile or run.
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> getContents >>= run 2 pModule
    "-s":fs    -> mapM_ (runFile 0 pModule) fs
    fs         -> mapM_ (runFile 2 pModule) fs
