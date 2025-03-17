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

-- | A parser is a function from a list of tokens to either an error message or a parsed value.
type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

runFile :: (Print Module, Show Module) => Verbosity -> ParseFun Module -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

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

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely as a Module."
    , "  (files)         Parse content of files verbosely as a Module."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> getContents >>= run 2 pModule
    "-s":fs    -> mapM_ (runFile 0 pModule) fs
    fs         -> mapM_ (runFile 2 pModule) fs
