-- File: Main.hs
-- Updated to support recursive module resolution, pretty printing,
-- and printing the last instance (Inst) from the main module.

module Main where

import Prelude
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import System.IO          ( stderr, hPutStrLn )
import System.FilePath    ( takeDirectory, (</>) )
import System.Directory   ( canonicalizePath )
import Control.Monad      ( forM, forM_ )
import Data.IORef         ( IORef, newIORef, readIORef, modifyIORef )
import qualified Data.Set as Set

import MettaVenus.Abs
import MettaVenus.Lex   ( mkPosToken, Token )
import MettaVenus.Par   ( pModule, myLexer )
import MettaVenus.Print ( Print, printTree )
import MettaVenus.Skel  ()

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Main <module-file> [other-module-files...]"
    , "       If no file is provided, the module is read from standard input."
    , "       Imports are resolved relative to the module file's location,"
    , "       or the current directory if read from standard input."
    ]

-- Recursively load a module from a file.
-- Tracks visited canonical file paths to avoid reloading the same module.
loadModuleFile :: FilePath -> IORef (Set.Set FilePath) -> IO [Module]
loadModuleFile path visitedRef = do
  canonical <- canonicalizePath path
  visited <- readIORef visitedRef
  if Set.member canonical visited
    then return []  -- Already loaded; skip.
    else do
      modifyIORef visitedRef (Set.insert canonical)
      content <- readFile canonical
      case pModule (myLexer content) of
        Left err -> do
          hPutStrLn stderr $ "Parse error in " ++ canonical ++ ": " ++ err
          exitFailure
        Right mod ->
          -- Resolve all imports relative to the current module's directory.
          loadImports (takeDirectory canonical) mod visitedRef >>= \imports ->
            return (mod : imports)

-- For a given module and its base directory, recursively load all imported modules.
loadImports :: FilePath -> Module -> IORef (Set.Set FilePath) -> IO [Module]
loadImports baseDir mod visitedRef = do
  let imports = case mod of
                  ModuleImpl imps _ _ -> imps
  importedModulesLists <- forM imports $ \imp -> do
      let impPath = case imp of
                      ImportModule s       -> s
                      ImportModuleAs s _   -> s
                      ImportFromModule _ s -> s
      let fullPath = baseDir </> impPath
      loadModuleFile fullPath visitedRef
  return (concat importedModulesLists)

-- Loads a module from standard input.
-- Uses the current directory as the base for resolving imports.
loadModuleFromStdin :: IORef (Set.Set FilePath) -> IO [Module]
loadModuleFromStdin visitedRef = do
  content <- getContents
  case pModule (myLexer content) of
    Left err -> do
      hPutStrLn stderr $ "Parse error from standard input: " ++ err
      exitFailure
    Right mod ->
      loadImports "." mod visitedRef >>= \imports ->
         return (mod : imports)

-- Find the last Inst in the main module.  It searches through the module's Progs,
-- selecting those of the form ProgInst, and returns the last one, or InstEmpty if none.
findLastInst :: Module -> Inst
findLastInst (ModuleImpl _ _ progs) =
  case [inst | ProgInst inst <- progs] of
    [] -> InstEmpty
    xs -> last xs

-- Main entry point.
main :: IO ()
main = do
  args <- getArgs
  visitedRef <- newIORef Set.empty
  modules <- case args of
    ["--help"] -> usage >> return []
    []         -> loadModuleFromStdin visitedRef
    fs         -> do
                   modsLists <- forM fs $ \f -> loadModuleFile f visitedRef
                   return (concat modsLists)
  -- Print all loaded modules using the pretty printer.
  putStrLn "\nLoaded Modules:\n"
  forM_ modules $ \mod -> do
      putStrLn (printTree mod)
  -- Extract and print the last Inst from the main module (first loaded module).
  case modules of
    [] -> return ()
    (mainModule:_) -> do
         let lastInst = findLastInst mainModule
         putStrLn "\nLast Instance in Main Module:\n"
         putStrLn (printTree lastInst)
