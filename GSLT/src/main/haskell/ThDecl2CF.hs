module Main where

import Prelude
  ( ($), (.)
  , Either(..)
  , Int, (>)
  , String, (++), concat, unlines
  , Show, show
  , IO, (>>), (>>=), map, mapM_, putStrLn, error
  , FilePath
  , getContents, readFile
  )
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )

import MettaVenus.Abs 
  ( ThDecl(..)
  , Prog(..)
  , Grammar(..)
  , Def(..)       
  , Item(..)      
  , Cat(..)       
  , Ident(..)     
  , FreeTheory(..)
  )

import MettaVenus.Lex   ( Token, mkPosToken )
import MettaVenus.Par   ( pThDecl, myLexer )
import MettaVenus.Print ( Print, printTree )
import MettaVenus.Skel  ()

-- | Transformation functions to traverse the Grammar AST.
-- Replace every BindTerminal with an NTerminal representing "Ident".
transformItem :: Item -> Item
transformItem (BindTerminal ints) = NTerminal (IdCat (Ident "Ident"))
transformItem other               = other

transformDef :: Def -> Def
transformDef (Rule l cat items)     = Rule l cat (map transformItem items)
transformDef (Internal l cat items) = Internal l cat (map transformItem items)
transformDef d                      = d

transformGrammar :: Grammar -> Grammar
transformGrammar (MkGrammar defs) = MkGrammar (map transformDef defs)

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: (Print ThDecl, Show ThDecl) => Verbosity -> ParseFun ThDecl -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: (Print ThDecl, Show ThDecl) => Verbosity -> ParseFun ThDecl -> String -> IO ()
run v p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse Failed...\n"
      putStrV v "Tokens:"
      mapM_ (putStrV v . showPosToken . mkPosToken) ts
      putStrLn err
      exitFailure
    Right thDecl -> do
      putStrLn "\nParse Successful!"
      -- Extract the Grammar subtree from the FreeTheory part of the theory.
      let grammar = case thDecl of
                      GSLTDecl _ _ (Generators g) _ _ -> g
                      _ -> error "Unexpected ThDecl structure."
      -- Transform the Grammar by replacing BindTerminal nodes.
      let transformedGrammar = transformGrammar grammar
      putStrLn "\nTransformed Grammar:"
      putStrLn (printTree transformedGrammar)
  where
    ts = myLexer s
    showPosToken ((l, c), t) = concat [ show l, ":", show c, "\t", show t ]

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely as a ThDecl."
    , "  (files)         Parse content of files verbosely as a ThDecl."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> getContents >>= run 2 pThDecl
    "-s":fs    -> mapM_ (runFile 0 pThDecl) fs
    fs         -> mapM_ (runFile 2 pThDecl) fs
