module Main where

import Prelude
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when, forM_ )

import MettaVenus.Abs 
import MettaVenus.Lex   ( Token, mkPosToken )
import MettaVenus.Par   ( pThDecl, myLexer )
import MettaVenus.Print ( Print, printTree )
import MettaVenus.Skel  ()

--------------------------------------------------------------------------------
-- Transformation functions to traverse the Grammar AST.
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

--------------------------------------------------------------------------------
-- Checking BindTerminal properties

-- | Traverse a Grammar and check every production for correct BindTerminal usage.
checkGrammar :: Grammar -> Either String ()
checkGrammar (MkGrammar defs) = mapM_ checkDef defs

-- | Only production definitions (Rule or Internal) contain a right-hand side.
checkDef :: Def -> Either String ()
checkDef (Rule label _ items)     = checkProduction ("production " ++ show label) items
checkDef (Internal label _ items) = checkProduction ("internal production " ++ show label) items
checkDef _                        = Right ()

-- | For a given production, compute the number of non-string items and,
-- while traversing the items in order (ignoring Terminal items),
-- check every BindTerminal.
checkProduction :: String -> [Item] -> Either String ()
checkProduction prodName items =
  let total = fromIntegral (length (filter (not . isTerminal) items)) :: Integer
      -- go: traverse items with a counter (curr) for the current non-string item index.
      go :: [Item] -> Integer -> Either String ()
      go [] _ = Right ()
      go (x:xs) curr =
        case x of
          Terminal _ -> go xs curr
          BindTerminal (Ints indices) ->
            if null indices
              then Left (prodName ++ ": BindTerminal at non-string position " ++ show curr ++ " has an empty IntList.")
              else do
                forM_ indices $ \j -> 
                  if j < 0 || j >= total
                    then Left (prodName ++ ": BindTerminal at non-string position " ++ show curr ++ " contains index " ++ show j ++ " which is out of range [0," ++ show total ++ ").")
                    else if j == curr
                      then Left (prodName ++ ": BindTerminal at non-string position " ++ show curr ++ " contains its own index " ++ show j ++ ".")
                      else Right ()
                go xs (curr + 1)
          _ -> go xs (curr + 1)
  in go items 0

-- | Determines whether an item is a Terminal (i.e. a quoted string).
isTerminal :: Item -> Bool
isTerminal (Terminal _) = True
isTerminal _            = False

--------------------------------------------------------------------------------
-- Main driver and parsing

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
      let grammar = case thDecl of
                      GSLTDecl _ _ (Generators g) _ _ -> g
                      _ -> error "Unexpected ThDecl structure."
      -- Check BindTerminal properties before proceeding.
      case checkGrammar grammar of
        Left errMsg -> do
          putStrLn $ "\nError: " ++ errMsg
          exitFailure
        Right () -> return ()
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
