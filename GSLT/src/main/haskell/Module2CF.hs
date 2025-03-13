module Main where

import Prelude
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when, forM_ )
import Data.List          ( nub, intercalate )

import MettaVenus.Abs 
import MettaVenus.Lex   ( Token, mkPosToken )
import MettaVenus.Par   ( pModule, myLexer )  -- use pModule for parsing a Module
import MettaVenus.Print ( Print, printTree )
import MettaVenus.Skel  ()

--------------------------------------------------------------------------------
-- Base Transformation Functions (as in step 1)

-- | transformItem returns a tuple: ([Def], Item)
--   (This version is used as the base for BindTerminal processing.)
baseTransformItem :: Item -> ([Def], Item)
baseTransformItem (BindTerminal m ints) =
  ( [ newDef m ]
  , NTerminal (IdCat (Ident "Ident"))
  )
  where
    newDef mIdent = Rule (LabNoP (Id (Ident "Id")))
                         (IdCat mIdent)
                         [NTerminal (IdCat (Ident "Ident"))]
baseTransformItem other = ([], other)

baseTransformItems :: [Item] -> ([Def], [Item])
baseTransformItems [] = ([], [])
baseTransformItems (x:xs) =
  let (extras1, x')      = baseTransformItem x
      (extrasRest, xs')  = baseTransformItems xs
  in (extras1 ++ extrasRest, x' : xs')

baseTransformDef :: Def -> ([Def], Def)
baseTransformDef (Rule l cat items) =
  let (extras, items') = baseTransformItems items
  in (extras, Rule l cat items')
baseTransformDef (Internal l cat items) =
  let (extras, items') = baseTransformItems items
  in (extras, Internal l cat items')
baseTransformDef d = ([], d)

baseTransformGrammar :: Grammar -> Grammar
baseTransformGrammar (MkGrammar defs) =
  let (extrasList, defs') = unzip (map baseTransformDef defs)
      extras = nub (concat extrasList)
  in MkGrammar (defs' ++ extras)

mangleCat :: String -> Cat -> Cat
mangleCat th cat =
  case flattenImported cat of
    [] -> cat
    xs -> IdCat (Ident (th ++ "_" ++ intercalate "_" xs))
  where
    flattenImported :: Cat -> [String]
    flattenImported (ImportedCat (Ident s) rest) = s : flattenImported rest
    flattenImported (IdCat (Ident s))            = [s]
    flattenImported (ListCat c)                    = flattenImported c
    flattenImported _                              = []

-- A version of transformItem that also updates NTerminal items using mangleCat.
transformItemWithTheory :: String -> Item -> ([Def], Item)
transformItemWithTheory th (NTerminal cat) =
  ([], NTerminal (mangleCat th cat))
transformItemWithTheory th (BindTerminal m ints) =
  -- We keep the BindTerminal transformation as in baseTransformItem.
  ( [ newDef m ]
  , NTerminal (IdCat (Ident "Ident"))
  )
  where
    newDef mIdent = Rule (LabNoP (Id (Ident "Id")))
                         (IdCat mIdent)
                         [NTerminal (IdCat (Ident "Ident"))]
transformItemWithTheory _ other = ([], other)

transformItemsWithTheory :: String -> [Item] -> ([Def], [Item])
transformItemsWithTheory _ [] = ([], [])
transformItemsWithTheory th (x:xs) =
  let (extras1, x')      = transformItemWithTheory th x
      (extrasRest, xs')  = transformItemsWithTheory th xs
  in (extras1 ++ extrasRest, x' : xs')

transformDefWithTheory :: String -> Def -> ([Def], Def)
transformDefWithTheory th (Rule l cat items) =
  let (extras, items') = transformItemsWithTheory th items
      newCat = mangleCat th cat
  in (extras, Rule l newCat items')
transformDefWithTheory th (Internal l cat items) =
  let (extras, items') = transformItemsWithTheory th items
      newCat = mangleCat th cat
  in (extras, Internal l newCat items')
transformDefWithTheory _ d = ([], d)

transformGrammarWithTheory :: String -> Grammar -> Grammar
transformGrammarWithTheory th (MkGrammar defs) =
  let (extrasList, defs') = unzip (map (transformDefWithTheory th) defs)
      extras = nub (concat extrasList)
  in MkGrammar (defs' ++ extras)

--------------------------------------------------------------------------------
-- Module Traversal and Transformation

-- | Transform a module by applying our transformation (with theory-specific mangling)
--   to every GSLTDeclAll production.
transformModule :: Module -> Module
transformModule (ModuleImpl name progs) =
  ModuleImpl name (map transformProg progs)

-- | Process a Prog: if it is a declaration, transform it.
transformProg :: Prog -> Prog
transformProg (ProgDecl d) = ProgDecl (transformDecl d)
transformProg other        = other

-- | Transform a declaration: if it is a GSLTDeclAll, update its grammar.
transformDecl :: Decl -> Decl
transformDecl (GSLTDeclAll thName varDecls exports (Generators g) eqns rewrites) =
  let thStr = case thName of
                NameVar (Ident s) -> s
                _                 -> "Wildcard"
  in GSLTDeclAll thName varDecls exports (Generators (transformGrammarWithTheory thStr g)) eqns rewrites
transformDecl d = d

--------------------------------------------------------------------------------
-- Module Checking (unchanged from step 1)

checkGrammar :: Grammar -> Either String ()
checkGrammar (MkGrammar defs) = mapM_ checkDef defs

checkDef :: Def -> Either String ()
checkDef (Rule label _ items)     = checkProduction ("production " ++ show label) items
checkDef (Internal label _ items) = checkProduction ("internal production " ++ show label) items
checkDef _                        = Right ()

checkProduction :: String -> [Item] -> Either String ()
checkProduction prodName items =
  let total = fromIntegral (length (filter (not . isTerminal) items)) :: Integer
      go :: [Item] -> Integer -> Either String ()
      go [] _ = Right ()
      go (x:xs) curr =
        case x of
          Terminal _ -> go xs curr
          BindTerminal _ (Ints indices) ->
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

isTerminal :: Item -> Bool
isTerminal (Terminal _) = True
isTerminal _            = False

-- | Check all GSLTDeclAll productions in the module.
checkModule :: Module -> Either String ()
checkModule (ModuleImpl _ progs) = mapM_ checkProg progs

checkProg :: Prog -> Either String ()
checkProg (ProgDecl d) = checkDecl d
checkProg _            = Right ()

checkDecl :: Decl -> Either String ()
checkDecl (GSLTDeclAll _ _ _ (Generators g) _ _) = checkGrammar g
checkDecl _                                      = Right ()

--------------------------------------------------------------------------------
-- Main Driver and Parsing

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

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
      -- Check every GSLTDeclAll's grammar
      case checkModule mod of
        Left errMsg -> do
          putStrLn $ "\nError: " ++ errMsg
          exitFailure
        Right () -> return ()
      -- Transform each grammar (with name mangling) and update the module
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
