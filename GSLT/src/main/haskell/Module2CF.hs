module Main where

import Prelude
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when, forM_ )
import Data.List
import Data.Function      (on)

import MettaVenus.Abs 
import MettaVenus.Lex   ( Token, mkPosToken )
import MettaVenus.Par   ( pModule, myLexer )
import MettaVenus.Print ( Print, printTree )
import MettaVenus.Skel  ()

labelToString :: Label -> String
labelToString (LabNoP (Id (Ident s)))      = s
labelToString (LabP   (Id (Ident s)) _)    = s
labelToString (LabPF  (Id (Ident s)) _ _)  = s
labelToString (LabF   (Id (Ident s)) _)    = s

baseTransformItem :: String -> String -> Integer -> Item -> ([Def], Item)
baseTransformItem th ruleLabel slot (BindTerminal m ints) =
  ( [ newDef th ruleLabel slot m ]
  , NTerminal (IdCat (Ident "Ident"))
  )
  where
    newDef th ruleLabel slot mIdent =
      Rule (LabNoP (Id (Ident (ruleLabel ++ "_" ++ show slot ++ "_Id"))))
           (mangleCat th (IdCat mIdent))
           [NTerminal (IdCat (Ident "Ident"))]
baseTransformItem _ _ _ other = ([], other)

baseTransformItems :: String -> String -> [Item] -> ([Def], [Item])
baseTransformItems th ruleLabel items = go 0 items
  where
    go _ [] = ([], [])
    go curr (item:xs) =
      let (defs, newItem) = baseTransformItem th ruleLabel curr item
          nextSlot = if isTerminal item then curr else curr + 1
          (defsRest, newItems) = go nextSlot xs
      in (defs ++ defsRest, newItem : newItems)

baseTransformDef :: Def -> ([Def], Def)
baseTransformDef (Rule l cat items) =
  let ruleLabelStr         = labelToString l
      (extras, items')     = baseTransformItems "base" ruleLabelStr items
  in (extras, Rule l cat items')
baseTransformDef (Internal l cat items) =
  let ruleLabelStr         = labelToString l
      (extras, items')     = baseTransformItems "base" ruleLabelStr items
  in (extras, Internal l cat items')
baseTransformDef d = ([], d)

baseTransformGrammar :: Grammar -> Grammar
baseTransformGrammar (MkGrammar defs) =
  let (extrasList, defs') = unzip (map baseTransformDef defs)
      extras              = nub (concat extrasList)
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
    
prefixLabel :: String -> Label -> Label
prefixLabel th (LabNoP (Id (Ident s)))      = LabNoP (Id (Ident (th ++ "_" ++ s)))
prefixLabel th (LabP   (Id (Ident s)) prof)   = LabP   (Id (Ident (th ++ "_" ++ s))) prof
prefixLabel th (LabPF  (Id (Ident s)) l2 prof)  = LabPF  (Id (Ident (th ++ "_" ++ s))) l2 prof
prefixLabel th (LabF   (Id (Ident s)) l2)       = LabF   (Id (Ident (th ++ "_" ++ s))) l2
prefixLabel _  lab                              = lab

baseFromImported :: String -> String
baseFromImported s =
  case break (=='_') s of
    (base, "")   -> base
    (base, _rest) -> base

transformItemWithTheory :: String -> String -> Integer -> Item -> ([Def], Item)
transformItemWithTheory th ruleLabel slot (NTerminal cat) =
  ([], NTerminal (mangleCat th cat))
transformItemWithTheory th ruleLabel slot (BindTerminal m ints) =
  ( [ newDef th ruleLabel slot m ]
  , NTerminal (IdCat (Ident "Ident"))
  )
  where
    newDef th ruleLabel slot mIdent =
      Rule (LabNoP (Id (Ident (th ++ "_" ++ ruleLabel ++ "_" ++ show slot ++ "_Id"))))
           (mangleCat th (IdCat mIdent))
           [NTerminal (IdCat (Ident "Ident"))]
transformItemWithTheory _ _ _ other = ([], other)

transformItemsWithTheory :: String -> String -> [Item] -> ([Def], [Item])
transformItemsWithTheory th ruleLabel items = go 0 items
  where
    go _ [] = ([], [])
    go curr (item:xs) =
      let (defs, newItem) = transformItemWithTheory th ruleLabel curr item
          nextSlot = if isTerminal item then curr else curr + 1
          (defsRest, newItems) = go nextSlot xs
      in (defs ++ defsRest, newItem : newItems)
      
transformDefWithTheory :: String -> Def -> ([Def], Def)
transformDefWithTheory th (Rule l cat items) =
  let ruleLabelStr         = labelToString l
      newLabel             = prefixLabel th l
      (extras, items')     = transformItemsWithTheory th ruleLabelStr items
      newCat               = mangleCat th cat
  in (extras, Rule newLabel newCat items')
transformDefWithTheory th (Internal l cat items) =
  let ruleLabelStr         = labelToString l
      newLabel             = prefixLabel th l
      (extras, items')     = transformItemsWithTheory th ruleLabelStr items
      newCat               = mangleCat th cat
  in (extras, Internal newLabel newCat items')
transformDefWithTheory _ d = ([], d)

transformGrammarWithTheory :: String -> Grammar -> Grammar
transformGrammarWithTheory th (MkGrammar defs) =
  let (extrasList, defs') = unzip (map (transformDefWithTheory th) defs)
      extras              = nub (concat extrasList)
  in MkGrammar (defs' ++ extras)

buildMapping :: [VariableDecl] -> [(String,String)]
buildMapping [] = []
buildMapping (VarDecl (Ident v) name : rest) =
  case name of
    NameVar (Ident t) -> (v, t) : buildMapping rest
    _ -> buildMapping rest

transformExports :: String -> [(String,String)] -> Exports -> Exports
transformExports th mapping (Categories exps) =
  Categories (map (transformExport th mapping) exps)

transformExport :: String -> [(String,String)] -> Export -> Export
transformExport th mapping (SimpleExp ident) =
  SimpleExp (mangleLocalIdent' th ident)
transformExport th mapping (Extends (Ident localCat) imp imps) =
  let (imp', impStr) = transformImport th mapping imp
      imps' = transformImports th mapping imps
  in Extends (Ident (mangleLocalIdent th localCat)) imp' imps'

transformImport :: String -> [(String,String)] -> Import -> (Import, String)
transformImport th mapping (SimpleImp cat wh) =
  let newCat = transformImportedCat mapping cat
      impStr = case newCat of
                 IdCat (Ident s) -> s
                 _ -> ""
      newWh = transformWhere th impStr wh
  in (SimpleImp newCat newWh, impStr)

transformImports :: String -> [(String,String)] -> Imports -> Imports
transformImports th mapping EmptyImp = EmptyImp
transformImports th mapping (AndImp imp imps) =
  let (imp', _) = transformImport th mapping imp
      imps' = transformImports th mapping imps
  in AndImp imp' imps'

transformWhere :: String -> String -> Where -> Where
transformWhere _ _ Empty = Empty
transformWhere th impStr (Block reps) =
  Block (map (transformReplacement th impStr) reps)

transformReplacement :: String -> String -> Replacement -> Replacement
transformReplacement th impStr (SimpleRepl (Ident preName) (Ident _preCat) (Ident postName) (Ident postCat) items) =
  let impBase    = baseFromImported impStr
      newPre     = impBase ++ "_" ++ preName
      newPost    = th ++ "_" ++ postName
      newPostCat = mangleLocalIdent th postCat
      (_, newItems) = transformItemsExport th items
  in SimpleRepl (Ident newPre) (Ident impStr) (Ident newPost) (Ident newPostCat) newItems

transformItemsExport :: String -> [Item] -> ([Def], [Item])
transformItemsExport th items = ([], map (transformItemExport th) items)

transformItemExport :: String -> Item -> Item
transformItemExport th (NTerminal cat) = NTerminal (mangleLocalCat th cat)
transformItemExport _ item = item

mangleLocalCat :: String -> Cat -> Cat
mangleLocalCat th (IdCat (Ident s)) = IdCat (Ident (th ++ "_" ++ s))
mangleLocalCat th (ListCat c) = ListCat (mangleLocalCat th c)
mangleLocalCat th (ImportedCat _ c) = mangleLocalCat th c

mangleLocalIdent :: String -> String -> String
mangleLocalIdent th s = th ++ "_" ++ s

mangleLocalIdent' :: String -> Ident -> Ident
mangleLocalIdent' th (Ident s) = Ident (th ++ "_" ++ s)

transformImportedCat :: [(String,String)] -> Cat -> Cat
transformImportedCat mapping (ImportedCat (Ident q) c) =
  case c of
    IdCat (Ident s) ->
      case lookup q mapping of
        Just t -> IdCat (Ident (t ++ "_" ++ s))
        Nothing -> ImportedCat (Ident q) c
    _ -> ImportedCat (Ident q) c
transformImportedCat _ cat = cat

transformModule :: Module -> Module
transformModule (ModuleImpl name progs) =
  let transformedProgs = map transformProg progs
      accumulatedProgs = accumulateTheories transformedProgs
  in ModuleImpl name accumulatedProgs

transformProg :: Prog -> Prog
transformProg (ProgDecl d) = ProgDecl (transformDecl d)
transformProg other        = other

transformDecl :: Decl -> Decl
transformDecl (GSLTDeclAll thName varDecls exports (Generators g) eqns rewrites) =
  let thStr   = case thName of
                  NameVar (Ident s) -> s
                  _                 -> "Wildcard"
      mapping = buildMapping varDecls
      newExports  = transformExports thStr mapping exports
      newGrammar  = transformGrammarWithTheory thStr g
  in GSLTDeclAll thName varDecls newExports (Generators newGrammar) eqns rewrites
transformDecl d = d

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

checkModule :: Module -> Either String ()
checkModule (ModuleImpl _ progs) = mapM_ checkProg progs

checkProg :: Prog -> Either String ()
checkProg (ProgDecl d) = checkDecl d
checkProg _            = Right ()

checkDecl :: Decl -> Either String ()
checkDecl (GSLTDeclAll _ _ _ (Generators g) _ _) = checkGrammar g
checkDecl _                                      = Right ()

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

---------------------------------------------------------
-- * Accumulation of Extended Theory Rules
---------------------------------------------------------

-- When a theory extends another, we need to copy (accumulate) the production rules
-- from the extended theory’s grammar, renaming the extended theory’s prefix to the
-- current theory’s prefix. If replacement rules are provided (via a where clause),
-- then only those replacements (converted to production rules) are accumulated.

-- Renaming helpers: given an old prefix and a new prefix, replace occurrences
-- in identifiers, labels, categories, items, and definitions.

renameIdent :: String -> String -> Ident -> Ident
renameIdent old new (Ident s) =
  if (old ++ "_") `isPrefixOf` s then Ident (new ++ drop (length old) s) else Ident s

renameLabel :: String -> String -> Label -> Label
renameLabel old new (LabNoP (Id ident))      = LabNoP (Id (renameIdent old new ident))
renameLabel old new (LabP   (Id ident) prof)   = LabP   (Id (renameIdent old new ident)) prof
renameLabel old new (LabPF  (Id ident) l2 prof)  = LabPF  (Id (renameIdent old new ident)) l2 prof
renameLabel old new (LabF   (Id ident) l2)       = LabF   (Id (renameIdent old new ident)) l2
renameLabel _ _ lab                             = lab

renameCat :: String -> String -> Cat -> Cat
renameCat old new (IdCat ident) = IdCat (renameIdent old new ident)
renameCat old new (ListCat c)   = ListCat (renameCat old new c)
renameCat old new (ImportedCat ident c) = ImportedCat ident (renameCat old new c)

renameItem :: String -> String -> Item -> Item
renameItem old new (NTerminal cat) = NTerminal (renameCat old new cat)
renameItem _ _ item                = item

renameDef :: String -> String -> Def -> Def
renameDef old new (Rule l cat items) =
  Rule (renameLabel old new l) (renameCat old new cat) (map (renameItem old new) items)
renameDef old new (Internal l cat items) =
  Internal (renameLabel old new l) (renameCat old new cat) (map (renameItem old new) items)
renameDef _ _ d = d

isProduction :: Def -> Bool
isProduction (Rule _ _ _)     = True
isProduction (Internal _ _ _) = True
isProduction _                = False

renameGrammar :: String -> String -> Grammar -> [Def]
renameGrammar old new (MkGrammar defs) =
  [ renameDef old new d | d <- defs, isProduction d ]

-- Convert a Replacement into a production rule (Def)
replacementToDef :: Replacement -> Def
replacementToDef (SimpleRepl _ _ (Ident post) (Ident postCat) items) =
  Rule (LabNoP (Id (Ident post))) (IdCat (Ident postCat)) items

-- Helper: Flatten an Import and its following Imports into a list.
flattenImports :: Import -> Imports -> [Import]
flattenImports imp EmptyImp            = [imp]
flattenImports imp (AndImp imp' rest)    = imp : flattenImports imp' rest

-- Accumulate production rules from a single import.
accumulateSingleImport :: TheoryMap -> String -> Import -> [Def]
accumulateSingleImport tm currentTh (SimpleImp cat wh) =
  case cat of
    IdCat (Ident s) ->
      let extTh = takeWhile (/= '_') s  -- e.g. "Monoid" from "Monoid_Proc"
      in case wh of
           Empty -> case lookup extTh tm of
                      Just extGrammar -> renameGrammar extTh currentTh extGrammar
                      Nothing -> []  -- extended theory not found
           Block replacements ->
                  map replacementToDef replacements
    _ -> []
      
-- For an export of the form Extends, process all imports (using "and" if present).
accumulateExport :: TheoryMap -> String -> Export -> [Def]
accumulateExport tm currentTh (Extends (Ident _localCat) imp imps) =
  let allImps = flattenImports imp imps
  in concatMap (accumulateSingleImport tm currentTh) allImps
accumulateExport _ _ _ = []

-- Accumulation pass over theory declarations.
-- We thread a mapping from theory name to the (accumulated) Grammar.
type TheoryMap = [(String, Grammar)]

---------------------------------------------------------
-- * Deduplication of Duplicate Production Rules
---------------------------------------------------------

-- Given two production rules, if they have the same left-hand side category and identical right-hand sides,
-- then we merge their labels.
-- We assume production rules are built using the Rule constructor.
deduplicateRules :: [Def] -> [Def]
deduplicateRules defs =
  let (others, rules) = partition (not . isProductionDef) defs
      -- Group production rules by their key: (category, items)
      grouped = groupBy ((==) `on` ruleKey) (sortBy (compare `on` ruleKey) rules)
      deduped = map combineGroup grouped
  in others ++ deduped
  where
    isProductionDef (Rule _ _ _) = True
    isProductionDef _ = False
    ruleKey (Rule _ cat items) = (cat, items)
    ruleKey _ = error "Not a production rule"
    combineGroup :: [Def] -> Def
    combineGroup [r] = r
    combineGroup rs@(Rule _ cat items : _) =
      let labels = map (\(Rule lab _ _) -> lab) rs
          newLabel = combineLabels labels
      in Rule newLabel cat items

-- Combine a list of labels into a single label.
-- We assume each label is of the form LabNoP (Id (Ident s)).
combineLabels :: [Label] -> Label
combineLabels ls = LabNoP (Id (Ident (combineLabelStrings (map extractLabelString ls))))

-- Extract the string from a generated label.
extractLabelString :: Label -> String
extractLabelString (LabNoP (Id (Ident s))) = s
extractLabelString lab = error ("Unexpected label format: " ++ show lab)

-- Combine label strings by splitting on underscores and merging.
-- For example, combining
--   "Rholang_PNew_0_Id" and "Rholang_PRecv_0_Id"
-- produces "Rholang_PNew_0_PRecv_0_Id".
combineLabelStrings :: [String] -> String
combineLabelStrings lbls =
  let unique = nub lbls
  in case unique of
       [] -> error "No labels to combine"
       (s:rest) ->
         case splitUnderscores s of
           [] -> s
           tokens ->
             let theory  = head tokens
                 suffix  = last tokens
                 mid     = tail (init tokens)
                 restMids = concatMap (\str ->
                               let ts = splitUnderscores str
                               in drop 1 (take (length ts - 1) ts)
                             ) rest
             in joinUnderscores ([theory] ++ mid ++ restMids ++ [suffix])

-- Utility: split a string on underscore.
splitUnderscores :: String -> [String]
splitUnderscores s = wordsWhen (=='_') s

-- Utility: join tokens with underscores.
joinUnderscores :: [String] -> String
joinUnderscores = intercalate "_"

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = break p s'

---------------------------------------------------------
-- * Updated Accumulation Pass
---------------------------------------------------------

-- In accumulateProg, when building the new grammar from the base definitions and extra (accumulated) rules,
-- we now apply deduplication.
accumulateProg :: TheoryMap -> Prog -> (TheoryMap, Prog)
accumulateProg tm (ProgDecl d@(GSLTDeclAll thName varDecls exports freeTheory eqns rewrites)) =
  let thStr = case thName of
                NameVar (Ident s) -> s
                _                 -> "Wildcard"
      (Generators (MkGrammar baseDefs)) = freeTheory
      extraRules = case exports of
                     Categories exps -> concatMap (accumulateExport tm thStr) exps
      -- Merge base definitions with extra rules and deduplicate them.
      newGrammar = MkGrammar (deduplicateRules (baseDefs ++ extraRules))
      newFreeTheory = Generators newGrammar
      newDecl = GSLTDeclAll thName varDecls exports newFreeTheory eqns rewrites
      newTM = (thStr, newGrammar) : tm
  in (newTM, ProgDecl newDecl)
accumulateProg tm prog = (tm, prog)

accumulateTheories :: [Prog] -> [Prog]
accumulateTheories progs =
  snd (mapAccumL accumulateProg [] progs)

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

