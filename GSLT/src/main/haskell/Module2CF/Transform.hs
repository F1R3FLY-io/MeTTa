module Transform
  ( labelToString
  , baseTransformGrammar
  , transformGrammarWithTheory
  , transformModule
  , transformProg
  , transformDecl
  , transformExports
  , transformExport
  , transformImport
  , transformImports
  , transformWhere
  , transformReplacement
  , transformItemsExport
  , transformItemExport
  , buildMapping
  , mangleCat
  , prefixLabel
  , baseFromImported
  , transformItemWithTheory
  , transformItemsWithTheory
  , transformDefWithTheory
  , mangleLocalCat
  , mangleLocalIdent
  , mangleLocalIdent'
  , transformImportedCat
  ) where

import Prelude
import Data.List (nub, intercalate)
import MettaVenus.Abs
import MettaVenus.Lex   ( Token, mkPosToken )
import MettaVenus.Par   ( pModule, myLexer )
import MettaVenus.Print ( Print, printTree )
import Utils ( isTerminal )
import Accumulate (accumulateTheories)

-- * Helper: Converting labels to strings
labelToString :: Label -> String
labelToString (LabNoP (Id (Ident s)))      = s
labelToString (LabP   (Id (Ident s)) _)    = s
labelToString (LabPF  (Id (Ident s)) _ _)  = s
labelToString (LabF   (Id (Ident s)) _)    = s

-- * Base Transformation Functions
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

-- * Mangling and Prefixing Helpers
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

-- * Transformation Functions with Theory
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

-- * Export and Import Transformations
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
mangleLocalCat th (ListCat c)       = ListCat (mangleLocalCat th c)
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

-- * Mapping for variable declarations
buildMapping :: [VariableDecl] -> [(String,String)]
buildMapping [] = []
buildMapping (VarDecl (Ident v) name : rest) =
  case name of
    NameVar (Ident t) -> (v, t) : buildMapping rest
    _ -> buildMapping rest

-- * Module/Program Transformation
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
