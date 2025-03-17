module Accumulate
  ( accumulateProg
  , accumulateTheories
  , deduplicateRules
  ) where

import Prelude
import Data.List ( partition, groupBy, sortBy, nub, mapAccumL )
import Data.Function ( on )
import Data.List ( intercalate )
import MettaVenus.Abs
import Rename ( renameGrammar )
import Utils ( splitUnderscores, joinUnderscores )

-- | Flattens an import tree into a list of imports.
flattenImports :: Import -> Imports -> [Import]
flattenImports imp EmptyImp         = [imp]
flattenImports imp (AndImp imp' rest) = imp : flattenImports imp' rest

-- | Accumulate definitions from a single import.
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

-- | Converts a replacement to a definition.
replacementToDef :: Replacement -> Def
replacementToDef (SimpleRepl _ _ (Ident post) (Ident postCat) items) =
  Rule (LabNoP (Id (Ident post))) (IdCat (Ident postCat)) items

-- | Accumulate definitions from an export.
accumulateExport :: TheoryMap -> String -> Export -> [Def]
accumulateExport tm currentTh (Extends (Ident _localCat) imp imps) =
  let allImps = flattenImports imp imps
  in concatMap (accumulateSingleImport tm currentTh) allImps
accumulateExport _ _ _ = []

type TheoryMap = [(String, Grammar)]

accumulateProg :: TheoryMap -> Prog -> (TheoryMap, Prog)
accumulateProg tm (ProgDecl d@(GSLTDeclAll thName varDecls exports freeTheory eqns rewrites)) =
  let thStr = case thName of
                NameVar (Ident s) -> s
                _                 -> "Wildcard"
      (Generators (MkGrammar baseDefs)) = freeTheory
      extraRules = case exports of
                     Categories exps -> concatMap (accumulateExport tm thStr) exps
      newGrammar = MkGrammar (deduplicateRules (baseDefs ++ extraRules))
      newFreeTheory = Generators newGrammar
      newDecl = GSLTDeclAll thName varDecls exports newFreeTheory eqns rewrites
      newTM = (thStr, newGrammar) : tm
  in (newTM, ProgDecl newDecl)
accumulateProg tm prog = (tm, prog)

accumulateTheories :: [Prog] -> [Prog]
accumulateTheories progs =
  snd (mapAccumL accumulateProg [] progs)

deduplicateRules :: [Def] -> [Def]
deduplicateRules defs =
  let (others, rules) = partition (not . isProductionDef) defs
      grouped = groupBy ((==) `on` ruleKey) (sortBy (compare `on` ruleKey) rules)
      deduped = map combineGroup grouped
  in others ++ deduped
  where
    isProductionDef (Rule _ _ _) = True
    isProductionDef _            = False
    ruleKey (Rule _ cat items)   = (cat, items)
    ruleKey _ = error "Not a production rule"
    combineGroup :: [Def] -> Def
    combineGroup [r] = r
    combineGroup rs@(Rule _ cat items : _) =
      let labels = map (\(Rule lab _ _) -> lab) rs
          newLabel = combineLabels labels
      in Rule newLabel cat items
    combineLabels :: [Label] -> Label
    combineLabels ls = LabNoP (Id (Ident (combineLabelStrings (map extractLabelString ls))))
    extractLabelString :: Label -> String
    extractLabelString (LabNoP (Id (Ident s))) = s
    extractLabelString lab = error ("Unexpected label format: " ++ show lab)
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
