-- | Module for accumulating and deduplicating rules from imports and exports.
-- This module handles flattening import trees, extracting extra definitions
-- from external theories, and merging duplicate rules.
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

--------------------------------------------------------------------------------
-- * Import Accumulation Helpers
--------------------------------------------------------------------------------

-- | Flattens an import tree into a list of individual imports.
flattenImports :: Import -> Imports -> [Import]
flattenImports imp EmptyImp         = [imp]
flattenImports imp (AndImp imp' rest) = imp : flattenImports imp' rest

-- | Accumulates definitions from a single import.
-- If the imported category matches an external theory, it retrieves the external
-- grammar or processes replacements.
accumulateSingleImport :: TheoryMap -> String -> Import -> [Def]
accumulateSingleImport tm currentTh (SimpleImp cat wh) =
  case cat of
    IdCat (Ident s) ->
      let extTh = takeWhile (/= '_') s  -- e.g. "Monoid" from "Monoid_Proc"
      in case wh of
           Empty -> case lookup extTh tm of
                      Just extGrammar -> renameGrammar extTh currentTh extGrammar
                      Nothing -> []  -- Extended theory not found.
           Block replacements ->
             map replacementToDef replacements
    _ -> []
    
-- | Converts a replacement into a grammar definition.
replacementToDef :: Replacement -> Def
replacementToDef (SimpleRepl _ _ (Ident post) (Ident postCat) items) =
  Rule (LabNoP (Id (Ident post))) (IdCat (Ident postCat)) items

-- | Accumulates definitions from an export declaration.
accumulateExport :: TheoryMap -> String -> Export -> [Def]
accumulateExport tm currentTh (Extends (Ident _localCat) imp imps) =
  let allImps = flattenImports imp imps
  in concatMap (accumulateSingleImport tm currentTh) allImps
accumulateExport _ _ _ = []

--------------------------------------------------------------------------------
-- * Accumulation of Theories and Deduplication
--------------------------------------------------------------------------------

type TheoryMap = [(String, Grammar)]

-- | Accumulates a single program declaration by incorporating external rules.
-- It builds a new grammar by combining the base definitions with extra rules
-- from external theories.
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

-- | Accumulates theories from a list of programs.
-- It uses mapAccumL to thread the TheoryMap through the list of programs.
accumulateTheories :: [Prog] -> [Prog]
accumulateTheories progs =
  snd (mapAccumL accumulateProg [] progs)

-- | Deduplicates production rules by grouping those with the same category and items.
-- For duplicate rules, their labels are merged.
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

    -- | Combines multiple labels into a single label.
    combineLabels :: [Label] -> Label
    combineLabels ls = LabNoP (Id (Ident (combineLabelStrings (map extractLabelString ls))))

    -- | Extracts the string from a label.
    extractLabelString :: Label -> String
    extractLabelString (LabNoP (Id (Ident s))) = s
    extractLabelString lab = error ("Unexpected label format: " ++ show lab)

    -- | Merges a list of label strings using underscores.
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
