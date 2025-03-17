-- | Module for renaming identifiers, labels, and categories.
-- This module provides functions to update names with a new prefix or change them
-- according to a specific naming convention.
module Rename
  ( renameIdent
  , renameLabel
  , renameCat
  , renameItem
  , renameDef
  , renameGrammar
  ) where

import Prelude
import Data.List ( isPrefixOf )
import MettaVenus.Abs

--------------------------------------------------------------------------------
-- * Identifier Renaming
--------------------------------------------------------------------------------

-- | Renames an identifier.
-- If the identifier already has the old prefix, it replaces it with the new prefix.
renameIdent :: String -> String -> Ident -> Ident
renameIdent old new (Ident s) =
  if (old ++ "_") `isPrefixOf` s then Ident (new ++ drop (length old) s) else Ident s

--------------------------------------------------------------------------------
-- * Label Renaming
--------------------------------------------------------------------------------

-- | Renames a label by applying the identifier renaming.
renameLabel :: String -> String -> Label -> Label
renameLabel old new (LabNoP (Id ident))      = LabNoP (Id (renameIdent old new ident))
renameLabel old new (LabP   (Id ident) prof)   = LabP   (Id (renameIdent old new ident)) prof
renameLabel old new (LabPF  (Id ident) l2 prof)  = LabPF  (Id (renameIdent old new ident)) l2 prof
renameLabel old new (LabF   (Id ident) l2)       = LabF   (Id (renameIdent old new ident)) l2
renameLabel _ _ lab                             = lab

--------------------------------------------------------------------------------
-- * Category Renaming
--------------------------------------------------------------------------------

-- | Renames a category by applying renaming to its identifier.
renameCat :: String -> String -> Cat -> Cat
renameCat old new (IdCat ident) = IdCat (renameIdent old new ident)
renameCat old new (ListCat c)   = ListCat (renameCat old new c)
renameCat old new (ImportedCat ident c) = ImportedCat ident (renameCat old new c)

--------------------------------------------------------------------------------
-- * Item and Definition Renaming
--------------------------------------------------------------------------------

-- | Renames a grammar item.
-- Only non-terminal items (NTerminal) are renamed.
renameItem :: String -> String -> Item -> Item
renameItem old new (NTerminal cat) = NTerminal (renameCat old new cat)
renameItem _ _ item                = item

-- | Renames a definition by renaming its label, category, and items.
renameDef :: String -> String -> Def -> Def
renameDef old new (Rule l cat items) =
  Rule (renameLabel old new l) (renameCat old new cat) (map (renameItem old new) items)
renameDef old new (Internal l cat items) =
  Internal (renameLabel old new l) (renameCat old new cat) (map (renameItem old new) items)
renameDef _ _ d = d

-- | Renames all productions in a grammar.
renameGrammar :: String -> String -> Grammar -> [Def]
renameGrammar old new (MkGrammar defs) =
  [ renameDef old new d | d <- defs, isProduction d ]
  where
    isProduction (Rule _ _ _)     = True
    isProduction (Internal _ _ _) = True
    isProduction _                = False
