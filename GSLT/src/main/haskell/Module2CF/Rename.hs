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

renameGrammar :: String -> String -> Grammar -> [Def]
renameGrammar old new (MkGrammar defs) =
  [ renameDef old new d | d <- defs, isProduction d ]
  where
    isProduction (Rule _ _ _)     = True
    isProduction (Internal _ _ _) = True
    isProduction _                = False
