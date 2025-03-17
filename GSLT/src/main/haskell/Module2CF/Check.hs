-- | Module for checking the correctness of grammars and modules.
-- It verifies that productions and declarations follow certain constraints,
-- such as ensuring indices in BindTerminal items are valid.
module Check
  ( checkGrammar
  , checkDef
  , checkProduction
  , checkModule
  , checkProg
  , checkDecl
  ) where

import Prelude
import Control.Monad ( forM_ )
import MettaVenus.Abs
import Utils ( isTerminal )

--------------------------------------------------------------------------------
-- * Grammar Checking
--------------------------------------------------------------------------------

-- | Checks the entire grammar.
checkGrammar :: Grammar -> Either String ()
checkGrammar (MkGrammar defs) = mapM_ checkDef defs

-- | Checks a single definition.
checkDef :: Def -> Either String ()
checkDef (Rule label _ items)     = checkProduction ("production " ++ show label) items
checkDef (Internal label _ items) = checkProduction ("internal production " ++ show label) items
checkDef _                        = Right ()

-- | Checks the production rules of a definition.
-- It ensures that BindTerminal items have non-empty index lists,
-- and that indices are within the allowed range.
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

--------------------------------------------------------------------------------
-- * Module and Declaration Checking
--------------------------------------------------------------------------------

-- | Checks an entire module by verifying each program.
checkModule :: Module -> Either String ()
checkModule (ModuleImpl _ progs) = mapM_ checkProg progs

-- | Checks a single program.
checkProg :: Prog -> Either String ()
checkProg (ProgDecl d) = checkDecl d
checkProg _            = Right ()

-- | Checks a declaration.
-- For GSLTDeclAll declarations, it checks the associated grammar.
checkDecl :: Decl -> Either String ()
checkDecl (GSLTDeclAll _ _ _ (Generators g) _ _) = checkGrammar g
checkDecl _                                      = Right ()
