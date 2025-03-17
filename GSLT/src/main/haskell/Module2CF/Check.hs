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

checkModule :: Module -> Either String ()
checkModule (ModuleImpl _ progs) = mapM_ checkProg progs

checkProg :: Prog -> Either String ()
checkProg (ProgDecl d) = checkDecl d
checkProg _            = Right ()

checkDecl :: Decl -> Either String ()
checkDecl (GSLTDeclAll _ _ _ (Generators g) _ _) = checkGrammar g
checkDecl _                                      = Right ()
