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
-- * Rewrite Checking
--------------------------------------------------------------------------------

-- | Collects all variable names (ASTVar) from an AST expression.
collectVars :: AST -> [Ident]
collectVars (ASTVar ident) = [ident]
collectVars (ASTSubst a1 a2 ident) = collectVars a1 ++ collectVars a2 ++ [ident]
collectVars (ASTSExp _ asts) = concatMap collectVars asts

-- | Extracts variable identifiers from a hypothesis.
collectHypVars :: Hypothesis -> [Ident]
collectHypVars (Hyp ident1 ident2) = [ident1, ident2]

-- | Checks a RewriteBase rule ensuring all right-hand side variables appear on the left.
checkRewriteBase :: String -> AST -> AST -> Either String ()
checkRewriteBase ruleName lhs rhs =
  let lhsVars = collectVars lhs
      rhsVars = collectVars rhs
      missing = filter (`notElem` lhsVars) rhsVars
  in if null missing
     then Right ()
     else Left $ "Rewrite rule '" ++ ruleName ++ "' contains undefined variables on the right-hand side: " ++ show missing

-- | Checks a rewrite rule, incorporating hypotheses when present.
checkRewrite :: RewriteDecl -> Either String ()
checkRewrite (RDecl (Ident ruleName) rewrite) = case rewrite of
  RewriteBase lhs rhs -> checkRewriteBase ruleName lhs rhs
  RewriteContext (Hyp ident1 ident2) innerRewrite ->
    let extraVars = [ident1, ident2]  -- Include hypothesis variables
    in case innerRewrite of
         RewriteBase lhs rhs ->
           let lhsVars = collectVars lhs ++ extraVars
               rhsVars = collectVars rhs
               missing = filter (`notElem` lhsVars) rhsVars
           in if null missing
              then Right ()
              else Left $ "Rewrite rule '" ++ ruleName ++ "' (with hypothesis) contains undefined variables on the right-hand side: " ++ show missing
         _ -> Left "Unexpected nested rewrite structure."

-- | Checks all rewrites in a declaration.
checkRewrites :: Rewrites -> Either String ()
checkRewrites (Transitions rewrites) = mapM_ checkRewrite rewrites

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
checkDecl (GSLTDeclAll _ _ _ (Generators g) _ rewrites) = do
  checkGrammar g
  checkRewrites rewrites
checkDecl _ = Right ()