{-# LANGUAGE OverloadedStrings #-}

module Interpreter where

import MettaVenus.Abs
import Data.List (intercalate)

-- The Theory record type with updated Export type.
data Theory = Theory
  { exports   :: [Export]      -- List of exports (with Cat instead of Ident)
  , terms     :: [Def]         -- List of definitions/terms
  , equations :: [Equation]    -- List of equations
  , rewrites  :: [RewriteDecl] -- List of rewrite declarations
  } deriving (Eq, Show)

-- A convenient value for an empty theory.
emptyTheory :: Theory
emptyTheory = Theory { exports = [], terms = [], equations = [], rewrites = [] }

-- An environment is a list of (String, Theory) pairs.
type Env = [(String, Theory)]

-- | Evaluate an Inst in a given context of Modules and an environment,
--   producing either an error message or a Theory.
evalInst :: [Module] -> Env -> Inst -> Either String Theory
evalInst ctx env inst = case inst of
  InstAddExports i exps -> do
      th <- evalInst ctx env i
      return th { exports = exports th ++ exps }
  InstAddReplacements i reps -> Right emptyTheory  -- Stub: process replacements
  InstAddTerms i gram -> do
      th <- evalInst ctx env i
      case gram of
         MkGrammar defs -> return th { terms = terms th ++ defs }
  InstAddEquations i eqs -> do
      th <- evalInst ctx env i
      return th { equations = equations th ++ eqs }
  InstAddRewrites i rws -> do
      th <- evalInst ctx env i
      return th { rewrites = rewrites th ++ rws }
  InstEmpty -> Right emptyTheory
  InstCtor name insts -> Right emptyTheory  -- Stub: process constructor instance
  InstCtorK name insts progs -> Right emptyTheory  -- Stub: process constructor with progs
  InstRef ident -> Right emptyTheory  -- Stub: process reference
  InstRec ptrn i1 i2 ->
      case ptrn of
         PtrnInst i0 -> do
             env' <- unifyInst ctx i0 i1 env
             evalInst ctx env' i2
         _ -> Left $ "InstRec: pattern is not PtrnInst: " ++ show ptrn
  InstTail i         -> Right emptyTheory  -- Stub
  InstSup i          -> Right emptyTheory  -- Stub
  InstInf i          -> Right emptyTheory  -- Stub
  InstFree name      -> Right emptyTheory  -- Stub
  InstFreeL name ps  -> Right emptyTheory  -- Stub
  InstComp i1 i2     -> Right emptyTheory  -- Stub
  InstConj i1 i2     -> Right emptyTheory  -- Stub
  InstDisj i1 i2     -> Right emptyTheory  -- Stub
  InstSub i1 i2      -> Right emptyTheory  -- Stub
  InstRest i1 i2     -> Right emptyTheory  -- Stub
  InstGCD i1 i2      -> Right emptyTheory  -- Stub
  InstPar i1 i2      -> Right emptyTheory  -- Stub

-- | Unify two Inst ASTs (n0 and n1) in the given context and environment.
--   If n0 is an InstRef (with an Ident), evaluate n1 and add the resulting Theory
--   to the environment (using the string from the Ident). Otherwise, if n0 and n1
--   have the same constructor, recursively unify their children. On a mismatch,
--   return a Left with an error message showing the two instantiations.
unifyInst :: [Module] -> Inst -> Inst -> Env -> Either String Env
unifyInst ctx n0 n1 env = case n0 of
  InstRef (Ident s) -> do
      th <- evalInst ctx env n1
      return ((s, th) : env)
  _ ->
      case (n0, n1) of
        (InstAddExports i0 exps0, InstAddExports i1 exps1) ->
           if exps0 == exps1
              then unifyInst ctx i0 i1 env
              else Left $ "Mismatch in InstAddExports:\n  " ++ show n0 ++ "\nvs\n  " ++ show n1
        (InstAddTerms i0 gram0, InstAddTerms i1 gram1) ->
           if gram0 == gram1
              then unifyInst ctx i0 i1 env
              else Left $ "Mismatch in InstAddTerms:\n  " ++ show n0 ++ "\nvs\n  " ++ show n1
        (InstAddEquations i0 eqs0, InstAddEquations i1 eqs1) ->
           if eqs0 == eqs1
              then unifyInst ctx i0 i1 env
              else Left $ "Mismatch in InstAddEquations:\n  " ++ show n0 ++ "\nvs\n  " ++ show n1
        (InstAddRewrites i0 rws0, InstAddRewrites i1 rws1) ->
           if rws0 == rws1
              then unifyInst ctx i0 i1 env
              else Left $ "Mismatch in InstAddRewrites:\n  " ++ show n0 ++ "\nvs\n  " ++ show n1
        (InstEmpty, InstEmpty) -> Right env
        (InstCtor name0 insts0, InstCtor name1 insts1) ->
           if name0 == name1 && length insts0 == length insts1
              then unifyInstList ctx insts0 insts1 env
              else Left $ "Mismatch in InstCtor:\n  " ++ show n0 ++ "\nvs\n  " ++ show n1
        (InstCtorK name0 insts0 progs0, InstCtorK name1 insts1 progs1) ->
           if name0 == name1 && length insts0 == length insts1 && progs0 == progs1
              then unifyInstList ctx insts0 insts1 env
              else Left $ "Mismatch in InstCtorK:\n  " ++ show n0 ++ "\nvs\n  " ++ show n1
        (InstTail i0, InstTail i1) ->
           unifyInst ctx i0 i1 env
        (InstSup i0, InstSup i1) ->
           unifyInst ctx i0 i1 env
        (InstInf i0, InstInf i1) ->
           unifyInst ctx i0 i1 env
        (InstFree name0, InstFree name1) ->
           if name0 == name1 then Right env
           else Left $ "Mismatch in InstFree:\n  " ++ show n0 ++ "\nvs\n  " ++ show n1
        (InstFreeL name0 ps0, InstFreeL name1 ps1) ->
           if name0 == name1 && ps0 == ps1 then Right env
           else Left $ "Mismatch in InstFreeL:\n  " ++ show n0 ++ "\nvs\n  " ++ show n1
        (InstComp i0 j0, InstComp i1 j1) -> do
              env' <- unifyInst ctx i0 i1 env
              unifyInst ctx j0 j1 env'
        (InstConj i0 j0, InstConj i1 j1) -> do
              env' <- unifyInst ctx i0 i1 env
              unifyInst ctx j0 j1 env'
        (InstDisj i0 j0, InstDisj i1 j1) -> do
              env' <- unifyInst ctx i0 i1 env
              unifyInst ctx j0 j1 env'
        (InstSub i0 j0, InstSub i1 j1) -> do
              env' <- unifyInst ctx i0 i1 env
              unifyInst ctx j0 j1 env'
        (InstRest i0 j0, InstRest i1 j1) -> do
              env' <- unifyInst ctx i0 i1 env
              unifyInst ctx j0 j1 env'
        (InstGCD i0 j0, InstGCD i1 j1) -> do
              env' <- unifyInst ctx i0 i1 env
              unifyInst ctx j0 j1 env'
        (InstPar i0 j0, InstPar i1 j1) -> do
              env' <- unifyInst ctx i0 i1 env
              unifyInst ctx j0 j1 env'
        _ -> Left $ "Unification failed: mismatch between\n  " ++ show n0 ++ "\nand\n  " ++ show n1

-- | Helper to unify lists of Insts pairwise.
unifyInstList :: [Module] -> [Inst] -> [Inst] -> Env -> Either String Env
unifyInstList _ [] [] env = Right env
unifyInstList ctx (x:xs) (y:ys) env = do
    env' <- unifyInst ctx x y env
    unifyInstList ctx xs ys env'
unifyInstList _ _ _ _ = Left "Unification failed: list length mismatch"
