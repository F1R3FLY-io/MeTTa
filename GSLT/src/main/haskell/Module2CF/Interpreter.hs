{-# LANGUAGE OverloadedStrings #-}

module Interpreter where

import MettaVenus.Abs

-- Define an environment as a list of (String, Theory) pairs.
type Env = [(String, Theory)]

-- The Theory record type with updated Export type.
data Theory = Theory
  { exports   :: [Export]      -- List of exports (now with Cat)
  , terms     :: [Def]         -- List of definitions/terms
  , equations :: [Equation]    -- List of equations
  , rewrites  :: [RewriteDecl] -- List of rewrite declarations
  } deriving (Eq, Show)

-- A convenient value for an empty theory.
emptyTheory :: Theory
emptyTheory = Theory { exports = [], terms = [], equations = [], rewrites = [] }

-- Evaluates an Inst in a given context of Modules, with an environment, producing a Theory.
evalInst :: Env -> [Module] -> Inst -> Either String Theory
evalInst env ctx inst = case inst of
  InstAddExports i exps -> do
    th <- evalInst env ctx i
    return th { exports = exports th ++ exps }
    
  InstAddReplacements i reps -> Right emptyTheory  -- Stub: process replacements
  
  InstAddTerms i gram -> do
    th <- evalInst env ctx i
    case gram of
      MkGrammar defs -> return th { terms = terms th ++ defs }
      
  InstAddEquations i eqs -> do
    th <- evalInst env ctx i
    return th { equations = equations th ++ eqs }
    
  InstAddRewrites i rws -> do
    th <- evalInst env ctx i
    return th { rewrites = rewrites th ++ rws }
    
  InstEmpty -> Right emptyTheory
  
  InstCtor name insts -> Right emptyTheory  -- Stub
  
  InstCtorK name insts progs -> Right emptyTheory  -- Stub
  
  InstRef ident -> Right emptyTheory  -- Stub
  
  InstRec ptrn i1 i2 ->
    case ptrn of
      PtrnInst (InstRef ident) ->
        case ident of
          Ident s -> do
            th1 <- evalInst env ctx i1
            let env' = (s, th1) : env
            evalInst env' ctx i2
      _ -> Left ("expected an identifier, got " ++ show ptrn)
      
  InstTail i -> Right emptyTheory  -- Stub
  
  InstSup i -> Right emptyTheory  -- Stub
  
  InstInf i -> Right emptyTheory  -- Stub
  
  InstFree name -> Right emptyTheory  -- Stub
  
  InstFreeL name progs -> Right emptyTheory  -- Stub
  
  InstComp i1 i2 -> Right emptyTheory  -- Stub
  
  InstConj i1 i2 -> Right emptyTheory  -- Stub
  
  InstDisj i1 i2 -> Right emptyTheory  -- Stub
  
  InstSub i1 i2 -> Right emptyTheory  -- Stub
  
  InstRest i1 i2 -> Right emptyTheory  -- Stub
  
  InstGCD i1 i2 -> Right emptyTheory  -- Stub
  
  InstPar i1 i2 -> Right emptyTheory  -- Stub
