{-# LANGUAGE OverloadedStrings #-}

module Interpreter where

import MettaVenus.Abs

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

-- Evaluates an Inst in a given context of Modules, producing a Theory.
evalInst :: [Module] -> Inst -> Theory
evalInst ctx inst = case inst of
  InstAddExports i exps ->
    let th = evalInst ctx i
    in th { exports = exports th ++ exps }
  InstAddReplacements i reps -> emptyTheory  -- Stub: process replacements
  InstAddTerms i gram ->
    let th = evalInst ctx i
    in case gram of
         MkGrammar defs -> th { terms = terms th ++ defs }
  InstAddEquations i eqs ->
    let th = evalInst ctx i
    in th { equations = equations th ++ eqs }
  InstAddRewrites i rws ->
    let th = evalInst ctx i
    in th { rewrites = rewrites th ++ rws }
  InstEmpty                  -> emptyTheory  -- Stub: represents an empty instance
  InstCtor name insts        -> emptyTheory  -- Stub: process a constructor instance
  InstCtorK name insts progs -> emptyTheory  -- Stub: process a constructor with progs
  InstRef ident              -> emptyTheory  -- Stub: process a reference
  InstRec ptrn i1 i2         -> emptyTheory  -- Stub: process a recursive instance
  InstTail i                 -> emptyTheory  -- Stub: process tail
  InstSup i                  -> emptyTheory  -- Stub: process sup
  InstInf i                  -> emptyTheory  -- Stub: process inf
  InstFree name              -> emptyTheory  -- Stub: process free instance
  InstFreeL name progs       -> emptyTheory  -- Stub: process free instance with additional programs
  InstComp i1 i2             -> emptyTheory  -- Stub: process composition
  InstConj i1 i2             -> emptyTheory  -- Stub: process conjunction
  InstDisj i1 i2             -> emptyTheory  -- Stub: process disjunction
  InstSub i1 i2              -> emptyTheory  -- Stub: process substitution
  InstRest i1 i2             -> emptyTheory  -- Stub: process remainder
  InstGCD i1 i2              -> emptyTheory  -- Stub: process gcd
  InstPar i1 i2              -> emptyTheory  -- Stub: process parallel instance
