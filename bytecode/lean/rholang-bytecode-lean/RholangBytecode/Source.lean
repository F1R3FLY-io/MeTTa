/-
  RholangBytecode.Source
  ──────────────────────
  Labeled transition system for rholang 1.2 source processes.
  This formalizes the standard operational semantics of the
  Rho calculus with the observable action label alphabet from Basic.

  F1R3FLY.io — Rholang 1.2 Bytecode Interpreter Full Abstraction
-/
import RholangBytecode.Basic

namespace RholangBytecode

/-! ### Spatial pattern matching (axiomatized)

  The spatial matcher is the core of rholang's receive semantics.
  It takes a pattern and a value/process and returns an optional
  substitution (list of bindings). -/

/-- Result of spatial pattern matching: a substitution mapping
    bound variables to values, or failure. -/
def Subst := List Val

/-- Spatial pattern match: returns `some σ` if pattern matches value,
    `none` on failure. -/
axiom spatialMatch : Pattern → Val → Option Subst

/-- Joint match across multiple channel-pattern pairs.
    All patterns must match for the continuation to fire. -/
axiom jointMatch : List (Pattern × Val) → Option Subst

/-! ### Ground expression evaluation

  Ground expressions evaluate deterministically to values.
  This is the sequential sublanguage that will become
  stack-machine code in the bytecode. -/

/-- Environment for ground expression evaluation. -/
def Env := List Val

/-- Deterministic evaluation of ground expressions. -/
axiom evalGExpr : GExpr → Env → Val

/-- Ground evaluation is total and deterministic. -/
axiom evalGExpr_deterministic :
  ∀ (e : GExpr) (ρ : Env) (v₁ v₂ : Val),
    evalGExpr e ρ = v₁ → evalGExpr e ρ = v₂ → v₁ = v₂

/-! ### RSpace state (tuple space)

  The RSpace stores channel→data mappings and channel→continuation
  mappings. We model it abstractly. -/

/-- An entry in the tuple space: either data waiting or a continuation waiting. -/
inductive TupleEntry where
  | dataWaiting    : Name → List Val → Bool → TupleEntry
  | contWaiting    : List (Name × Pattern) → Proc → Bool → TupleEntry
deriving Repr

/-- The RSpace state is a multiset of tuple entries. -/
def RSpace := List TupleEntry

/-- Empty RSpace. -/
def RSpace.empty : RSpace := []

/-! ### Source LTS

  The source labeled transition system for rholang 1.2.
  Transitions: P —α→ₛ P' with shared RSpace state. -/

/-- A source configuration is a process together with RSpace state
    and a set of known fresh names. -/
structure SourceConfig where
  proc   : Proc
  rspace : RSpace
  names  : List FreshId
deriving Repr

/-- Source transition relation.

  We define this as an inductive proposition capturing
  the standard rholang operational semantics rules. -/
inductive SourceStep : SourceConfig → Label → SourceConfig → Prop where

  /-- SEND: x!(v₁,...,vₙ) produces an output label. -/
  | send :
    ∀ (x : Name) (vs : List Proc) (persist : Bool) (σ σ' : RSpace)
      (ν : List FreshId) (vals : List Val),
    -- vs evaluate to vals under the current environment
    SourceStep
      ⟨Proc.send x vs persist, σ, ν⟩
      (Label.output x vals)
      ⟨Proc.nil, σ', ν⟩

  /-- RECV (immediate COMM): for(y<-x){P} where matching data exists. -/
  | recv_comm :
    ∀ (binds : List (Name × Pattern)) (body : Proc) (persist : Bool)
      (σ σ' : RSpace) (ν : List FreshId) (vals : List Val) (θ : Subst),
    -- Joint match succeeds, producing substitution θ
    jointMatch (binds.zip vals |>.map fun ((_, p), v) => (p, v)) = some θ →
    SourceStep
      ⟨Proc.recv binds body persist, σ, ν⟩
      (Label.input (binds.head!.1) vals)
      ⟨substProc body θ, σ', ν⟩

  /-- RECV (block): no matching data, register continuation. -/
  | recv_block :
    ∀ (binds : List (Name × Pattern)) (body : Proc) (persist : Bool)
      (σ : RSpace) (ν : List FreshId),
    SourceStep
      ⟨Proc.recv binds body persist, σ, ν⟩
      Label.tau
      ⟨Proc.nil, σ ++ [TupleEntry.contWaiting binds body persist], ν⟩

  /-- PAR: a component of P | Q steps. -/
  | par_left :
    ∀ (P P' Q : Proc) (σ σ' : RSpace) (ν ν' : List FreshId) (α : Label),
    SourceStep ⟨P, σ, ν⟩ α ⟨P', σ', ν'⟩ →
    SourceStep ⟨Proc.par P Q, σ, ν⟩ α ⟨Proc.par P' Q, σ', ν'⟩

  | par_right :
    ∀ (P Q Q' : Proc) (σ σ' : RSpace) (ν ν' : List FreshId) (α : Label),
    SourceStep ⟨Q, σ, ν⟩ α ⟨Q', σ', ν'⟩ →
    SourceStep ⟨Proc.par P Q, σ, ν⟩ α ⟨Proc.par P Q', σ', ν'⟩

  /-- COMM: synchronization between parallel components.
      This is the core Rho calculus COMM rule:
        x!(v̄) | for(ȳ <- x){P}  —τ→  P[v̄/ȳ]  -/
  | comm :
    ∀ (x : Name) (vs : List Proc) (vals : List Val)
      (binds : List (Name × Pattern)) (body : Proc)
      (σ : RSpace) (ν : List FreshId) (θ : Subst),
    jointMatch (binds.zip vals |>.map fun ((_, p), v) => (p, v)) = some θ →
    SourceStep
      ⟨Proc.par (Proc.send x vs false) (Proc.recv binds body false), σ, ν⟩
      Label.tau
      ⟨substProc body θ, σ, ν⟩

  /-- NEW: restriction generates fresh names with scope extrusion. -/
  | new_ :
    ∀ (n : Nat) (P P' : Proc) (σ σ' : RSpace) (ν : List FreshId)
      (freshIds : List FreshId) (α : Label),
    freshIds.length = n →
    (∀ fid, fid ∈ freshIds → fid ∉ ν) →
    SourceStep ⟨P, σ, ν ++ freshIds⟩ α ⟨P', σ', ν ++ freshIds⟩ →
    SourceStep
      ⟨Proc.new n P, σ, ν⟩
      (freshIds.foldr (fun fid l => Label.scope fid l) α)
      ⟨P', σ', ν ++ freshIds⟩

  /-- LET: ground expression evaluation (silent step). -/
  | letStep :
    ∀ (e : GExpr) (P : Proc) (σ : RSpace) (ν : List FreshId) (v : Val),
    evalGExpr e [] = v →
    SourceStep
      ⟨Proc.letIn e P, σ, ν⟩
      Label.tau
      ⟨substProc P [v], σ, ν⟩

  /-- MATCH: pattern match on a process. -/
  | matchStep :
    ∀ (P : Proc) (arms : List (Pattern × Proc)) (σ : RSpace) (ν : List FreshId)
      (i : Nat) (pᵢ : Pattern) (Qᵢ : Proc) (θ : Subst),
    arms.get? i = some (pᵢ, Qᵢ) →
    spatialMatch pᵢ (Val.vProc P) = some θ →
    (∀ j, j < i → ∀ pⱼ Qⱼ, arms.get? j = some (pⱼ, Qⱼ) →
      spatialMatch pⱼ (Val.vProc P) = none) →
    SourceStep
      ⟨Proc.matchP P arms, σ, ν⟩
      Label.tau
      ⟨substProc Qᵢ θ, σ, ν⟩

  /-- STRUCT: structural congruence allows rewriting before stepping. -/
  | struct :
    ∀ (P P' Q Q' : Proc) (σ σ' : RSpace) (ν ν' : List FreshId) (α : Label),
    P ≡ₛ P' →
    SourceStep ⟨P', σ, ν⟩ α ⟨Q', σ', ν'⟩ →
    Q' ≡ₛ Q →
    SourceStep ⟨P, σ, ν⟩ α ⟨Q, σ', ν'⟩

notation:40 C₁ " —[" α "]→ₛ " C₂ => SourceStep C₁ α C₂

/-! ### Reflexive transitive closure of τ-steps. -/

/-- Multi-step silent transitions. -/
inductive SourceTauStar : SourceConfig → SourceConfig → Prop where
  | refl : ∀ C, SourceTauStar C C
  | step : ∀ C₁ C₂ C₃,
    (C₁ —[Label.tau]→ₛ C₂) → SourceTauStar C₂ C₃ → SourceTauStar C₁ C₃

notation:40 C₁ " —τ*→ₛ " C₂ => SourceTauStar C₁ C₂

/-- Weak source transition: τ* · α · τ*. -/
def SourceWeakStep (C₁ : SourceConfig) (α : Label) (C₂ : SourceConfig) : Prop :=
  ∃ C₁' C₂', (C₁ —τ*→ₛ C₁') ∧ (C₁' —[α]→ₛ C₂') ∧ (C₂' —τ*→ₛ C₂)

notation:40 C₁ " =[" α "]⇒ₛ " C₂ => SourceWeakStep C₁ α C₂

end RholangBytecode
