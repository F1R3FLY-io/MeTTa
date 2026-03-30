/-
  RholangBytecode.Bisimulation
  ────────────────────────────
  Definitions of strong and weak bisimulation for both the
  source (rholang) and target (bytecode VM) labeled transition
  systems, plus standard up-to techniques.

  F1R3FLY.io — Rholang 1.2 Bytecode Interpreter Full Abstraction
-/
import RholangBytecode.Basic
import RholangBytecode.Source
import RholangBytecode.VM

namespace RholangBytecode

/-! ### Strong bisimulation on source configurations -/

/-- A relation R on source configs is a (strong) bisimulation
    if whenever (C₁, C₂) ∈ R:
    - if C₁ —α→ C₁' then ∃ C₂', C₂ —α→ C₂' ∧ (C₁', C₂') ∈ R
    - if C₂ —α→ C₂' then ∃ C₁', C₁ —α→ C₁' ∧ (C₁', C₂') ∈ R  -/
def IsSourceBisimulation (R : SourceConfig → SourceConfig → Prop) : Prop :=
  ∀ C₁ C₂, R C₁ C₂ →
    (∀ α C₁', (C₁ —[α]→ₛ C₁') →
      ∃ C₂', (C₂ —[α]→ₛ C₂') ∧ R C₁' C₂') ∧
    (∀ α C₂', (C₂ —[α]→ₛ C₂') →
      ∃ C₁', (C₁ —[α]→ₛ C₁') ∧ R C₁' C₂')

/-- Two source configurations are bisimilar if they are related
    by some bisimulation. -/
def SourceBisimilar (C₁ C₂ : SourceConfig) : Prop :=
  ∃ R, IsSourceBisimulation R ∧ R C₁ C₂

notation:50 C₁ " ~ₛ " C₂ => SourceBisimilar C₁ C₂

/-! ### Strong bisimulation on target (VM) configurations -/

/-- A relation R on VM configs is a (strong) bisimulation. -/
def IsVMBisimulation (R : VMConfig → VMConfig → Prop) : Prop :=
  ∀ C₁ C₂, R C₁ C₂ →
    (∀ α C₁', (C₁ —[α]→ₜ C₁') →
      ∃ C₂', (C₂ —[α]→ₜ C₂') ∧ R C₁' C₂') ∧
    (∀ α C₂', (C₂ —[α]→ₜ C₂') →
      ∃ C₁', (C₁ —[α]→ₜ C₁') ∧ R C₁' C₂')

/-- Two VM configurations are bisimilar. -/
def VMBisimilar (C₁ C₂ : VMConfig) : Prop :=
  ∃ R, IsVMBisimulation R ∧ R C₁ C₂

notation:50 C₁ " ~ₜ " C₂ => VMBisimilar C₁ C₂

/-! ### Weak bisimulation

  Weak bisimulation absorbs finite τ-sequences.
  This is needed because ground computation introduces
  τ-steps in the target that have no source counterpart. -/

/-- A relation R on VM configs is a weak bisimulation. -/
def IsVMWeakBisimulation (R : VMConfig → VMConfig → Prop) : Prop :=
  ∀ C₁ C₂, R C₁ C₂ →
    (∀ α C₁', (C₁ —[α]→ₜ C₁') →
      if α = Label.tau then
        ∃ C₂', (C₂ —τ*→ₜ C₂') ∧ R C₁' C₂'
      else
        ∃ C₂', (C₂ =[α]⇒ₜ C₂') ∧ R C₁' C₂') ∧
    (∀ α C₂', (C₂ —[α]→ₜ C₂') →
      if α = Label.tau then
        ∃ C₁', (C₁ —τ*→ₜ C₁') ∧ R C₁' C₂'
      else
        ∃ C₁', (C₁ =[α]⇒ₜ C₁') ∧ R C₁' C₂')

/-- Two VM configurations are weakly bisimilar. -/
def VMWeakBisimilar (C₁ C₂ : VMConfig) : Prop :=
  ∃ R, IsVMWeakBisimulation R ∧ R C₁ C₂

notation:50 C₁ " ≈ₜ " C₂ => VMWeakBisimilar C₁ C₂

/-! ### Standard properties of bisimulation -/

/-- Source bisimilarity is reflexive. -/
theorem sourceBisim_refl : ∀ (C : SourceConfig), C ~ₛ C := by
  intro C
  exact ⟨fun a b => a = b,
    fun C₁ C₂ h => by
      subst h
      exact ⟨fun α C₁' step => ⟨C₁', step, rfl⟩,
             fun α C₂' step => ⟨C₂', step, rfl⟩⟩,
    rfl⟩

/-- Source bisimilarity is symmetric. -/
theorem sourceBisim_symm :
    ∀ (C₁ C₂ : SourceConfig), (C₁ ~ₛ C₂) → (C₂ ~ₛ C₁) := by
  intro C₁ C₂ ⟨R, hR, h12⟩
  exact ⟨fun a b => R b a,
    fun C₂' C₁' h => by
      obtain ⟨hL, hR'⟩ := hR C₁' C₂' h
      exact ⟨hR', hL⟩,
    h12⟩

/-- VM bisimilarity is reflexive. -/
theorem vmBisim_refl : ∀ (C : VMConfig), C ~ₜ C := by
  intro C
  exact ⟨fun a b => a = b,
    fun C₁ C₂ h => by
      subst h
      exact ⟨fun α C₁' step => ⟨C₁', step, rfl⟩,
             fun α C₂' step => ⟨C₂', step, rfl⟩⟩,
    rfl⟩

/-- VM bisimilarity is symmetric. -/
theorem vmBisim_symm :
    ∀ (C₁ C₂ : VMConfig), (C₁ ~ₜ C₂) → (C₂ ~ₜ C₁) := by
  intro C₁ C₂ ⟨R, hR, h12⟩
  exact ⟨fun a b => R b a,
    fun C₂' C₁' h => by
      obtain ⟨hL, hR'⟩ := hR C₁' C₂' h
      exact ⟨hR', hL⟩,
    h12⟩

/-! ### Up-to techniques (Pous/Sangiorgi)

  These are proof techniques that allow working with relations
  smaller than bisimulations. Essential for the full abstraction
  proof where we need to handle ground τ-steps. -/

/-- The reflexive, symmetric, transitive closure of a relation. -/
inductive RST (R : α → α → Prop) : α → α → Prop where
  | base : R a b → RST R a b
  | refl : RST R a a
  | symm : RST R a b → RST R b a
  | trans : RST R a b → RST R b c → RST R a c

/-- Bisimulation up to equivalence: R is a bisimulation up to ~
    if whenever (C₁, C₂) ∈ R and C₁ —α→ C₁', there exists C₂'
    such that C₂ —α→ C₂' and (C₁', C₂') ∈ (~ ∘ R ∘ ~). -/
def IsVMBisimUpTo (R : VMConfig → VMConfig → Prop) : Prop :=
  ∀ C₁ C₂, R C₁ C₂ →
    (∀ α C₁', (C₁ —[α]→ₜ C₁') →
      ∃ C₂' C₁'' C₂'',
        (C₂ —[α]→ₜ C₂') ∧
        (C₁' ~ₜ C₁'') ∧ R C₁'' C₂'' ∧ (C₂'' ~ₜ C₂')) ∧
    (∀ α C₂', (C₂ —[α]→ₜ C₂') →
      ∃ C₁' C₁'' C₂'',
        (C₁ —[α]→ₜ C₁') ∧
        (C₁' ~ₜ C₁'') ∧ R C₁'' C₂'' ∧ (C₂'' ~ₜ C₂'))

/-- Soundness of bisimulation up to equivalence:
    if R is a bisimulation up to ~, then R ⊆ ~. -/
axiom bisimUpTo_sound :
  ∀ (R : VMConfig → VMConfig → Prop),
    IsVMBisimUpTo R →
    ∀ C₁ C₂, R C₁ C₂ → (C₁ ~ₜ C₂)

/-! ### Cross-system bisimulation

  For full abstraction we need to relate source and target
  configurations. We use an encoding relation. -/

/-- An encoding relation pairs source configs with VM configs
    that are "compatible" — i.e., the VM config is the compilation
    of the source config. -/
def CrossRelation := SourceConfig → VMConfig → Prop

/-- A cross-relation is a cross-bisimulation if observable actions
    can be matched in both directions. -/
def IsCrossBisimulation (R : CrossRelation) : Prop :=
  ∀ Cs Ct, R Cs Ct →
    -- Source steps can be matched by target
    (∀ α Cs', (Cs —[α]→ₛ Cs') →
      ∃ Ct', (Ct =[α]⇒ₜ Ct') ∧ R Cs' Ct') ∧
    -- Target observable steps can be matched by source
    (∀ α Ct', α.isObservable → (Ct —[α]→ₜ Ct') →
      ∃ Cs', (Cs —[α]→ₛ Cs') ∧ R Cs' Ct') ∧
    -- Target τ-steps (ground computation) stay in the relation
    (∀ Ct', (Ct —[Label.tau]→ₜ Ct') →
      -- Either it's a ground step and R Cs Ct' still holds
      R Cs Ct' ∨
      -- Or it's a structural τ (COMM, PAR) and source can match
      ∃ Cs', (Cs —[Label.tau]→ₛ Cs') ∧ R Cs' Ct')

end RholangBytecode
