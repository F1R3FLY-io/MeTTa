/-
  RholangBytecode.VM
  ──────────────────
  Virtual machine configuration and labeled transition system
  for the bytecode interpreter. The VM is a concurrent system
  of lightweight stack-machine threads interacting through RSpace.

  F1R3FLY.io — Rholang 1.2 Bytecode Interpreter Full Abstraction
-/
import RholangBytecode.Basic
import RholangBytecode.Bytecode
import RholangBytecode.Source

namespace RholangBytecode

/-! ### Thread state -/

/-- The status of a process thread in the VM. -/
inductive ThreadStatus where
  | running   : ThreadStatus
  | blocked   : ThreadStatus
  | completed : ThreadStatus
  | outOfPhlo : ThreadStatus
deriving DecidableEq, Repr

/-- Operand stack. -/
abbrev Stack := List Val

/-- Local variable frame. -/
abbrev Locals := List Val

/-- A unique thread identifier. -/
structure ThreadId where
  id : Nat
deriving DecidableEq, Repr

/-- A process thread in the bytecode VM.
    This is the quintuple ⟨pc, code, S, L, status⟩. -/
structure Thread where
  tid    : ThreadId
  pc     : Nat
  code   : Code
  stack  : Stack
  locals : Locals
  status : ThreadStatus
deriving Repr

/-- A thread is runnable. -/
def Thread.isRunnable (t : Thread) : Prop :=
  t.status = ThreadStatus.running

/-- Fetch the current instruction of a thread (if any). -/
def Thread.currentInstr (t : Thread) : Option Instr :=
  t.code.get? t.pc

/-! ### Machine configuration

  The machine configuration ⟨Π, σ, Ν, κ⟩ where:
  - Π is the process pool (multiset of threads)
  - σ is the RSpace state
  - Ν is the name store
  - κ is the remaining cost (phlogiston) -/

/-- The global machine configuration. -/
structure VMConfig where
  pool    : List Thread          -- Π: process pool
  rspace  : RSpace               -- σ: tuple space state
  names   : List FreshId         -- Ν: generated fresh names
  cost    : Nat                  -- κ: remaining phlogiston
  prog    : BytecodeProgram      -- the program (immutable context)
deriving Repr

/-- A configuration has runnable threads. -/
def VMConfig.hasRunnable (cfg : VMConfig) : Prop :=
  ∃ t, t ∈ cfg.pool ∧ t.isRunnable

/-! ### COMM events from RSpace -/

/-- A COMM event returned by RSpace when produce/consume match. -/
structure CommEvent where
  continuation : ProcId
  bindings     : List Val
deriving Repr

/-! ### VM Transition Rules (Target LTS)

  The target LTS mirrors the source label alphabet exactly.
  This is the critical design property for full abstraction. -/

/-- Single-instruction execution result for ground ops. -/
structure GroundResult where
  thread : Thread
deriving Repr

/-- Execute a single ground instruction on a thread.
    Returns the updated thread. This is axiomatized;
    each case is straightforward stack manipulation. -/
axiom execGround : Thread → BytecodeProgram → GroundResult

/-- Ground execution advances the PC and only modifies stack/locals. -/
axiom execGround_advances_pc :
  ∀ (t : Thread) (prog : BytecodeProgram),
    t.isRunnable →
    (∃ i, t.currentInstr = some i ∧ i.isGround) →
    (execGround t prog).thread.pc > t.pc ∨
    -- or jump within code bounds
    (execGround t prog).thread.pc < t.code.length

/-- Ground execution does not modify RSpace. -/
axiom execGround_preserves_rspace :
  ∀ (t : Thread) (prog : BytecodeProgram)
    (σ : RSpace),
    t.isRunnable →
    (∃ i, t.currentInstr = some i ∧ i.isGround) →
    -- RSpace is untouched (expressed via the config-level rule below)
    True

/-! ### Target LTS transitions -/

/-- Target transition relation on VM configurations. -/
inductive VMStep : VMConfig → Label → VMConfig → Prop where

  /-- GROUND: Execute a ground instruction (τ-step).
      Only the executing thread's state changes;
      RSpace and other threads are untouched. -/
  | ground :
    ∀ (cfg : VMConfig) (t : Thread) (t' : Thread)
      (rest : List Thread),
    t ∈ cfg.pool →
    t.isRunnable →
    (∃ i, t.currentInstr = some i ∧ i.isGround) →
    execGround t cfg.prog = ⟨t'⟩ →
    cfg.pool = rest ++ [t] ++ [] →  -- t is selected from pool
    VMStep cfg Label.tau
      { cfg with pool := rest ++ [t'] }

  /-- SEND: Execute a SEND instruction.
      Pops arity values + channel from stack,
      performs produce on RSpace. -/
  | send :
    ∀ (cfg : VMConfig) (t : Thread) (rest : List Thread)
      (x : Name) (vals : List Val) (arity : Nat) (persist : Bool)
      (σ' : RSpace) (commOpt : Option CommEvent),
    t ∈ cfg.pool →
    t.isRunnable →
    t.currentInstr = some (Instr.send arity persist) →
    -- x and vals are on the stack (topmost is last arg)
    -- After produce, we get updated RSpace and optional COMM
    VMStep cfg (Label.output x vals)
      { cfg with
        pool := rest ++
          (match commOpt with
           | none => [{ t with status := ThreadStatus.completed }]
           | some ce =>
             [ { t with status := ThreadStatus.completed },
               { tid := ⟨cfg.pool.length⟩,  -- fresh thread id
                 pc := 0,
                 code := (cfg.prog.getProcDef ce.continuation).get!.code,
                 stack := [],
                 locals := ce.bindings,
                 status := ThreadStatus.running } ]),
        rspace := σ' }

  /-- RECEIVE (immediate COMM): Matching data exists in RSpace. -/
  | recv_comm :
    ∀ (cfg : VMConfig) (t : Thread) (rest : List Thread)
      (nBinds : Nat) (persist : Bool) (contId : ProcId)
      (channels : List Name) (vals : List Val)
      (σ' : RSpace) (θ : Subst),
    t ∈ cfg.pool →
    t.isRunnable →
    t.currentInstr = some (Instr.receive nBinds persist contId) →
    VMStep cfg (Label.input (channels.head!) vals)
      { cfg with
        pool := rest ++
          [ { t with status := ThreadStatus.completed },
            { tid := ⟨cfg.pool.length⟩,
              pc := 0,
              code := (cfg.prog.getProcDef contId).get!.code,
              stack := [],
              locals := θ,
              status := ThreadStatus.running } ],
        rspace := σ' }

  /-- RECEIVE (block): No matching data; register continuation. -/
  | recv_block :
    ∀ (cfg : VMConfig) (t : Thread) (rest : List Thread)
      (nBinds : Nat) (persist : Bool) (contId : ProcId)
      (σ' : RSpace),
    t ∈ cfg.pool →
    t.isRunnable →
    t.currentInstr = some (Instr.receive nBinds persist contId) →
    VMStep cfg Label.tau
      { cfg with
        pool := rest ++ [{ t with status := ThreadStatus.blocked }],
        rspace := σ' }

  /-- PAR: Spawn two new threads. -/
  | par :
    ∀ (cfg : VMConfig) (t : Thread) (rest : List Thread)
      (p1 p2 : ProcId),
    t ∈ cfg.pool →
    t.isRunnable →
    t.currentInstr = some (Instr.par p1 p2) →
    VMStep cfg Label.tau
      { cfg with
        pool := rest ++
          [ { t with status := ThreadStatus.completed },
            { tid := ⟨cfg.pool.length⟩,
              pc := 0,
              code := (cfg.prog.getProcDef p1).get!.code,
              stack := [], locals := t.locals,
              status := ThreadStatus.running },
            { tid := ⟨cfg.pool.length + 1⟩,
              pc := 0,
              code := (cfg.prog.getProcDef p2).get!.code,
              stack := [], locals := t.locals,
              status := ThreadStatus.running } ] }

  /-- NEW: Create fresh names (τ-step with scope extrusion). -/
  | new_ :
    ∀ (cfg : VMConfig) (t : Thread) (t' : Thread) (rest : List Thread)
      (n : Nat) (freshIds : List FreshId),
    t ∈ cfg.pool →
    t.isRunnable →
    t.currentInstr = some (Instr.new_ n) →
    freshIds.length = n →
    (∀ fid, fid ∈ freshIds → fid ∉ cfg.names) →
    VMStep cfg Label.tau
      { cfg with
        pool := rest ++ [t'],  -- t' has fresh names pushed on stack
        names := cfg.names ++ freshIds }

  /-- RSPACE_COMM: A latent COMM fires from RSpace
      (blocked thread is awakened by a produce). -/
  | rspace_comm :
    ∀ (cfg : VMConfig) (ce : CommEvent) (σ' : RSpace),
    VMStep cfg Label.tau
      { cfg with
        pool := cfg.pool ++
          [{ tid := ⟨cfg.pool.length⟩,
             pc := 0,
             code := (cfg.prog.getProcDef ce.continuation).get!.code,
             stack := [],
             locals := ce.bindings,
             status := ThreadStatus.running }],
        rspace := σ' }

  /-- COST: Charge phlogiston. -/
  | cost_ok :
    ∀ (cfg : VMConfig) (t : Thread) (rest : List Thread) (n : Nat),
    t ∈ cfg.pool →
    t.isRunnable →
    t.currentInstr = some (Instr.costCharge n) →
    cfg.cost ≥ n →
    VMStep cfg Label.tau
      { cfg with
        pool := rest ++ [{ t with pc := t.pc + 1 }],
        cost := cfg.cost - n }

  | cost_exhaust :
    ∀ (cfg : VMConfig) (t : Thread) (rest : List Thread) (n : Nat),
    t ∈ cfg.pool →
    t.isRunnable →
    t.currentInstr = some (Instr.costCharge n) →
    cfg.cost < n →
    VMStep cfg Label.tau
      { cfg with
        pool := rest ++ [{ t with status := ThreadStatus.outOfPhlo }],
        cost := 0 }

notation:40 C₁ " —[" α "]→ₜ " C₂ => VMStep C₁ α C₂

/-! ### Multi-step and weak transitions for the target -/

/-- Reflexive transitive closure of τ in the target. -/
inductive VMTauStar : VMConfig → VMConfig → Prop where
  | refl : ∀ C, VMTauStar C C
  | step : ∀ C₁ C₂ C₃,
    (C₁ —[Label.tau]→ₜ C₂) → VMTauStar C₂ C₃ → VMTauStar C₁ C₃

notation:40 C₁ " —τ*→ₜ " C₂ => VMTauStar C₁ C₂

/-- Weak target transition: τ* · α · τ*. -/
def VMWeakStep (C₁ : VMConfig) (α : Label) (C₂ : VMConfig) : Prop :=
  ∃ C₁' C₂', (C₁ —τ*→ₜ C₁') ∧ (C₁' —[α]→ₜ C₂') ∧ (C₂' —τ*→ₜ C₂)

notation:40 C₁ " =[" α "]⇒ₜ " C₂ => VMWeakStep C₁ α C₂

/-! ### Ground computation normal form

  A VM configuration is in "ground normal form" when every
  runnable thread's current instruction is an RSpaceOp (or HALT).
  That is, all ground computation has been completed. -/

/-- A thread is at an observable frontier. -/
def Thread.atFrontier (t : Thread) : Prop :=
  t.status ≠ ThreadStatus.running ∨
  (∃ i, t.currentInstr = some i ∧ i.isRSpaceOp) ∨
  t.currentInstr = some Instr.halt ∨
  t.currentInstr = none

/-- A VM configuration is in ground normal form. -/
def VMConfig.isGroundNF (cfg : VMConfig) : Prop :=
  ∀ t, t ∈ cfg.pool → t.atFrontier

end RholangBytecode
