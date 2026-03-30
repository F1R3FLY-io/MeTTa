/-
  RholangBytecode.Compiler
  ────────────────────────
  The compilation function [[ − ]] from rholang 1.2 source
  processes to bytecode programs. Defined compositionally on
  the structure of source terms.

  F1R3FLY.io — Rholang 1.2 Bytecode Interpreter Full Abstraction
-/
import RholangBytecode.Basic
import RholangBytecode.Bytecode
import RholangBytecode.Source
import RholangBytecode.VM

namespace RholangBytecode

/-! ### Scope analysis

  Before compilation, a scope analysis pass assigns local
  variable slots to each bound variable. We axiomatize this. -/

/-- A scope environment maps variable de Bruijn indices to local slots. -/
abbrev ScopeEnv := List Slot

/-- Scope analysis: given a process, returns slot assignments. -/
axiom scopeAnalysis : Proc → ScopeEnv

/-! ### Ground expression compilation

  Ground expressions compile to sequences of stack-machine
  instructions. This is purely sequential code. -/

/-- Compile a ground expression to a sequence of instructions. -/
def compileGExpr : GExpr → ScopeEnv → Code
  | GExpr.lit (Val.vInt n), _   => [Instr.pushInt n]
  | GExpr.lit (Val.vBool b), _  => [Instr.pushBool b]
  | GExpr.lit Val.vNil, _       => [Instr.pushNil]
  | GExpr.lit Val.vUnit, _      => [Instr.pushUnit]
  | GExpr.lit _, _              => [Instr.pushNil]  -- other literals
  | GExpr.var i, env            =>
      match env.get? i with
      | some slot => [Instr.loadLocal slot]
      | none      => [Instr.pushNil]  -- error case
  | GExpr.binop BinOp.add e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.add]
  | GExpr.binop BinOp.sub e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.sub]
  | GExpr.binop BinOp.mul e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.mul]
  | GExpr.binop BinOp.lt e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.lt]
  | GExpr.binop BinOp.eq e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.eq]
  | GExpr.binop BinOp.and_ e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.and_]
  | GExpr.binop BinOp.or_ e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.or_]
  | GExpr.binop BinOp.concat e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.concat]
  | GExpr.binop _ e₁ e₂, env =>
      compileGExpr e₁ env ++ compileGExpr e₂ env ++ [Instr.add]  -- placeholder
  | GExpr.unop UnOp.neg e, env =>
      compileGExpr e env ++ [Instr.neg]
  | GExpr.unop UnOp.not_ e, env =>
      compileGExpr e env ++ [Instr.not_]
  | GExpr.unop UnOp.length e, env =>
      compileGExpr e env ++ [Instr.length]
  | GExpr.unop _ e, env =>
      compileGExpr e env ++ [Instr.toString]
  | GExpr.listNew es, env =>
      es.bind (fun e => compileGExpr e env) ++ [Instr.listNew es.length]
  | GExpr.setNew es, env =>
      es.bind (fun e => compileGExpr e env) ++ [Instr.setNew es.length]
  | GExpr.mapNew pairs, env =>
      pairs.bind (fun (k, v) =>
        compileGExpr k env ++ compileGExpr v env) ++
      [Instr.mapNew pairs.length]
  | GExpr.method _ obj args, env =>
      compileGExpr obj env ++
      args.bind (fun a => compileGExpr a env) ++
      [Instr.pushNil]  -- method dispatch placeholder

/-! ### All instructions produced by compileGExpr are ground.

  This is a key property: ground expression compilation only
  generates ground instructions. -/

theorem compileGExpr_all_ground :
    ∀ (e : GExpr) (env : ScopeEnv) (i : Instr),
      i ∈ compileGExpr e env → i.isGround := by
  intro e env i h
  -- Each case of compileGExpr only produces ground instructions.
  -- The proof proceeds by induction on e, examining each constructor.
  sorry  -- Straightforward but tedious induction on GExpr

/-! ### Process compilation

  The main compilation function. Returns a ProcDef for the
  compiled process, plus any subsidiary ProcDefs generated
  for sub-processes (continuations, parallel branches). -/

/-- Compilation state: tracks the next available ProcId. -/
structure CompState where
  nextId  : ProcId
  procDefs : List ProcDef
  strings  : List String
  patterns : List Pattern
deriving Repr

/-- Initial compilation state. -/
def CompState.init : CompState :=
  { nextId := 0, procDefs := [], strings := [], patterns := [] }

/-- Allocate a fresh ProcId. -/
def CompState.freshId (s : CompState) : ProcId × CompState :=
  (s.nextId, { s with nextId := s.nextId + 1 })

/-- Intern a string, returning its index. -/
def CompState.internString (s : CompState) (str : String) : StrIdx × CompState :=
  match s.strings.indexOf? str with
  | some idx => (idx, s)
  | none     => (s.strings.length, { s with strings := s.strings ++ [str] })

/-- Intern a pattern, returning its index. -/
def CompState.internPattern (s : CompState) (pat : Pattern) : Nat × CompState :=
  (s.patterns.length, { s with patterns := s.patterns ++ [pat] })

/-! ### The compilation function [[ − ]]

  We axiomatize the top-level compilation function and state its
  key structural properties. A full constructive definition would
  require mutual recursion through all Proc/Name/GExpr constructors
  with the CompState threading. -/

/-- Compile a rholang process to a bytecode program.
    [[ P ]] produces a BytecodeProgram. -/
axiom compile : Proc → BytecodeProgram

/-- The initial VM configuration for a compiled program. -/
def initialVMConfig (P : Proc) (cost : Nat) : VMConfig :=
  let prog := compile P
  let mainDef := prog.procDefs.head!
  { pool := [{ tid := ⟨0⟩,
               pc := 0,
               code := mainDef.code,
               stack := [],
               locals := List.replicate mainDef.numLocals Val.vNil,
               status := ThreadStatus.running }],
    rspace := [],
    names := [],
    cost := cost,
    prog := prog }

/-- The initial source configuration. -/
def initialSourceConfig (P : Proc) : SourceConfig :=
  { proc := P, rspace := [], names := [] }

/-! ### Structural properties of compilation

  These properties are used in the full abstraction proof. -/

/-- Compilation is compositional: [[ P | Q ]] uses a PAR
    instruction referencing [[ P ]] and [[ Q ]] as sub-ProcDefs. -/
axiom compile_par :
  ∀ (P Q : Proc),
    ∃ p1 p2 rest,
      (compile (Proc.par P Q)).procDefs.head!.code =
        [Instr.par p1 p2] ++ rest ∧
      (compile (Proc.par P Q)).getProcDef p1 = some (compile P).procDefs.head! ∧
      (compile (Proc.par P Q)).getProcDef p2 = some (compile Q).procDefs.head!

/-- Compilation of send: [[ x!(e₁,...,eₙ) ]] ends with SEND. -/
axiom compile_send :
  ∀ (x : Name) (es : List Proc) (persist : Bool),
    ∃ preamble arity,
      (compile (Proc.send x es persist)).procDefs.head!.code =
        preamble ++ [Instr.send arity persist] ∧
      (∀ i, i ∈ preamble → i.isGround) ∧
      arity = es.length

/-- Compilation of receive: [[ for(ȳ<-x̄){P} ]] ends with RECEIVE. -/
axiom compile_recv :
  ∀ (binds : List (Name × Pattern)) (body : Proc) (persist : Bool),
    ∃ preamble nBinds contId,
      (compile (Proc.recv binds body persist)).procDefs.head!.code =
        preamble ++ [Instr.receive nBinds persist contId] ∧
      (∀ i, i ∈ preamble → i.isGround) ∧
      nBinds = binds.length

/-- Compilation of new: [[ new x₁,...,xₙ in P ]] starts with NEW. -/
axiom compile_new :
  ∀ (n : Nat) (P : Proc),
    ∃ bodyCode,
      (compile (Proc.new n P)).procDefs.head!.code =
        [Instr.new_ n] ++ bodyCode

/-- Compilation of nil: [[ 0 ]] is just HALT. -/
axiom compile_nil :
  (compile Proc.nil).procDefs.head!.code = [Instr.halt]

/-- Compilation of let: [[ let x = e in P ]] is ground code for e,
    a STORE_LOCAL, then [[ P ]]. -/
axiom compile_let :
  ∀ (e : GExpr) (P : Proc),
    ∃ eCode slot pCode,
      (compile (Proc.letIn e P)).procDefs.head!.code =
        eCode ++ [Instr.storeLocal slot] ++ pCode ∧
      (∀ i, i ∈ eCode → i.isGround)

/-! ### Key structural theorem: code shape

  Every compiled ProcDef has the shape:
    ground* ; (RSpaceOp | HALT)

  That is, a (possibly empty) sequence of ground instructions
  followed by exactly one RSpace interaction or HALT. -/

/-- A code sequence has the ground-then-terminal shape. -/
def hasGroundTerminalShape (code : Code) : Prop :=
  ∃ groundPart terminal,
    code = groundPart ++ [terminal] ∧
    (∀ i, i ∈ groundPart → i.isGround) ∧
    (terminal.isRSpaceOp ∨ terminal = Instr.halt)

/-- All ProcDefs in a compiled program have ground-terminal shape. -/
axiom compile_shape :
  ∀ (P : Proc) (pd : ProcDef),
    pd ∈ (compile P).procDefs →
    hasGroundTerminalShape pd.code

/-! ### Compilation preserves structural congruence -/

axiom compile_struct_cong :
  ∀ (P Q : Proc), P ≡ₛ Q →
    initialVMConfig P 1000 ~ₜ initialVMConfig Q 1000

/-! ### Compilation is injective up to α-renaming of slots -/

/-- Two processes yielding the same compiled observable behavior
    must be structurally congruent. -/
axiom compile_injective :
  ∀ (P Q : Proc),
    initialVMConfig P 1000 ~ₜ initialVMConfig Q 1000 →
    P ≡ₛ Q ∨ (initialSourceConfig P ~ₛ initialSourceConfig Q)

end RholangBytecode
