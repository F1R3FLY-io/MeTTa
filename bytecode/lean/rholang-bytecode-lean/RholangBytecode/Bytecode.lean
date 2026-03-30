/-
  RholangBytecode.Bytecode
  ────────────────────────
  The bytecode instruction set for rholang 1.2, formalized as
  an inductive type. This corresponds to the BNF in Section 3
  of the architecture document.

  F1R3FLY.io — Rholang 1.2 Bytecode Interpreter Full Abstraction
-/
import RholangBytecode.Basic

namespace RholangBytecode

/-- Process definition identifier (index into the ProcDef table). -/
abbrev ProcId := Nat

/-- Local variable slot index. -/
abbrev Slot := Nat

/-- Instruction offset for jumps. -/
abbrev Offset := Int

/-- String constant pool index. -/
abbrev StrIdx := Nat

/-! ### Bytecode Instructions

  The instruction set is stratified into layers matching
  the architecture document:
  - Stack manipulation
  - Arithmetic / comparison
  - Boolean / string / collection
  - Local variable access
  - Control flow
  - Name and process construction
  - RSpace interaction (terminal)
  - System / cost accounting -/

/-- A single bytecode instruction. -/
inductive Instr where
  -- Stack manipulation
  | pushInt     : Int → Instr
  | pushBool    : Bool → Instr
  | pushString  : StrIdx → Instr
  | pushUri     : StrIdx → Instr
  | pushNil     : Instr
  | pushUnit    : Instr
  | pop         : Instr
  | dup         : Instr
  | swap        : Instr
  | rot         : Instr

  -- Arithmetic (a b -- result)
  | add | sub | mul | div | mod_
  | lt | le | gt | ge | eq | neq
  | neg

  -- Boolean
  | and_ | or_ | not_

  -- String
  | concat | length | slice | toString | stringToInt

  -- Collections
  | listNew     : Nat → Instr       -- pop n, build list
  | listNth     : Instr
  | listLength  : Instr
  | listAppend  : Instr
  | listSlice   : Instr
  | setNew      : Nat → Instr
  | setAdd      : Instr
  | setContains : Instr
  | setDelete   : Instr
  | mapNew      : Nat → Instr       -- pop 2n items
  | mapGet      : Instr
  | mapSet      : Instr
  | mapContains : Instr
  | mapDelete   : Instr
  | mapKeys     : Instr

  -- Local variable access
  | loadLocal   : Slot → Instr
  | storeLocal  : Slot → Instr

  -- Control flow
  | jump        : Offset → Instr
  | jumpIf      : Offset → Instr    -- pop bool, jump if true
  | jumpUnless  : Offset → Instr
  | matchBegin  : Nat → Instr
  | matchArm    : Nat → Offset → Instr  -- pattern index, offset
  | matchEnd    : Instr
  | halt        : Instr

  -- Name / process construction
  | quote       : Instr             -- process → @process
  | deref       : Instr             -- name → *name
  | new_        : Nat → Instr       -- create n fresh names
  | bundleR     : Instr
  | bundleW     : Instr
  | bundleRW    : Instr
  | pushPat     : Nat → Instr       -- push pattern from pattern table

  -- RSpace interaction (TERMINAL instructions)
  | send        : Nat → Bool → Instr       -- arity, persistent
  | receive     : Nat → Bool → ProcId → Instr  -- nBinds, persist, contProcId
  | par         : ProcId → ProcId → Instr  -- spawn two processes
  | peek        : Nat → ProcId → Instr     -- non-destructive receive

  -- System
  | costCharge  : Nat → Instr
  | logStdout   : Instr
  | logStderr   : Instr
deriving Repr

/-! ### Instruction classification

  We classify instructions by their role. This classification
  is central to the full abstraction proof: ground instructions
  produce only τ-transitions. -/

/-- An instruction is a ground operation (stack/arith/bool/string/coll/local/control). -/
def Instr.isGround : Instr → Prop
  | .pushInt _    => True  | .pushBool _   => True
  | .pushString _ => True  | .pushUri _    => True
  | .pushNil      => True  | .pushUnit     => True
  | .pop          => True  | .dup          => True
  | .swap         => True  | .rot          => True
  | .add          => True  | .sub          => True
  | .mul          => True  | .div          => True
  | .mod_         => True  | .neg          => True
  | .lt           => True  | .le           => True
  | .gt           => True  | .ge           => True
  | .eq           => True  | .neq          => True
  | .and_         => True  | .or_          => True
  | .not_         => True
  | .concat       => True  | .length       => True
  | .slice        => True  | .toString     => True
  | .stringToInt  => True
  | .listNew _    => True  | .listNth      => True
  | .listLength   => True  | .listAppend   => True
  | .listSlice    => True
  | .setNew _     => True  | .setAdd       => True
  | .setContains  => True  | .setDelete    => True
  | .mapNew _     => True  | .mapGet       => True
  | .mapSet       => True  | .mapContains  => True
  | .mapDelete    => True  | .mapKeys      => True
  | .loadLocal _  => True  | .storeLocal _ => True
  | .jump _       => True  | .jumpIf _     => True
  | .jumpUnless _ => True
  | .matchBegin _ => True  | .matchArm _ _ => True
  | .matchEnd     => True  | .halt         => True
  | .costCharge _ => True  | .logStdout    => True
  | .logStderr    => True
  | .quote        => True  | .deref        => True
  | .new_ _       => True  -- NEW is ground in the sense of being τ-labeled
  | .bundleR      => True  | .bundleW      => True
  | .bundleRW     => True  | .pushPat _    => True
  | _             => False

/-- An instruction is an RSpace interaction (terminal). -/
def Instr.isRSpaceOp : Instr → Prop
  | .send _ _      => True
  | .receive _ _ _ => True
  | .par _ _       => True
  | .peek _ _      => True
  | _              => False

/-- Every instruction is either ground or RSpace. -/
axiom instr_classification :
  ∀ (i : Instr), i.isGround ∨ i.isRSpaceOp

/-! ### Code and ProcDef table -/

/-- A code block: a sequence of instructions. -/
abbrev Code := List Instr

/-- A process definition in the bytecode program. -/
structure ProcDef where
  procId    : ProcId
  arity     : Nat
  numLocals : Nat
  code      : Code
deriving Repr

/-- A complete bytecode program. -/
structure BytecodeProgram where
  procDefs    : List ProcDef
  stringTable : List String
  patternTable : List Pattern
deriving Repr

/-- Lookup a ProcDef by id. -/
def BytecodeProgram.getProcDef (prog : BytecodeProgram) (pid : ProcId) : Option ProcDef :=
  prog.procDefs.find? (fun pd => pd.procId == pid)

end RholangBytecode
