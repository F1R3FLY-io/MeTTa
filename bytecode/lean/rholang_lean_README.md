# Rholang 1.2 Bytecode Interpreter — Full Abstraction in Lean 4

**F1R3FLY.io** — *E Pluribus Sapiens*

## Overview

This Lean 4 project formalizes the full abstraction theorem for the rholang 1.2
bytecode interpreter:

```
∀ P Q : Proc,  P ~ₛ Q  ↔  ⟦P⟧ ~ₜ ⟦Q⟧
```

That is, the compilation function `⟦−⟧` from rholang source to bytecode
preserves and reflects bisimulation equivalence. Two rholang programs are
observationally equivalent if and only if their compiled bytecode
representations are observationally equivalent in the bytecode VM.

## Module Structure

| File | Contents |
|------|----------|
| `Basic.lean` | Mutual inductive types for `Val`, `Name`, `Proc`, `GExpr`, `Pattern`; the shared `Label` alphabet; structural congruence axioms |
| `Source.lean` | Source LTS (`SourceStep`), spatial pattern matching interface, ground expression evaluation, weak transitions |
| `Bytecode.lean` | `Instr` type (full bytecode BNF), instruction classification (`isGround` / `isRSpaceOp`), `ProcDef`, `BytecodeProgram` |
| `VM.lean` | VM configuration (`VMConfig`), thread state, target LTS (`VMStep`), ground normal form predicate |
| `Bisimulation.lean` | Strong and weak bisimulation for source and target; up-to techniques; cross-system bisimulation |
| `Compiler.lean` | `compileGExpr` (constructive), `compile` (axiomatized); structural properties (`compile_shape`, `compile_par`, etc.) |
| `GroundInvisibility.lean` | Key Lemma 1 (ground is τ-only, deterministic, terminating, thread-local); Key Lemma 2 (τ-absorption) |
| `FullAbstraction.lean` | Key Lemma 3 (label preservation); **Soundness**; **Completeness**; **Full Abstraction** iff-theorem; corollaries |

## Proof Architecture

The proof is structured around three key lemmas:

1. **Ground Invisibility** (`GroundInvisibility.lean`): Stack-machine computation
   consists entirely of silent (τ), deterministic, terminating, thread-local steps.

2. **τ-Absorption** (`GroundInvisibility.lean`): Ground τ-sequences are absorbed
   by weak bisimulation, so ground normalization preserves observational equivalence.

3. **Label Preservation** (`FullAbstraction.lean`): The observable labels (output,
   input, scope extrusion) produced by bytecode SEND/RECEIVE/NEW instructions
   are identical to those of the corresponding source transitions.

**Soundness** (P ~ Q ⟹ ⟦P⟧ ~ ⟦Q⟧) is proved by constructing a relation
R_T = { (⟦P⟧, ⟦Q⟧) | P ~ Q } and showing it is a bisimulation up to ~ₜ,
then applying the Pous/Sangiorgi up-to soundness principle.

**Completeness** (⟦P⟧ ~ ⟦Q⟧ ⟹ P ~ Q) is proved by constructing
R_S = { (P, Q) | ⟦P⟧ ~ ⟦Q⟧ } and showing it is a bisimulation on
the source LTS, using the injectivity of compilation to "decompile"
target transitions back to source transitions.

## Axiom Budget

The formalization axiomatizes components that would require extensive
library development. These fall into three categories:

### Functions (require constructive implementation)
- `compile` — the full compilation function
- `execGround` — single ground instruction semantics
- `groundNormalize` — reduce all threads to observable frontier
- `spatialMatch` / `jointMatch` — rholang's spatial pattern matcher
- `substProc` / `substName` — capture-avoiding substitution

### Properties (require proof)
- `compile_shape` — all ProcDefs have ground-then-terminal structure
- `compile_par/send/recv/new/nil/let` — compositional compilation
- `compile_injective` — compilation is faithful (no spurious identification)
- `bisimUpTo_sound` — Pous/Sangiorgi up-to technique

### Proof obligations (`sorry`)
- ~15 `sorry` markers in lemma proofs
- Estimated 3000–5000 lines to fully discharge

## Building

```bash
# Install Lean 4 (via elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build
cd rholang-bytecode-lean
lake build
```

## References

1. Meredith & Radestock, "Namespace Logic" (TGC 2005)
2. Meredith & Stay, "Higher Category Models of the π-Calculus" (arXiv:1504.04311)
3. Milner, "Communicating and Mobile Systems: The π-Calculus" (CUP 1999)
4. Sangiorgi, "Introduction to Bisimulation and Coinduction" (CUP 2012)
5. Pous, "Complete Lattices and Up-To Techniques" (APLAS 2007)
6. Stay & Meredith, "A Calculus for Quantum Processes" (2024)

## License

Copyright 2026 F1R3FLY.io. All rights reserved.
