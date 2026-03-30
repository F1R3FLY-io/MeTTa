import Lake
open Lake DSL

package rholangBytecode where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib RholangBytecode where
  srcDir := "."
  roots := #[`RholangBytecode.Basic,
             `RholangBytecode.Source,
             `RholangBytecode.Bytecode,
             `RholangBytecode.VM,
             `RholangBytecode.Bisimulation,
             `RholangBytecode.Compiler,
             `RholangBytecode.GroundInvisibility,
             `RholangBytecode.FullAbstraction]
