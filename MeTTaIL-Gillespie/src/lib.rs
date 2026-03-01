//! # MeTTaIL Gillespie Extensions
//!
//! This crate extends MeTTaIL's rewrite rule system with **rate maps** that
//! associate spatial behavior terms (refining the type on the LHS of a rule)
//! with either:
//!
//! - **Real probabilities** in `[0, 1]` — producing a classical Gillespie
//!   simulator in the style of the stochastic π-machine.
//! - **Complex amplitudes** where `|z|² ∈ [0, 1]` — producing a quantum
//!   Gillespie simulator built from continuous-time Markov chains for quantum
//!   model checking.
//!
//! ## Architecture
//!
//! The extension layers on top of MeTTaIL's existing `language!` macro:
//!
//! ```text
//! ┌──────────────────────────────────────────────────────┐
//! │  language! { ... rewrites { ... } }                  │  ← existing
//! ├──────────────────────────────────────────────────────┤
//! │  AugmentedRewriteRule                                │
//! │    LHS: term + RateMap<SpatialBehavior, RateValue>   │  ← this crate
//! │    RHS: term + RateMap<SpatialBehavior, RateValue>   │
//! ├──────────────────────────────────────────────────────┤
//! │  GillespieSimulator                                  │
//! │    ClassicalMode  (real rates, SSA)                   │  ← this crate
//! │    QuantumMode    (complex amplitudes, CTMC)          │
//! └──────────────────────────────────────────────────────┘
//! ```

pub mod rate_value;
pub mod spatial_behavior;
pub mod rate_map;
pub mod augmented_rule;
pub mod gillespie;
pub mod quantum;
pub mod simulator;
pub mod language_ext;
pub mod fuzzer;

// Re-exports for convenient use
pub use rate_value::RateValue;
pub use spatial_behavior::SpatialBehavior;
pub use rate_map::RateMap;
pub use augmented_rule::{AugmentedRewriteRule, AugmentedRhs};
pub use simulator::{Simulator, SimulatorMode, SimulationStep, SimulationTrace};
