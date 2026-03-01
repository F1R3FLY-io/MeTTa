//! # Unified Simulator Interface
//!
//! Provides a single `Simulator` type that dispatches between classical
//! (stochastic π-machine) and quantum (CTMC) Gillespie simulation based
//! on whether the rate maps contain real or complex values.

use crate::augmented_rule::{AugmentedRewriteSystem, TermRef};
use crate::gillespie::{ClassicalGillespie, ClassicalStep};
use crate::quantum::{QuantumGillespie, QuantumStep};
use crate::rate_map::{MapMode, RateMap};
use serde::{Deserialize, Serialize};
use std::fmt;

/// The simulation mode, determined by the rate value types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SimulatorMode {
    /// Real-valued rates → stochastic π-machine style SSA.
    Classical,
    /// Complex-valued amplitudes → quantum CTMC model checking.
    Quantum,
}

/// A single step in a simulation trace (unified over both modes).
#[derive(Debug, Clone)]
pub enum SimulationStep {
    Classical(ClassicalStep),
    Quantum(QuantumStep),
}

impl SimulationStep {
    pub fn time(&self) -> f64 {
        match self {
            SimulationStep::Classical(s) => s.time,
            SimulationStep::Quantum(s) => s.time,
        }
    }

    pub fn tau(&self) -> f64 {
        match self {
            SimulationStep::Classical(s) => s.tau,
            SimulationStep::Quantum(s) => s.tau,
        }
    }
}

impl fmt::Display for SimulationStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SimulationStep::Classical(s) => {
                write!(
                    f,
                    "t={:.6}: [{}] {} via {} (rate={:.4}) → {}",
                    s.time, s.rule_name, s.triggered_behavior, s.rule_name, s.rate, s.result_term
                )
            }
            SimulationStep::Quantum(s) => {
                let dim = s.state.dimension();
                let total_p = s.state.total_probability();
                write!(
                    f,
                    "t={:.6}: superposition dim={}, total_p={:.6}",
                    s.time, dim, total_p
                )?;
                if let Some((ref term, _)) = s.measured {
                    write!(f, " → measured: {}", term)?;
                }
                Ok(())
            }
        }
    }
}

/// A complete simulation trace.
#[derive(Debug, Clone)]
pub struct SimulationTrace {
    pub mode: SimulatorMode,
    pub steps: Vec<SimulationStep>,
    pub initial_term: TermRef,
}

impl SimulationTrace {
    /// Total simulation time.
    pub fn total_time(&self) -> f64 {
        self.steps.last().map(|s| s.time()).unwrap_or(0.0)
    }

    /// Number of steps.
    pub fn num_steps(&self) -> usize {
        self.steps.len()
    }

    /// Display a summary of the trace.
    pub fn summary(&self) -> String {
        format!(
            "SimulationTrace(mode={:?}, steps={}, time={:.6}, initial={})",
            self.mode,
            self.num_steps(),
            self.total_time(),
            self.initial_term,
        )
    }
}

/// Unified simulator that dispatches between classical and quantum modes.
pub enum Simulator {
    Classical(ClassicalGillespie),
    Quantum(QuantumGillespie),
}

impl Simulator {
    /// Create a simulator, auto-detecting the mode from the rewrite system.
    ///
    /// If any rule has complex-valued rates, the quantum simulator is used.
    /// Otherwise, the classical simulator is used.
    pub fn new(
        initial_term: TermRef,
        initial_rate_map: RateMap,
        system: AugmentedRewriteSystem,
    ) -> Self {
        let mode = detect_mode(&system);
        match mode {
            SimulatorMode::Classical => Simulator::Classical(ClassicalGillespie::new(
                initial_term,
                initial_rate_map,
                system,
            )),
            SimulatorMode::Quantum => Simulator::Quantum(QuantumGillespie::new(
                initial_term,
                initial_rate_map,
                system,
            )),
        }
    }

    /// Force a specific simulation mode.
    pub fn with_mode(
        initial_term: TermRef,
        initial_rate_map: RateMap,
        system: AugmentedRewriteSystem,
        mode: SimulatorMode,
    ) -> Self {
        match mode {
            SimulatorMode::Classical => Simulator::Classical(ClassicalGillespie::new(
                initial_term,
                initial_rate_map,
                system,
            )),
            SimulatorMode::Quantum => Simulator::Quantum(QuantumGillespie::new(
                initial_term,
                initial_rate_map,
                system,
            )),
        }
    }

    /// Get the current simulation mode.
    pub fn mode(&self) -> SimulatorMode {
        match self {
            Simulator::Classical(_) => SimulatorMode::Classical,
            Simulator::Quantum(_) => SimulatorMode::Quantum,
        }
    }

    /// Execute one step.
    pub fn step(&mut self) -> Option<SimulationStep> {
        match self {
            Simulator::Classical(sim) => sim.step().map(SimulationStep::Classical),
            Simulator::Quantum(sim) => sim.step().map(SimulationStep::Quantum),
        }
    }

    /// Run for up to `max_steps` steps.
    pub fn run(&mut self, max_steps: usize) -> SimulationTrace {
        let (mode, initial) = match self {
            Simulator::Classical(sim) => {
                (SimulatorMode::Classical, sim.current_term.clone())
            }
            Simulator::Quantum(sim) => {
                let term = sim
                    .state
                    .amplitudes
                    .values()
                    .next()
                    .map(|(t, _, _)| t.clone())
                    .unwrap_or_else(|| TermRef::new(0, "?", "?"));
                (SimulatorMode::Quantum, term)
            }
        };

        let mut steps = Vec::new();
        for _ in 0..max_steps {
            match self.step() {
                Some(step) => steps.push(step),
                None => break,
            }
        }

        SimulationTrace {
            mode,
            steps,
            initial_term: initial,
        }
    }

    /// Run until a time limit.
    pub fn run_until(&mut self, max_time: f64, max_steps: usize) -> SimulationTrace {
        let (mode, initial) = match self {
            Simulator::Classical(sim) => {
                (SimulatorMode::Classical, sim.current_term.clone())
            }
            Simulator::Quantum(sim) => {
                let term = sim
                    .state
                    .amplitudes
                    .values()
                    .next()
                    .map(|(t, _, _)| t.clone())
                    .unwrap_or_else(|| TermRef::new(0, "?", "?"));
                (SimulatorMode::Quantum, term)
            }
        };

        let mut steps = Vec::new();
        for _ in 0..max_steps {
            match self.step() {
                Some(step) => {
                    if step.time() > max_time {
                        break;
                    }
                    steps.push(step);
                }
                None => break,
            }
        }

        SimulationTrace {
            mode,
            steps,
            initial_term: initial,
        }
    }

    /// Current simulation time.
    pub fn time(&self) -> f64 {
        match self {
            Simulator::Classical(sim) => sim.time,
            Simulator::Quantum(sim) => sim.time,
        }
    }
}

/// Detect the simulation mode from a rewrite system.
fn detect_mode(system: &AugmentedRewriteSystem) -> SimulatorMode {
    for rule in &system.rules {
        if let Some(MapMode::Quantum) = rule.lhs_rate_map.mode() {
            return SimulatorMode::Quantum;
        }
        if let Some(MapMode::Quantum) = rule.rhs.rate_map.mode() {
            return SimulatorMode::Quantum;
        }
    }
    SimulatorMode::Classical
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::augmented_rule::AugmentedRewriteRule;
    use crate::rate_value::RateValue;
    use crate::spatial_behavior::SpatialBehavior;

    #[test]
    fn test_auto_detect_classical() {
        let mut system = AugmentedRewriteSystem::new();
        let mut lhs = RateMap::new();
        lhs.insert(SpatialBehavior::local("x"), RateValue::real(0.5).unwrap());
        system.add_rule(AugmentedRewriteRule::new(
            "test",
            TermRef::new(1, "P", "A"),
            lhs,
            TermRef::new(2, "P", "B"),
            RateMap::new(),
        ));

        let sim = Simulator::new(
            TermRef::new(1, "P", "A"),
            RateMap::new(),
            system,
        );
        assert_eq!(sim.mode(), SimulatorMode::Classical);
    }

    #[test]
    fn test_auto_detect_quantum() {
        let mut system = AugmentedRewriteSystem::new();
        let s = 1.0 / 2.0_f64.sqrt();
        let mut lhs = RateMap::new();
        lhs.insert(
            SpatialBehavior::local("x"),
            RateValue::complex(s, 0.0).unwrap(),
        );
        system.add_rule(AugmentedRewriteRule::new(
            "test",
            TermRef::new(1, "P", "A"),
            lhs,
            TermRef::new(2, "P", "B"),
            RateMap::new(),
        ));

        let sim = Simulator::new(
            TermRef::new(1, "P", "A"),
            RateMap::new(),
            system,
        );
        assert_eq!(sim.mode(), SimulatorMode::Quantum);
    }

    #[test]
    fn test_unified_run() {
        let mut system = AugmentedRewriteSystem::new();
        let mut lhs = RateMap::new();
        lhs.insert(SpatialBehavior::local("x"), RateValue::real(0.5).unwrap());
        let mut rhs = RateMap::new();
        rhs.insert(SpatialBehavior::local("x"), RateValue::real(0.3).unwrap());
        system.add_rule(AugmentedRewriteRule::new(
            "test",
            TermRef::new(1, "P", "A"),
            lhs,
            TermRef::new(2, "P", "B"),
            rhs,
        ));

        let mut sim = Simulator::new(
            TermRef::new(1, "P", "A"),
            RateMap::new(),
            system,
        );
        let trace = sim.run(10);
        assert!(!trace.steps.is_empty());
        assert_eq!(trace.mode, SimulatorMode::Classical);
    }
}
