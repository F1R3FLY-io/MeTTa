//! # Quantum Gillespie Simulation
//!
//! Implements Gillespie-style simulation using **continuous-time Markov chains**
//! (CTMCs) with complex-valued transition amplitudes, enabling quantum model
//! checking of MeTTaIL programs.
//!
//! ## Theory
//!
//! When rate map values are complex amplitudes `z_i` with `|z_i|² ∈ [0, 1]`,
//! the rewrite system defines a quantum stochastic process:
//!
//! - The **state space** is the set of terms reachable via rewrites.
//! - The **generator matrix** `Q` has complex entries: `Q_{ij} = z_{ij}`
//!   where `z_{ij}` is the amplitude for transitioning from state `i` to `j`.
//! - The **density matrix** `ρ(t) = e^{Qt} ρ(0) e^{Q†t}` evolves the
//!   quantum state.
//! - **Measurement** collapses to a classical distribution via `|z|²`.
//!
//! ## Relation to the stochastic π-machine
//!
//! In the classical case (all amplitudes real), this reduces exactly to the
//! stochastic π-machine. The quantum extension adds:
//!
//! - **Interference**: amplitudes for different paths to the same state add
//!   as complex numbers, so `|z_1 + z_2|² ≠ |z_1|² + |z_2|²` in general.
//! - **Entanglement**: parallel composition of quantum processes creates
//!   entangled state spaces (tensor products of individual spaces).
//! - **Superposition**: a term can be in a superposition of rewrite
//!   outcomes, with the distribution determined by measurement.

use crate::augmented_rule::{AugmentedRewriteSystem, TermRef};
use crate::rate_map::RateMap;
use num_complex::Complex64;
use rand::Rng;
use std::collections::HashMap;

/// A quantum state: a superposition of terms weighted by complex amplitudes.
#[derive(Debug, Clone)]
pub struct QuantumState {
    /// Map from term IDs to their amplitudes in the superposition.
    pub amplitudes: HashMap<u64, (TermRef, Complex64, RateMap)>,
}

impl QuantumState {
    /// Create a pure state (single term with amplitude 1).
    pub fn pure(term: TermRef, rate_map: RateMap) -> Self {
        let id = term.id;
        let mut amplitudes = HashMap::new();
        amplitudes.insert(id, (term, Complex64::new(1.0, 0.0), rate_map));
        QuantumState { amplitudes }
    }

    /// Create a superposition from a list of (term, amplitude, rate_map) triples.
    pub fn superposition(components: Vec<(TermRef, Complex64, RateMap)>) -> Self {
        let mut amplitudes = HashMap::new();
        for (term, amp, rm) in components {
            let entry = amplitudes
                .entry(term.id)
                .or_insert_with(|| (term.clone(), Complex64::new(0.0, 0.0), rm.clone()));
            // Amplitudes for the same term interfere (add)
            entry.1 += amp;
        }
        QuantumState { amplitudes }
    }

    /// Compute the probability of measuring each term.
    /// Returns a distribution: term_id → |amplitude|².
    pub fn measurement_distribution(&self) -> Vec<(u64, &TermRef, f64)> {
        self.amplitudes
            .iter()
            .map(|(id, (term, amp, _))| (*id, term, amp.norm_sqr()))
            .filter(|(_, _, p)| *p > 1e-15)
            .collect()
    }

    /// Perform a measurement (collapse the superposition).
    /// Returns the measured term and its rate map.
    pub fn measure(&self, rng: &mut impl Rng) -> Option<(TermRef, RateMap)> {
        let dist = self.measurement_distribution();
        if dist.is_empty() {
            return None;
        }

        let total: f64 = dist.iter().map(|(_, _, p)| p).sum();
        let r: f64 = rng.gen::<f64>() * total;
        let mut cumulative = 0.0;

        for (id, _, prob) in &dist {
            cumulative += prob;
            if cumulative >= r {
                let (term, _, rm) = &self.amplitudes[id];
                return Some((term.clone(), rm.clone()));
            }
        }

        // Edge case: return last
        let last_id = dist.last().unwrap().0;
        let (term, _, rm) = &self.amplitudes[&last_id];
        Some((term.clone(), rm.clone()))
    }

    /// Total probability (should be ≤ 1, = 1 for normalized states).
    pub fn total_probability(&self) -> f64 {
        self.amplitudes.values().map(|(_, amp, _)| amp.norm_sqr()).sum()
    }

    /// Normalize the quantum state so total probability = 1.
    pub fn normalize(&mut self) {
        let total = self.total_probability();
        if total > 1e-15 {
            let factor = 1.0 / total.sqrt();
            for (_, amp, _) in self.amplitudes.values_mut() {
                *amp *= factor;
            }
        }
    }

    /// Number of terms in the superposition.
    pub fn dimension(&self) -> usize {
        self.amplitudes.len()
    }
}

/// A row of the generator matrix for the quantum CTMC.
#[derive(Debug, Clone)]
pub struct GeneratorRow {
    /// Transitions from this state: (target_term_id, amplitude).
    pub transitions: Vec<(u64, Complex64)>,
    /// Diagonal entry: negative sum of off-diagonal |z|² values.
    pub diagonal: Complex64,
}

/// The generator matrix Q for the quantum CTMC.
///
/// Q_{ij} = amplitude for transitioning from state i to state j.
/// Q_{ii} = -Σ_{j≠i} |Q_{ij}|² (ensures probability conservation).
#[derive(Debug, Clone)]
pub struct GeneratorMatrix {
    /// Map from term_id → row of transitions.
    pub rows: HashMap<u64, GeneratorRow>,
}

impl GeneratorMatrix {
    /// Build the generator matrix from a rewrite system and a set of
    /// reachable states.
    pub fn from_system(
        system: &AugmentedRewriteSystem,
        states: &HashMap<u64, TermRef>,
    ) -> Self {
        let mut rows = HashMap::new();

        for (from_id, from_term) in states {
            let mut transitions = Vec::new();
            let matching = system.matching_rules(from_term);

            for rule in matching {
                // Each spatial behavior entry contributes a transition amplitude
                for (_, rv) in rule.lhs_rate_map.entries() {
                    let amp = rv.as_complex();
                    let to_id = rule.rhs.term.id;
                    transitions.push((to_id, amp));
                }
            }

            // Diagonal: -Σ off-diagonal |z|²
            let off_diag_sum: f64 = transitions.iter().map(|(_, z)| z.norm_sqr()).sum();
            let diagonal = Complex64::new(-off_diag_sum, 0.0);

            rows.insert(
                *from_id,
                GeneratorRow {
                    transitions,
                    diagonal,
                },
            );
        }

        GeneratorMatrix { rows }
    }

    /// Compute the transition probability matrix for a small time step dt
    /// using first-order approximation: P(dt) ≈ I + Q·dt
    pub fn transition_matrix_first_order(
        &self,
        dt: f64,
    ) -> HashMap<u64, Vec<(u64, Complex64)>> {
        let mut result = HashMap::new();

        for (from_id, row) in &self.rows {
            let mut transitions = Vec::new();

            // Off-diagonal entries: Q_{ij} * dt
            for (to_id, amp) in &row.transitions {
                transitions.push((*to_id, amp * dt));
            }

            // Diagonal entry: 1 + Q_{ii} * dt
            let self_amp = Complex64::new(1.0, 0.0) + row.diagonal * dt;
            transitions.push((*from_id, self_amp));

            result.insert(*from_id, transitions);
        }

        result
    }
}

/// The result of one step of the quantum Gillespie algorithm.
#[derive(Debug, Clone)]
pub struct QuantumStep {
    /// The time at which this step occurs.
    pub time: f64,
    /// The waiting time.
    pub tau: f64,
    /// The quantum state after this step (before measurement).
    pub state: QuantumState,
    /// If a measurement was performed, the collapsed result.
    pub measured: Option<(TermRef, RateMap)>,
    /// The rule that fired (if deterministic selection occurred).
    pub rule_name: Option<String>,
}

/// Quantum Gillespie simulator for MeTTaIL rewrite systems.
///
/// This simulator evolves a quantum state through the CTMC defined by
/// the augmented rewrite system, with periodic measurements to collapse
/// the superposition for observation.
pub struct QuantumGillespie {
    /// The current simulation time.
    pub time: f64,
    /// The current quantum state.
    pub state: QuantumState,
    /// The rewrite system.
    pub system: AugmentedRewriteSystem,
    /// Random number generator.
    rng: rand::rngs::ThreadRng,
    /// Time step for CTMC evolution (smaller = more accurate).
    pub dt: f64,
    /// Whether to measure (collapse) after each step.
    pub measure_each_step: bool,
}

impl QuantumGillespie {
    /// Create a new quantum Gillespie simulator.
    pub fn new(
        initial_term: TermRef,
        initial_rate_map: RateMap,
        system: AugmentedRewriteSystem,
    ) -> Self {
        QuantumGillespie {
            time: 0.0,
            state: QuantumState::pure(initial_term, initial_rate_map),
            system,
            rng: rand::thread_rng(),
            dt: 0.01,
            measure_each_step: false,
        }
    }

    /// Set the time step for CTMC evolution.
    pub fn with_dt(mut self, dt: f64) -> Self {
        self.dt = dt;
        self
    }

    /// Set whether to measure after each step.
    pub fn with_measurement(mut self, measure: bool) -> Self {
        self.measure_each_step = measure;
        self
    }

    /// Evolve the quantum state by one time step using the CTMC.
    ///
    /// For each component |ψ_i⟩ in the superposition, apply all matching
    /// rules' amplitudes to produce new superposition components.
    pub fn step(&mut self) -> Option<QuantumStep> {
        if self.state.amplitudes.is_empty() {
            return None;
        }

        // Sample waiting time using total "rate" (sum of |z|² for all transitions)
        let total_rate: f64 = self
            .state
            .amplitudes
            .values()
            .map(|(term, amp, _)| {
                let matching = self.system.matching_rules(term);
                let rule_rate: f64 = matching
                    .iter()
                    .map(|r| r.total_propensity())
                    .sum();
                amp.norm_sqr() * rule_rate
            })
            .sum();

        if total_rate < 1e-15 {
            return None;
        }

        let r1: f64 = self.rng.gen();
        let tau = (1.0 / total_rate) * (1.0 / r1).ln();

        // Evolve: for each current state component, apply all matching rules
        let mut new_components: Vec<(TermRef, Complex64, RateMap)> = Vec::new();

        for (_, (term, amp, rm)) in &self.state.amplitudes {
            let matching = self.system.matching_rules(term);

            if matching.is_empty() {
                // No rules match — this component persists unchanged
                new_components.push((term.clone(), *amp, rm.clone()));
            } else {
                // For each matching rule, each spatial behavior entry produces
                // a transition with the composed amplitude.
                for rule in &matching {
                    for (_, rv) in rule.lhs_rate_map.entries() {
                        let transition_amp = rv.as_complex();
                        let new_amp = amp * transition_amp;
                        if new_amp.norm_sqr() > 1e-15 {
                            new_components.push((
                                rule.rhs.term.clone(),
                                new_amp,
                                rule.rhs.rate_map.clone(),
                            ));
                        }
                    }
                }

                // The component that doesn't transition (remains in current state)
                // with amplitude proportional to (1 - transition probability)
                let transition_prob: f64 = matching
                    .iter()
                    .flat_map(|r| r.lhs_rate_map.entries().iter())
                    .map(|(_, rv)| rv.probability())
                    .sum::<f64>()
                    .min(1.0);
                let remain_amp = amp * Complex64::new((1.0 - transition_prob).sqrt(), 0.0);
                if remain_amp.norm_sqr() > 1e-15 {
                    new_components.push((term.clone(), remain_amp, rm.clone()));
                }
            }
        }

        // Build new quantum state with interference
        let mut new_state = QuantumState::superposition(new_components);
        new_state.normalize();

        self.time += tau;

        // Optionally measure
        let measured = if self.measure_each_step {
            new_state.measure(&mut self.rng)
        } else {
            None
        };

        // If measured, collapse to the measured state
        if let Some((ref mterm, ref mrm)) = measured {
            new_state = QuantumState::pure(mterm.clone(), mrm.clone());
        }

        let step = QuantumStep {
            time: self.time,
            tau,
            state: new_state.clone(),
            measured,
            rule_name: None,
        };

        self.state = new_state;
        Some(step)
    }

    /// Run the simulator for a given number of steps.
    pub fn run(&mut self, max_steps: usize) -> Vec<QuantumStep> {
        let mut trace = Vec::new();
        for _ in 0..max_steps {
            match self.step() {
                Some(step) => trace.push(step),
                None => break,
            }
        }
        trace
    }

    /// Sample the current state by measurement.
    pub fn sample(&mut self) -> Option<(TermRef, RateMap)> {
        self.state.measure(&mut self.rng)
    }

    /// Get the current measurement distribution without collapsing.
    pub fn distribution(&self) -> Vec<(u64, &TermRef, f64)> {
        self.state.measurement_distribution()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::augmented_rule::AugmentedRewriteRule;

    fn make_quantum_system() -> (TermRef, RateMap, AugmentedRewriteSystem) {
        let initial_term = TermRef::new(1, "Proc", "x?(y).P | x!(Q)");
        let initial_map = RateMap::new();

        let s = 1.0 / 2.0_f64.sqrt(); // 1/√2

        let mut system = AugmentedRewriteSystem::new();

        // Rule with complex amplitudes — creates superposition
        let mut lhs_map = RateMap::new();
        lhs_map.insert(
            SpatialBehavior::interaction("x", "x"),
            RateValue::complex(s, 0.0).unwrap(), // amplitude 1/√2
        );

        let mut rhs_map = RateMap::new();
        rhs_map.insert(
            SpatialBehavior::local("x"),
            RateValue::complex(s, 0.0).unwrap(),
        );

        system.add_rule(AugmentedRewriteRule::new(
            "QUANTUM_COMM",
            TermRef::new(0, "Proc", "x?(y).P | x!(Q)"),
            lhs_map,
            TermRef::new(2, "Proc", "P{Q/y}"),
            rhs_map,
        ));

        (initial_term, initial_map, system)
    }

    #[test]
    fn test_quantum_state_pure() {
        let state = QuantumState::pure(
            TermRef::new(1, "Proc", "test"),
            RateMap::new(),
        );
        assert!((state.total_probability() - 1.0).abs() < 1e-10);
        assert_eq!(state.dimension(), 1);
    }

    #[test]
    fn test_quantum_interference() {
        // Two paths to the same state should interfere
        let term = TermRef::new(1, "Proc", "P");
        let s = 1.0 / 2.0_f64.sqrt();

        let state = QuantumState::superposition(vec![
            (term.clone(), Complex64::new(s, 0.0), RateMap::new()),
            (term.clone(), Complex64::new(s, 0.0), RateMap::new()),
        ]);

        // Constructive interference: (1/√2 + 1/√2)² = (√2)² = 2
        // But this exceeds 1, so after normalization...
        // The key point is amplitudes add, not probabilities.
        let amp = state.amplitudes[&1].1;
        assert!((amp.re - 2.0_f64.sqrt()).abs() < 1e-10);
    }

    #[test]
    fn test_quantum_destructive_interference() {
        let term = TermRef::new(1, "Proc", "P");
        let s = 1.0 / 2.0_f64.sqrt();

        let state = QuantumState::superposition(vec![
            (term.clone(), Complex64::new(s, 0.0), RateMap::new()),
            (term.clone(), Complex64::new(-s, 0.0), RateMap::new()),
        ]);

        // Destructive interference: (1/√2 - 1/√2) = 0
        let amp = state.amplitudes[&1].1;
        assert!(amp.norm_sqr() < 1e-10);
    }

    #[test]
    fn test_quantum_step() {
        let (term, rate_map, system) = make_quantum_system();
        let mut sim = QuantumGillespie::new(term, rate_map, system);
        let step = sim.step();
        assert!(step.is_some());
        let step = step.unwrap();
        assert!(step.time > 0.0);
    }
}
