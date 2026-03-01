//! # Classical Gillespie Simulation
//!
//! Implements the Stochastic Simulation Algorithm (SSA) in the style of the
//! **stochastic π-machine** (Phillips & Cardelli).
//!
//! ## Algorithm
//!
//! Given a set of augmented rewrite rules with real-valued rate maps:
//!
//! 1. **Compute propensities**: For each rule `r_i` with LHS rate map entries
//!    `{sb_j ↦ p_j}`, the propensity `a_i = Σ_j p_j` where the sum is over
//!    spatial behaviors that match the current term.
//!
//! 2. **Compute total propensity**: `a_0 = Σ_i a_i`
//!
//! 3. **Sample waiting time**: `τ = (1/a_0) * ln(1/r_1)` where `r_1 ~ U(0,1)`
//!
//! 4. **Select reaction**: Choose rule `r_μ` such that
//!    `Σ_{i<μ} a_i < r_2 * a_0 ≤ Σ_{i≤μ} a_i` where `r_2 ~ U(0,1)`
//!
//! 5. **Select spatial behavior within rule**: Within the chosen rule,
//!    select which spatial behavior entry triggered using the same
//!    cumulative distribution method.
//!
//! 6. **Apply rewrite**: Fire the rule, producing the RHS term and rate map.
//!
//! 7. **Advance time**: `t ← t + τ`
//!
//! This is Gillespie's Direct Method, extended to operate over MeTTaIL's
//! rewrite rules with spatial behavior annotations.

use crate::augmented_rule::{AugmentedRewriteSystem, TermRef};
use crate::rate_map::RateMap;
use crate::spatial_behavior::SpatialBehavior;
use rand::Rng;

/// The result of one step of the classical Gillespie algorithm.
#[derive(Debug, Clone)]
pub struct ClassicalStep {
    /// The time at which this step occurs.
    pub time: f64,
    /// The waiting time (τ) before this step.
    pub tau: f64,
    /// Index of the rule that fired.
    pub rule_index: usize,
    /// Name of the rule that fired.
    pub rule_name: String,
    /// The spatial behavior that triggered the rule.
    pub triggered_behavior: SpatialBehavior,
    /// The rate value associated with the triggered behavior.
    pub rate: f64,
    /// The resulting term.
    pub result_term: TermRef,
    /// The resulting rate map (carried forward).
    pub result_rate_map: RateMap,
}

/// Classical Gillespie simulator for MeTTaIL rewrite systems.
pub struct ClassicalGillespie {
    /// The current simulation time.
    pub time: f64,
    /// The current term being rewritten.
    pub current_term: TermRef,
    /// The current rate map associated with the term.
    pub current_rate_map: RateMap,
    /// The rewrite system.
    pub system: AugmentedRewriteSystem,
    /// Random number generator.
    rng: rand::rngs::ThreadRng,
}

impl ClassicalGillespie {
    /// Create a new classical Gillespie simulator.
    pub fn new(
        initial_term: TermRef,
        initial_rate_map: RateMap,
        system: AugmentedRewriteSystem,
    ) -> Self {
        ClassicalGillespie {
            time: 0.0,
            current_term: initial_term,
            current_rate_map: initial_rate_map,
            system,
            rng: rand::thread_rng(),
        }
    }

    /// Compute propensities for all applicable rules.
    ///
    /// Returns a vector of (rule_index, propensity) pairs.
    pub fn compute_propensities(&self) -> Vec<(usize, f64)> {
        self.system
            .rules
            .iter()
            .enumerate()
            .filter(|(_, rule)| rule.lhs_term.sort == self.current_term.sort)
            .map(|(i, rule)| {
                // The propensity of a rule is the sum of rates for all
                // spatial behaviors in its LHS map that are compatible
                // with the current term's rate map.
                let propensity = rule
                    .lhs_rate_map
                    .entries()
                    .iter()
                    .map(|(sb, rv)| {
                        // If the current term has a rate for this spatial behavior,
                        // multiply the rates (interaction probability).
                        // Otherwise use the rule's rate directly.
                        if let Some(current_rv) = self.current_rate_map.get(sb) {
                            rv.probability() * current_rv.probability()
                        } else {
                            rv.probability()
                        }
                    })
                    .sum::<f64>();
                (i, propensity)
            })
            .filter(|(_, p)| *p > 1e-15)
            .collect()
    }

    /// Execute one step of the Gillespie SSA.
    ///
    /// Returns `None` if no rules can fire (system has reached a normal form
    /// or all propensities are zero).
    pub fn step(&mut self) -> Option<ClassicalStep> {
        let propensities = self.compute_propensities();
        if propensities.is_empty() {
            return None;
        }

        // Total propensity
        let a0: f64 = propensities.iter().map(|(_, p)| p).sum();
        if a0 < 1e-15 {
            return None;
        }

        // Sample waiting time: τ = (1/a0) * ln(1/r1)
        let r1: f64 = self.rng.gen();
        let tau = (1.0 / a0) * (1.0 / r1).ln();

        // Select which rule fires: cumulative distribution
        let r2: f64 = self.rng.gen();
        let threshold = r2 * a0;
        let mut cumulative = 0.0;
        let mut selected_rule_index = propensities[0].0;
        for (idx, prop) in &propensities {
            cumulative += prop;
            if cumulative >= threshold {
                selected_rule_index = *idx;
                break;
            }
        }

        let rule = &self.system.rules[selected_rule_index];

        // Select which spatial behavior within the rule triggered
        let entries = rule.lhs_rate_map.entries();
        let rule_total: f64 = entries.iter().map(|(_, rv)| rv.probability()).sum();
        let r3: f64 = self.rng.gen();
        let sb_threshold = r3 * rule_total;
        let mut sb_cumulative = 0.0;
        let mut triggered_behavior = entries[0].0.clone();
        let mut triggered_rate = entries[0].1.probability();
        for (sb, rv) in entries {
            sb_cumulative += rv.probability();
            if sb_cumulative >= sb_threshold {
                triggered_behavior = sb.clone();
                triggered_rate = rv.probability();
                break;
            }
        }

        // Apply the rewrite
        let result_term = rule.rhs.term.clone();
        let result_rate_map = rule.rhs.rate_map.clone();

        // Advance time
        self.time += tau;

        let step = ClassicalStep {
            time: self.time,
            tau,
            rule_index: selected_rule_index,
            rule_name: rule.name.clone(),
            triggered_behavior,
            rate: triggered_rate,
            result_term: result_term.clone(),
            result_rate_map: result_rate_map.clone(),
        };

        // Update state
        self.current_term = result_term;
        self.current_rate_map = result_rate_map;

        Some(step)
    }

    /// Run the simulator for a given number of steps or until no rules can fire.
    pub fn run(&mut self, max_steps: usize) -> Vec<ClassicalStep> {
        let mut trace = Vec::new();
        for _ in 0..max_steps {
            match self.step() {
                Some(step) => trace.push(step),
                None => break,
            }
        }
        trace
    }

    /// Run until a given time limit.
    pub fn run_until(&mut self, max_time: f64) -> Vec<ClassicalStep> {
        let mut trace = Vec::new();
        loop {
            match self.step() {
                Some(step) => {
                    if step.time > max_time {
                        // Undo the time advance
                        self.time = step.time - step.tau;
                        break;
                    }
                    trace.push(step);
                }
                None => break,
            }
        }
        trace
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rate_value::RateValue;

    fn make_test_system() -> (TermRef, RateMap, AugmentedRewriteSystem) {
        // A simple two-rule system modeling a channel communication
        let initial_term = TermRef::new(1, "Proc", "x?(y).P | x!(Q)");

        let mut initial_map = RateMap::new();
        initial_map.insert(
            SpatialBehavior::interaction("x", "x"),
            RateValue::real(1.0).unwrap(),
        );

        let mut system = AugmentedRewriteSystem::new();

        // COMM rule: x?(y).P | x!(Q) ~> P{Q/y}
        let mut lhs_map = RateMap::new();
        lhs_map.insert(
            SpatialBehavior::interaction("x", "x"),
            RateValue::real(0.7).unwrap(),
        );
        let mut rhs_map = RateMap::new();
        rhs_map.insert(
            SpatialBehavior::local("x"),
            RateValue::real(0.3).unwrap(),
        );
        system.add_rule(AugmentedRewriteRule::new(
            "COMM",
            TermRef::new(0, "Proc", "x?(y).P | x!(Q)"),
            lhs_map,
            TermRef::new(2, "Proc", "P{Q/y}"),
            rhs_map,
        ));

        (initial_term, initial_map, system)
    }

    #[test]
    fn test_classical_step() {
        let (term, rate_map, system) = make_test_system();
        let mut sim = ClassicalGillespie::new(term, rate_map, system);
        let step = sim.step();
        assert!(step.is_some());
        let step = step.unwrap();
        assert!(step.time > 0.0);
        assert_eq!(step.rule_name, "COMM");
    }

    #[test]
    fn test_classical_run() {
        let (term, rate_map, system) = make_test_system();
        let mut sim = ClassicalGillespie::new(term, rate_map, system);
        let trace = sim.run(5);
        // Should fire at least once (COMM rule matches)
        assert!(!trace.is_empty());
    }
}
