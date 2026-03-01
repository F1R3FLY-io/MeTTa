//! # Rate Maps
//!
//! A `RateMap` is a map from `SpatialBehavior` keys to `RateValue` values.
//! It augments the left-hand side (and is produced on the right-hand side)
//! of a rewrite rule.
//!
//! ## Semantics
//!
//! On the **LHS** of a rule, a rate map constrains *when* the rule can fire
//! and with what probability/amplitude. Each entry says: "if the spatial
//! context matches this behavior, the rate for this rule firing is this value."
//!
//! On the **RHS** of a rule, a rate map describes the rates that the resulting
//! term carries forward — enabling cascading stochastic/quantum behavior.
//!
//! ## Normalization
//!
//! For classical (real) mode, the map's values must sum to at most 1.
//! For quantum (complex) mode, the sum of |z_i|² must be at most 1.
//! The `normalize` method enforces this.

use crate::rate_value::{RateValue, RateValueError};
use crate::spatial_behavior::SpatialBehavior;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use thiserror::Error;

/// Errors arising from rate map operations.
#[derive(Debug, Error)]
pub enum RateMapError {
    #[error("Rate value error: {0}")]
    RateValue(#[from] RateValueError),

    #[error("Total probability {0} exceeds 1.0 (real mode)")]
    ProbabilityOverflow(f64),

    #[error("Total |z|² = {0} exceeds 1.0 (quantum mode)")]
    AmplitudeOverflow(f64),

    #[error("Mixed real and complex rates in the same map")]
    MixedModes,

    #[error("Empty rate map")]
    EmptyMap,
}

/// A map from spatial behavior terms to rate values.
///
/// This is the core data structure that augments rewrite rules.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateMap {
    entries: Vec<(SpatialBehavior, RateValue)>,
}

impl RateMap {
    /// Create an empty rate map.
    pub fn new() -> Self {
        RateMap {
            entries: Vec::new(),
        }
    }

    /// Create a rate map from a list of (behavior, value) pairs.
    pub fn from_entries(entries: Vec<(SpatialBehavior, RateValue)>) -> Self {
        RateMap { entries }
    }

    /// Insert a spatial behavior with its rate.
    pub fn insert(&mut self, behavior: SpatialBehavior, rate: RateValue) {
        // If the behavior already exists, update it
        if let Some(entry) = self.entries.iter_mut().find(|(b, _)| b == &behavior) {
            entry.1 = rate;
        } else {
            self.entries.push((behavior, rate));
        }
    }

    /// Look up the rate for a given spatial behavior.
    pub fn get(&self, behavior: &SpatialBehavior) -> Option<&RateValue> {
        self.entries
            .iter()
            .find(|(b, _)| b == behavior)
            .map(|(_, v)| v)
    }

    /// Return all entries as a slice.
    pub fn entries(&self) -> &[(SpatialBehavior, RateValue)] {
        &self.entries
    }

    /// Number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Is the map empty?
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Determine whether this map is in real (classical) or complex (quantum) mode.
    pub fn mode(&self) -> Option<MapMode> {
        if self.entries.is_empty() {
            return None;
        }
        let has_real = self.entries.iter().any(|(_, v)| v.is_real());
        let has_complex = self.entries.iter().any(|(_, v)| v.is_complex());
        match (has_real, has_complex) {
            (true, false) => Some(MapMode::Classical),
            (false, true) => Some(MapMode::Quantum),
            (true, true) => Some(MapMode::Mixed), // will cause error on validate
            (false, false) => None,
        }
    }

    /// Total probability mass: sum of p_i for real, sum of |z_i|² for complex.
    pub fn total_probability(&self) -> f64 {
        self.entries.iter().map(|(_, v)| v.probability()).sum()
    }

    /// Validate that the map is well-formed:
    /// - No mixed modes
    /// - Total probability ≤ 1
    pub fn validate(&self) -> Result<(), RateMapError> {
        if self.entries.is_empty() {
            return Ok(()); // empty maps are trivially valid
        }

        if let Some(MapMode::Mixed) = self.mode() {
            return Err(RateMapError::MixedModes);
        }

        let total = self.total_probability();
        if total > 1.0 + 1e-10 {
            match self.mode() {
                Some(MapMode::Classical) => {
                    return Err(RateMapError::ProbabilityOverflow(total))
                }
                Some(MapMode::Quantum) => return Err(RateMapError::AmplitudeOverflow(total)),
                _ => {}
            }
        }

        Ok(())
    }

    /// Normalize the map so total probability sums to exactly 1.
    /// Returns the normalization factor applied.
    pub fn normalize(&mut self) -> Result<f64, RateMapError> {
        if self.entries.is_empty() {
            return Err(RateMapError::EmptyMap);
        }
        self.validate()?;

        let total = self.total_probability();
        if total < 1e-15 {
            return Err(RateMapError::EmptyMap);
        }

        match self.mode() {
            Some(MapMode::Classical) => {
                for entry in &mut self.entries {
                    if let RateValue::Real(r) = &mut entry.1 {
                        *r /= total;
                    }
                }
            }
            Some(MapMode::Quantum) => {
                // Normalize amplitudes so Σ|z_i|² = 1
                let norm_factor = total.sqrt();
                for entry in &mut self.entries {
                    if let RateValue::Complex(z) = &mut entry.1 {
                        *z /= norm_factor;
                    }
                }
            }
            _ => {}
        }
        Ok(total)
    }

    /// Select a behavior according to the rate map (for classical mode).
    /// Returns the index of the selected behavior.
    /// Uses the Gillespie SSA selection: generate uniform random in [0, total),
    /// then walk the cumulative distribution.
    pub fn select_classical(&self, uniform_sample: f64) -> Option<usize> {
        let total = self.total_probability();
        if total < 1e-15 {
            return None;
        }
        let threshold = uniform_sample * total;
        let mut cumulative = 0.0;
        for (i, (_, v)) in self.entries.iter().enumerate() {
            cumulative += v.probability();
            if cumulative >= threshold {
                return Some(i);
            }
        }
        // Floating point edge case — return last
        Some(self.entries.len() - 1)
    }

    /// Compose two rate maps (e.g., for sequential rule application).
    /// Matching behaviors have their rates composed (multiplied).
    /// Non-matching behaviors are dropped.
    pub fn compose(&self, other: &RateMap) -> Result<RateMap, RateMapError> {
        let mut result = RateMap::new();
        for (sb1, rv1) in &self.entries {
            if let Some(rv2) = other.get(sb1) {
                let composed = rv1.compose(rv2)?;
                result.insert(sb1.clone(), composed);
            }
        }
        Ok(result)
    }

    /// Merge two rate maps (e.g., for parallel composition).
    /// Matching behaviors have their rates added.
    /// Non-matching behaviors are kept with their original rates.
    pub fn merge(&self, other: &RateMap) -> RateMap {
        let mut result = self.clone();
        for (sb, rv) in &other.entries {
            if let Some(existing) = result
                .entries
                .iter_mut()
                .find(|(b, _)| b == sb)
            {
                existing.1 = existing.1.add(rv);
            } else {
                result.entries.push((sb.clone(), *rv));
            }
        }
        result
    }

    /// Extract as a HashMap for indexed access (useful for the ascent engine).
    pub fn to_hash_map(&self) -> HashMap<SpatialBehavior, RateValue> {
        self.entries.iter().cloned().collect()
    }
}

impl Default for RateMap {
    fn default() -> Self {
        Self::new()
    }
}

/// The mode of a rate map.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapMode {
    /// All values are real — classical Gillespie / stochastic π-machine.
    Classical,
    /// All values are complex — quantum CTMC model checking.
    Quantum,
    /// Mixed (invalid for simulation).
    Mixed,
}

impl fmt::Display for RateMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (sb, rv)) in self.entries.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} ↦ {}", sb, rv)?;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rate_map_classical() {
        let mut rm = RateMap::new();
        rm.insert(
            SpatialBehavior::local("x"),
            RateValue::real(0.3).unwrap(),
        );
        rm.insert(
            SpatialBehavior::local("y"),
            RateValue::real(0.5).unwrap(),
        );
        assert!(rm.validate().is_ok());
        assert_eq!(rm.mode(), Some(MapMode::Classical));
        assert!((rm.total_probability() - 0.8).abs() < 1e-10);
    }

    #[test]
    fn test_rate_map_quantum() {
        let mut rm = RateMap::new();
        // |1/√2|² = 0.5 each, total = 1.0
        let s = 1.0 / 2.0_f64.sqrt();
        rm.insert(
            SpatialBehavior::local("x"),
            RateValue::complex(s, 0.0).unwrap(),
        );
        rm.insert(
            SpatialBehavior::local("y"),
            RateValue::complex(0.0, s).unwrap(),
        );
        assert!(rm.validate().is_ok());
        assert_eq!(rm.mode(), Some(MapMode::Quantum));
        assert!((rm.total_probability() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_mixed_mode_rejected() {
        let mut rm = RateMap::new();
        rm.insert(
            SpatialBehavior::local("x"),
            RateValue::real(0.3).unwrap(),
        );
        rm.insert(
            SpatialBehavior::local("y"),
            RateValue::complex(0.1, 0.1).unwrap(),
        );
        assert!(matches!(rm.validate(), Err(RateMapError::MixedModes)));
    }

    #[test]
    fn test_select_classical() {
        let mut rm = RateMap::new();
        rm.insert(
            SpatialBehavior::local("x"),
            RateValue::real(0.3).unwrap(),
        );
        rm.insert(
            SpatialBehavior::local("y"),
            RateValue::real(0.7).unwrap(),
        );
        // Sample near 0 should select first
        assert_eq!(rm.select_classical(0.1), Some(0));
        // Sample near 1 should select second
        assert_eq!(rm.select_classical(0.9), Some(1));
    }

    #[test]
    fn test_normalize() {
        let mut rm = RateMap::new();
        rm.insert(
            SpatialBehavior::local("x"),
            RateValue::real(0.2).unwrap(),
        );
        rm.insert(
            SpatialBehavior::local("y"),
            RateValue::real(0.3).unwrap(),
        );
        rm.normalize().unwrap();
        assert!((rm.total_probability() - 1.0).abs() < 1e-10);
    }
}
