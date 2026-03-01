//! # Augmented Rewrite Rules
//!
//! This module defines `AugmentedRewriteRule`, which extends MeTTaIL's
//! standard rewrite rules with rate maps.
//!
//! ## Standard MeTTaIL rewrite rule (existing):
//! ```text
//! LHS_term ~> RHS_term
//! ```
//!
//! ## Augmented rewrite rule (this extension):
//! ```text
//! (LHS_term, LHS_rate_map) ~> (RHS_term, RHS_rate_map)
//! ```
//!
//! Where:
//! - **LHS_rate_map**: keys are `SpatialBehavior` terms refining the type of
//!   `LHS_term`; values are rates/amplitudes governing when this rule fires.
//! - **RHS_rate_map**: the rates carried forward by the resulting term after
//!   the rewrite, enabling cascading stochastic/quantum dynamics.
//!
//! ## Proposed `language!` macro syntax:
//!
//! ```text
//! rewrites {
//!     (PPar {(PInput n ^x.p), (POutput n q), ...rest})
//!         ~> (PPar {(subst ^x.p (NQuote q)), ...rest})
//!         where {
//!             comm(@n, @n) => 0.5,   // classical rate
//!         }
//!         producing {
//!             local(@n) => 0.5,
//!         };
//! }
//! ```

use crate::rate_map::RateMap;
use serde::{Deserialize, Serialize};
use std::fmt;

/// An abstract term representation.
///
/// In the full MeTTaIL integration, this would be parameterized over the
/// generated AST type from the `language!` macro. Here we use a generic
/// term representation that can wrap any term type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TermRef {
    /// Unique identifier for the term (e.g., from the ascent engine).
    pub id: u64,
    /// The term's type/syntactic category in the defined language.
    pub sort: String,
    /// Human-readable representation for display.
    pub display: String,
}

impl TermRef {
    pub fn new(id: u64, sort: impl Into<String>, display: impl Into<String>) -> Self {
        TermRef {
            id,
            sort: sort.into(),
            display: display.into(),
        }
    }
}

impl fmt::Display for TermRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display)
    }
}

/// The right-hand side of an augmented rewrite rule:
/// a term together with an output rate map.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AugmentedRhs {
    /// The resulting term.
    pub term: TermRef,
    /// The rate map carried forward by the resulting term.
    pub rate_map: RateMap,
}

/// An augmented rewrite rule: LHS (term + rate map) → RHS (term + rate map).
///
/// This is the central type that connects MeTTaIL's rewriting engine to
/// the Gillespie simulator.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AugmentedRewriteRule {
    /// Name/label for the rule (for debugging and traces).
    pub name: String,

    /// The left-hand side pattern term.
    pub lhs_term: TermRef,

    /// Rate map on the left-hand side.
    /// Keys are spatial behaviors refining the type of `lhs_term`.
    /// Values are rates (real) or amplitudes (complex).
    pub lhs_rate_map: RateMap,

    /// The right-hand side: term + output rate map.
    pub rhs: AugmentedRhs,

    /// Optional structural rule condition (e.g., "if S ~> T then ...").
    /// This connects to MeTTaIL's existing conditional rewrite support.
    pub condition: Option<String>,
}

impl AugmentedRewriteRule {
    /// Create a new augmented rewrite rule.
    pub fn new(
        name: impl Into<String>,
        lhs_term: TermRef,
        lhs_rate_map: RateMap,
        rhs_term: TermRef,
        rhs_rate_map: RateMap,
    ) -> Self {
        AugmentedRewriteRule {
            name: name.into(),
            lhs_term,
            lhs_rate_map,
            rhs: AugmentedRhs {
                term: rhs_term,
                rate_map: rhs_rate_map,
            },
            condition: None,
        }
    }

    /// Add a condition to the rule.
    pub fn with_condition(mut self, condition: impl Into<String>) -> Self {
        self.condition = Some(condition.into());
        self
    }

    /// Compute the total propensity (rate) for this rule firing
    /// given a particular spatial behavior context.
    pub fn propensity(
        &self,
        context: &crate::spatial_behavior::SpatialBehavior,
    ) -> f64 {
        self.lhs_rate_map
            .get(context)
            .map(|rv| rv.probability())
            .unwrap_or(0.0)
    }

    /// Compute the total propensity across all spatial behaviors
    /// in the LHS rate map.
    pub fn total_propensity(&self) -> f64 {
        self.lhs_rate_map.total_probability()
    }

    /// Check whether this rule is in classical (real) or quantum (complex) mode.
    pub fn is_quantum(&self) -> bool {
        matches!(
            self.lhs_rate_map.mode(),
            Some(crate::rate_map::MapMode::Quantum)
        )
    }

    /// Validate the rule: both LHS and RHS rate maps must be well-formed.
    pub fn validate(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        if let Err(e) = self.lhs_rate_map.validate() {
            errors.push(format!("LHS rate map: {}", e));
        }
        if let Err(e) = self.rhs.rate_map.validate() {
            errors.push(format!("RHS rate map: {}", e));
        }
        // Check mode consistency
        let lhs_mode = self.lhs_rate_map.mode();
        let rhs_mode = self.rhs.rate_map.mode();
        if let (Some(l), Some(r)) = (lhs_mode, rhs_mode) {
            if l != r {
                errors.push(format!(
                    "Mode mismatch: LHS is {:?} but RHS is {:?}",
                    l, r
                ));
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl fmt::Display for AugmentedRewriteRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: ({}, {}) ~> ({}, {})",
            self.name,
            self.lhs_term,
            self.lhs_rate_map,
            self.rhs.term,
            self.rhs.rate_map
        )?;
        if let Some(cond) = &self.condition {
            write!(f, "  [if {}]", cond)?;
        }
        Ok(())
    }
}

/// A collection of augmented rewrite rules forming a stochastic/quantum
/// rewrite system.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AugmentedRewriteSystem {
    pub rules: Vec<AugmentedRewriteRule>,
}

impl AugmentedRewriteSystem {
    pub fn new() -> Self {
        AugmentedRewriteSystem { rules: Vec::new() }
    }

    pub fn add_rule(&mut self, rule: AugmentedRewriteRule) {
        self.rules.push(rule);
    }

    /// Find all rules whose LHS pattern matches a given term (by sort).
    pub fn matching_rules(&self, term: &TermRef) -> Vec<&AugmentedRewriteRule> {
        self.rules
            .iter()
            .filter(|r| r.lhs_term.sort == term.sort)
            .collect()
    }

    /// Compute the total propensity across all rules.
    pub fn total_propensity(&self) -> f64 {
        self.rules.iter().map(|r| r.total_propensity()).sum()
    }

    /// Validate all rules in the system.
    pub fn validate(&self) -> Result<(), Vec<String>> {
        let mut all_errors = Vec::new();
        for (i, rule) in self.rules.iter().enumerate() {
            if let Err(errs) = rule.validate() {
                for e in errs {
                    all_errors.push(format!("Rule {} ({}): {}", i, rule.name, e));
                }
            }
        }
        if all_errors.is_empty() {
            Ok(())
        } else {
            Err(all_errors)
        }
    }
}

impl Default for AugmentedRewriteSystem {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rate_value::RateValue;
    use crate::spatial_behavior::SpatialBehavior;

    fn make_comm_rule() -> AugmentedRewriteRule {
        let mut lhs_map = RateMap::new();
        lhs_map.insert(
            SpatialBehavior::interaction("x", "x"),
            RateValue::real(0.5).unwrap(),
        );

        let mut rhs_map = RateMap::new();
        rhs_map.insert(
            SpatialBehavior::local("x"),
            RateValue::real(0.5).unwrap(),
        );

        AugmentedRewriteRule::new(
            "COMM",
            TermRef::new(1, "Proc", "x?(y).P | x!(Q)"),
            lhs_map,
            TermRef::new(2, "Proc", "P{Q/y}"),
            rhs_map,
        )
    }

    #[test]
    fn test_augmented_rule_creation() {
        let rule = make_comm_rule();
        assert_eq!(rule.name, "COMM");
        assert!(!rule.is_quantum());
        assert!((rule.total_propensity() - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_rule_validation() {
        let rule = make_comm_rule();
        assert!(rule.validate().is_ok());
    }

    #[test]
    fn test_rewrite_system() {
        let mut system = AugmentedRewriteSystem::new();
        system.add_rule(make_comm_rule());

        let term = TermRef::new(1, "Proc", "test");
        let matches = system.matching_rules(&term);
        assert_eq!(matches.len(), 1);
    }
}
