//! # Language Extension: Augmented Rewrite Syntax
//!
//! This module documents and provides helpers for extending the `language!`
//! macro in MeTTaIL to support augmented rewrite rules with rate maps.
//!
//! ## Proposed Syntax Extension
//!
//! The existing `language!` macro supports:
//!
//! ```text
//! rewrites {
//!     (PPar {(PInput n ^x.p), (POutput n q), ...rest})
//!         ~> (PPar {(subst ^x.p (NQuote q)), ...rest});
//! }
//! ```
//!
//! We extend this with `where` (LHS rate map) and `producing` (RHS rate map)
//! clauses:
//!
//! ```text
//! rewrites {
//!     // Classical stochastic COMM rule
//!     (PPar {(PInput n ^x.p), (POutput n q), ...rest})
//!         ~> (PPar {(subst ^x.p (NQuote q)), ...rest})
//!         where {
//!             comm(n, n) => 0.5,
//!             local(n) => 0.3,
//!         }
//!         producing {
//!             local(n) => 0.5,
//!         };
//!
//!     // Quantum COMM rule (complex amplitudes)
//!     (PPar {(PInput n ^x.p), (POutput n q), ...rest})
//!         ~> (PPar {(subst ^x.p (NQuote q)), ...rest})
//!         where {
//!             comm(n, n) => (0.707, 0.0),    // 1/√2
//!             local(n) => (0.0, 0.707),       // i/√2
//!         }
//!         producing {
//!             local(n) => (0.5, 0.5),
//!         };
//!
//!     // Structural rule with rates
//!     if S ~> T then (PPar {S, ...rest}) ~> (PPar {T, ...rest})
//!         where {
//!             null => 1.0,
//!         };
//!
//!     // Drop rule with no rate annotation (defaults to rate 1.0)
//!     (PDrop (NQuote P)) ~> P;
//! }
//! ```
//!
//! ## Syntax Details
//!
//! ### Rate map entries
//!
//! ```text
//! spatial_behavior => rate_value
//! ```
//!
//! Where `spatial_behavior` is one of:
//! - `null` — trivial behavior
//! - `local(channel)` — localized to a channel
//! - `comm(ch_in, ch_out)` — interaction between channels
//! - `(b1 | b2)` — parallel composition
//! - `(b1 ; b2)` — sequential composition
//! - `!b` — replicated behavior
//! - `[guard](b)` — guarded behavior
//! - `custom_tag(args...)` — user-defined
//!
//! And `rate_value` is one of:
//! - `0.5` — a real number in [0, 1]
//! - `(0.5, 0.3)` — a complex number (re, im) where |z|² ∈ [0, 1]
//!
//! ### Channel references
//!
//! Channel names in spatial behaviors can reference pattern variables from
//! the LHS of the rewrite rule. In the COMM example above, `n` refers to
//! the same `n` bound in `(PInput n ^x.p)`.
//!
//! ## Default Behavior
//!
//! Rules without `where`/`producing` clauses default to:
//! - LHS rate map: `{ null => 1.0 }` (always fires with rate 1)
//! - RHS rate map: `{}` (empty, no rates carried forward)
//!
//! This ensures backward compatibility with existing MeTTaIL programs.

use crate::augmented_rule::{AugmentedRewriteRule, TermRef};
use crate::rate_map::RateMap;
use crate::rate_value::RateValue;
use crate::spatial_behavior::SpatialBehavior;

/// Builder for constructing augmented rewrite rules with a fluent API.
///
/// This mirrors how the proc macro would construct rules during code generation.
///
/// # Example
///
/// ```rust
/// use mettail_gillespie::language_ext::RuleBuilder;
/// use mettail_gillespie::spatial_behavior::SpatialBehavior;
///
/// let rule = RuleBuilder::new("COMM")
///     .lhs(1, "Proc", "x?(y).P | x!(Q)")
///     .rhs(2, "Proc", "P{Q/y}")
///     .where_rate(SpatialBehavior::interaction("x", "x"), 0.5)
///     .producing_rate(SpatialBehavior::local("x"), 0.3)
///     .build()
///     .unwrap();
/// ```
pub struct RuleBuilder {
    name: String,
    lhs_term: Option<TermRef>,
    rhs_term: Option<TermRef>,
    lhs_rates: Vec<(SpatialBehavior, RateEntry)>,
    rhs_rates: Vec<(SpatialBehavior, RateEntry)>,
    condition: Option<String>,
}

/// A rate entry that can be either real or complex, before validation.
enum RateEntry {
    Real(f64),
    Complex(f64, f64),
}

impl RuleBuilder {
    /// Create a new rule builder with a name.
    pub fn new(name: impl Into<String>) -> Self {
        RuleBuilder {
            name: name.into(),
            lhs_term: None,
            rhs_term: None,
            lhs_rates: Vec::new(),
            rhs_rates: Vec::new(),
            condition: None,
        }
    }

    /// Set the LHS term.
    pub fn lhs(mut self, id: u64, sort: &str, display: &str) -> Self {
        self.lhs_term = Some(TermRef::new(id, sort, display));
        self
    }

    /// Set the RHS term.
    pub fn rhs(mut self, id: u64, sort: &str, display: &str) -> Self {
        self.rhs_term = Some(TermRef::new(id, sort, display));
        self
    }

    /// Add a `where` clause entry with a real rate.
    pub fn where_rate(mut self, behavior: SpatialBehavior, rate: f64) -> Self {
        self.lhs_rates.push((behavior, RateEntry::Real(rate)));
        self
    }

    /// Add a `where` clause entry with a complex amplitude.
    pub fn where_amplitude(
        mut self,
        behavior: SpatialBehavior,
        re: f64,
        im: f64,
    ) -> Self {
        self.lhs_rates
            .push((behavior, RateEntry::Complex(re, im)));
        self
    }

    /// Add a `producing` clause entry with a real rate.
    pub fn producing_rate(mut self, behavior: SpatialBehavior, rate: f64) -> Self {
        self.rhs_rates.push((behavior, RateEntry::Real(rate)));
        self
    }

    /// Add a `producing` clause entry with a complex amplitude.
    pub fn producing_amplitude(
        mut self,
        behavior: SpatialBehavior,
        re: f64,
        im: f64,
    ) -> Self {
        self.rhs_rates
            .push((behavior, RateEntry::Complex(re, im)));
        self
    }

    /// Add a condition.
    pub fn condition(mut self, cond: impl Into<String>) -> Self {
        self.condition = Some(cond.into());
        self
    }

    /// Build the augmented rewrite rule.
    pub fn build(self) -> Result<AugmentedRewriteRule, String> {
        let lhs_term = self
            .lhs_term
            .ok_or_else(|| "LHS term not set".to_string())?;
        let rhs_term = self
            .rhs_term
            .ok_or_else(|| "RHS term not set".to_string())?;

        let mut lhs_map = RateMap::new();
        for (sb, entry) in &self.lhs_rates {
            let rv = match entry {
                RateEntry::Real(r) => RateValue::real(*r).map_err(|e| e.to_string())?,
                RateEntry::Complex(re, im) => {
                    RateValue::complex(*re, *im).map_err(|e| e.to_string())?
                }
            };
            lhs_map.insert(sb.clone(), rv);
        }

        // Default: if no where clause, use { null => 1.0 }
        if lhs_map.is_empty() {
            lhs_map.insert(
                SpatialBehavior::Null,
                RateValue::real(1.0).unwrap(),
            );
        }

        let mut rhs_map = RateMap::new();
        for (sb, entry) in &self.rhs_rates {
            let rv = match entry {
                RateEntry::Real(r) => RateValue::real(*r).map_err(|e| e.to_string())?,
                RateEntry::Complex(re, im) => {
                    RateValue::complex(*re, *im).map_err(|e| e.to_string())?
                }
            };
            rhs_map.insert(sb.clone(), rv);
        }

        let mut rule = AugmentedRewriteRule::new(
            self.name, lhs_term, lhs_map, rhs_term, rhs_map,
        );
        if let Some(cond) = self.condition {
            rule = rule.with_condition(cond);
        }

        rule.validate().map_err(|errs| errs.join("; "))?;
        Ok(rule)
    }
}

/// Helper to create a default rate map (null → 1.0) for unannotated rules.
pub fn default_lhs_rate_map() -> RateMap {
    let mut rm = RateMap::new();
    rm.insert(SpatialBehavior::Null, RateValue::real(1.0).unwrap());
    rm
}

/// Helper to create an empty rate map for unannotated RHS.
pub fn default_rhs_rate_map() -> RateMap {
    RateMap::new()
}

/// Generate the code snippet that the proc macro would emit for a single
/// augmented rewrite rule. This is a reference for the macro implementation.
///
/// In the actual macro, the generated code would look like:
///
/// ```text
/// {
///     let mut __lhs_rate_map = RateMap::new();
///     __lhs_rate_map.insert(
///         SpatialBehavior::interaction(n.clone(), n.clone()),
///         RateValue::real(0.5).unwrap(),
///     );
///     let mut __rhs_rate_map = RateMap::new();
///     __rhs_rate_map.insert(
///         SpatialBehavior::local(n.clone()),
///         RateValue::real(0.3).unwrap(),
///     );
///     AugmentedRewriteRule::new(
///         "COMM",
///         lhs_term_ref,
///         __lhs_rate_map,
///         rhs_term_ref,
///         __rhs_rate_map,
///     )
/// }
/// ```
pub fn codegen_reference() -> &'static str {
    r#"
// === PROC MACRO CODE GENERATION REFERENCE ===
//
// For each rewrite rule in the language! macro with a `where`/`producing`
// clause, the proc macro should generate code similar to:
//
// 1. Parse the `where { ... }` block into (SpatialBehavior, RateValue) pairs
// 2. Parse the `producing { ... }` block similarly  
// 3. Generate an AugmentedRewriteRule constructor
//
// The key additions to the existing macro parsing (in macros/src/parse.rs):
//
// - After parsing `~>` and the RHS term, check for optional `where` keyword
// - If present, parse `{ behavior => value, ... }` entries
// - Then check for optional `producing` keyword
// - If present, parse the same structure for RHS rates
//
// The generated ascent rules should include the rate map in the relation:
//
//   relation rewrite(TermId, TermId, RateMap, RateMap);
//
// Instead of the current:
//
//   relation rewrite(TermId, TermId);
"#
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rule_builder_classical() {
        let rule = RuleBuilder::new("COMM")
            .lhs(1, "Proc", "x?(y).P | x!(Q)")
            .rhs(2, "Proc", "P{Q/y}")
            .where_rate(SpatialBehavior::interaction("x", "x"), 0.5)
            .producing_rate(SpatialBehavior::local("x"), 0.3)
            .build()
            .unwrap();

        assert_eq!(rule.name, "COMM");
        assert!(!rule.is_quantum());
        assert!((rule.total_propensity() - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_rule_builder_quantum() {
        let s = 1.0 / 2.0_f64.sqrt();
        let rule = RuleBuilder::new("Q_COMM")
            .lhs(1, "Proc", "x?(y).P | x!(Q)")
            .rhs(2, "Proc", "P{Q/y}")
            .where_amplitude(SpatialBehavior::interaction("x", "x"), s, 0.0)
            .producing_amplitude(SpatialBehavior::local("x"), s, 0.0)
            .build()
            .unwrap();

        assert_eq!(rule.name, "Q_COMM");
        assert!(rule.is_quantum());
    }

    #[test]
    fn test_default_unannotated_rule() {
        let rule = RuleBuilder::new("DROP")
            .lhs(1, "Proc", "*(@(P))")
            .rhs(2, "Proc", "P")
            // No where/producing → defaults
            .build()
            .unwrap();

        assert_eq!(rule.name, "DROP");
        // Default LHS map: { null => 1.0 }
        assert!((rule.total_propensity() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_rule_builder_with_condition() {
        let rule = RuleBuilder::new("STRUCT")
            .lhs(1, "Proc", "{S, ...rest}")
            .rhs(2, "Proc", "{T, ...rest}")
            .condition("S ~> T")
            .where_rate(SpatialBehavior::Null, 1.0)
            .build()
            .unwrap();

        assert_eq!(rule.condition, Some("S ~> T".to_string()));
    }
}
