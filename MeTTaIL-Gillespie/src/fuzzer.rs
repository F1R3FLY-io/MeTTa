//! # Weighted Term Fuzzer
//!
//! Generates random terms from a MeTTaIL language specification using
//! weighted type productions. Developers annotate each production in the
//! grammar with a weight, and the fuzzer uses these weights to guide
//! random term generation.
//!
//! ## Concept
//!
//! Given a language definition:
//!
//! ```text
//! language! {
//!     types { Proc, Name },
//!     terms {
//!         PZero   . |- "0" : Proc;                              // weight: 5.0
//!         PDrop   . n:Name |- "*" "(" n ")" : Proc;             // weight: 2.0
//!         POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc;  // weight: 3.0
//!         PInput  . n:Name, ^x.p:[Name -> Proc] |- ...          // weight: 3.0
//!         PPar    . ps:HashBag(Proc) |- ...                     // weight: 1.0
//!         NQuote  . p:Proc |- "@" "(" p ")" : Name;             // weight: 5.0
//!     },
//! }
//! ```
//!
//! The fuzzer can produce `k` random terms that are `n` production steps
//! away from the empty program (`PZero`).
//!
//! ## Proposed Syntax Extension
//!
//! ```text
//! terms {
//!     PZero . |- "0" : Proc                               [weight: 5.0];
//!     PDrop . n:Name |- "*" "(" n ")" : Proc              [weight: 2.0];
//!     POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc  [weight: 3.0];
//!     ...
//! }
//! ```
//!
//! Or equivalently via a separate `weights` block:
//!
//! ```text
//! weights {
//!     PZero => 5.0,
//!     PDrop => 2.0,
//!     POutput => 3.0,
//!     PInput => 3.0,
//!     PPar => 1.0,
//!     NQuote => 5.0,
//! }
//! ```
//!
//! ## Usage
//!
//! ```rust,ignore
//! use mettail_gillespie::fuzzer::*;
//!
//! let spec = LanguageSpec::new("RhoCalc")
//!     .add_type("Proc")
//!     .add_type("Name")
//!     .add_production(Production::new("PZero", "Proc").weight(5.0))
//!     .add_production(Production::new("PDrop", "Proc").child("n", "Name").weight(2.0))
//!     .add_production(Production::new("POutput", "Proc")
//!         .child("n", "Name").child("q", "Proc").weight(3.0))
//!     .add_production(Production::new("PInput", "Proc")
//!         .child("n", "Name").binder("x", "Name", "p", "Proc").weight(3.0))
//!     .add_production(Production::new("PPar", "Proc")
//!         .variadic("ps", "Proc").weight(1.0))
//!     .add_production(Production::new("NQuote", "Name")
//!         .child("p", "Proc").weight(5.0));
//!
//! let mut fuzzer = Fuzzer::new(&spec);
//! let terms = fuzzer.generate(
//!     "Proc",    // target sort
//!     5,         // n = max depth (steps from empty program)
//!     100,       // k = number of terms to generate
//! );
//! ```

use rand::distributions::WeightedIndex;
use rand::prelude::*;
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

// ─── Language Specification Types ──────────────────────────────────────────

/// A syntactic category (type) in the language.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SortName(pub String);

impl SortName {
    pub fn new(s: impl Into<String>) -> Self {
        SortName(s.into())
    }
}

impl fmt::Display for SortName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A child slot in a production — either a simple recursive child,
/// a binder (higher-order), or a variadic bag.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ChildSlot {
    /// A simple recursive child: `name : Sort`
    Simple {
        name: String,
        sort: SortName,
    },

    /// A binder (higher-order child): `^x.body : [BinderSort -> BodySort]`
    Binder {
        /// The name of the bound variable
        var_name: String,
        /// The sort of the bound variable
        var_sort: SortName,
        /// The name of the body
        body_name: String,
        /// The sort of the body (under the binder)
        body_sort: SortName,
    },

    /// A variadic child (bag/multiset): `ps : Bag(Sort)`
    /// The fuzzer generates between `min_count` and `max_count` children.
    Variadic {
        name: String,
        element_sort: SortName,
        min_count: usize,
        max_count: usize,
    },
}

impl ChildSlot {
    /// Get all sorts that need to be generated to fill this slot.
    pub fn required_sorts(&self) -> Vec<&SortName> {
        match self {
            ChildSlot::Simple { sort, .. } => vec![sort],
            ChildSlot::Binder {
                var_sort,
                body_sort,
                ..
            } => vec![var_sort, body_sort],
            ChildSlot::Variadic { element_sort, .. } => vec![element_sort],
        }
    }

    /// Name of this slot.
    pub fn name(&self) -> &str {
        match self {
            ChildSlot::Simple { name, .. } => name,
            ChildSlot::Binder { body_name, .. } => body_name,
            ChildSlot::Variadic { name, .. } => name,
        }
    }
}

/// A production (term constructor) in the language grammar.
///
/// Corresponds to a single entry in the `terms { ... }` block of the
/// `language!` macro.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Production {
    /// Name of the constructor (e.g., "PZero", "POutput", "NQuote").
    pub name: String,
    /// The sort this production produces (e.g., "Proc", "Name").
    pub result_sort: SortName,
    /// Child slots that must be filled recursively.
    pub children: Vec<ChildSlot>,
    /// The weight for fuzzing. Higher weight = more likely to be chosen.
    pub weight: f64,
    /// Display template for rendering generated terms.
    /// Uses `{child_name}` placeholders.
    /// e.g., `"{n}!({q})"` for POutput.
    pub display_template: Option<String>,
}

impl Production {
    /// Create a new production with default weight 1.0.
    pub fn new(name: impl Into<String>, result_sort: impl Into<String>) -> Self {
        Production {
            name: name.into(),
            result_sort: SortName::new(result_sort),
            children: Vec::new(),
            weight: 1.0,
            display_template: None,
        }
    }

    /// Set the weight.
    pub fn weight(mut self, w: f64) -> Self {
        self.weight = w;
        self
    }

    /// Add a simple child slot.
    pub fn child(mut self, name: impl Into<String>, sort: impl Into<String>) -> Self {
        self.children.push(ChildSlot::Simple {
            name: name.into(),
            sort: SortName::new(sort),
        });
        self
    }

    /// Add a binder (higher-order) child slot.
    pub fn binder(
        mut self,
        var_name: impl Into<String>,
        var_sort: impl Into<String>,
        body_name: impl Into<String>,
        body_sort: impl Into<String>,
    ) -> Self {
        self.children.push(ChildSlot::Binder {
            var_name: var_name.into(),
            var_sort: SortName::new(var_sort),
            body_name: body_name.into(),
            body_sort: SortName::new(body_sort),
        });
        self
    }

    /// Add a variadic (bag) child slot.
    pub fn variadic(
        mut self,
        name: impl Into<String>,
        element_sort: impl Into<String>,
    ) -> Self {
        self.children.push(ChildSlot::Variadic {
            name: name.into(),
            element_sort: SortName::new(element_sort),
            min_count: 2,
            max_count: 5,
        });
        self
    }

    /// Add a variadic child slot with explicit count bounds.
    pub fn variadic_bounded(
        mut self,
        name: impl Into<String>,
        element_sort: impl Into<String>,
        min_count: usize,
        max_count: usize,
    ) -> Self {
        self.children.push(ChildSlot::Variadic {
            name: name.into(),
            element_sort: SortName::new(element_sort),
            min_count,
            max_count,
        });
        self
    }

    /// Set the display template.
    pub fn template(mut self, t: impl Into<String>) -> Self {
        self.display_template = Some(t.into());
        self
    }

    /// Is this a nullary production (no children)?
    pub fn is_nullary(&self) -> bool {
        self.children.is_empty()
    }

    /// The "cost" of this production = 1 + sum of child costs.
    /// Nullary productions cost 1. Used for depth budgeting.
    pub fn min_depth(&self) -> usize {
        if self.is_nullary() {
            0
        } else {
            1
        }
    }
}

/// A complete language specification for fuzzing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LanguageSpec {
    /// Name of the language.
    pub name: String,
    /// The sorts (syntactic categories).
    pub sorts: Vec<SortName>,
    /// All productions, grouped by result sort for efficient lookup.
    pub productions: Vec<Production>,
}

impl LanguageSpec {
    /// Create a new language specification.
    pub fn new(name: impl Into<String>) -> Self {
        LanguageSpec {
            name: name.into(),
            sorts: Vec::new(),
            productions: Vec::new(),
        }
    }

    /// Add a sort.
    pub fn add_type(mut self, sort: impl Into<String>) -> Self {
        self.sorts.push(SortName::new(sort));
        self
    }

    /// Add a production.
    pub fn add_production(mut self, prod: Production) -> Self {
        self.productions.push(prod);
        self
    }

    /// Get all productions for a given sort.
    pub fn productions_for_sort(&self, sort: &SortName) -> Vec<&Production> {
        self.productions
            .iter()
            .filter(|p| &p.result_sort == sort)
            .collect()
    }

    /// Get all nullary (base case) productions for a sort.
    pub fn nullary_productions_for_sort(&self, sort: &SortName) -> Vec<&Production> {
        self.productions
            .iter()
            .filter(|p| &p.result_sort == sort && p.is_nullary())
            .collect()
    }

    /// Validate the spec: every sort referenced in children must exist,
    /// every sort must have at least one production, and at least one
    /// nullary production must be reachable.
    pub fn validate(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        let sort_set: std::collections::HashSet<&SortName> =
            self.sorts.iter().collect();

        // Check every sort has at least one production
        for sort in &self.sorts {
            if self.productions_for_sort(sort).is_empty() {
                errors.push(format!("Sort '{}' has no productions", sort));
            }
        }

        // Check every child references a known sort
        for prod in &self.productions {
            if !sort_set.contains(&prod.result_sort) {
                errors.push(format!(
                    "Production '{}' produces unknown sort '{}'",
                    prod.name, prod.result_sort
                ));
            }
            for child in &prod.children {
                for sort in child.required_sorts() {
                    if !sort_set.contains(sort) {
                        errors.push(format!(
                            "Production '{}' child '{}' references unknown sort '{}'",
                            prod.name,
                            child.name(),
                            sort
                        ));
                    }
                }
            }
        }

        // Check weights are positive
        for prod in &self.productions {
            if prod.weight <= 0.0 {
                errors.push(format!(
                    "Production '{}' has non-positive weight {}",
                    prod.name, prod.weight
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

// ─── Generated Terms ───────────────────────────────────────────────────────

/// A variable name generated by the fuzzer (for binders).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VarName(pub String);

impl fmt::Display for VarName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A generated term from the fuzzer.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FuzzTerm {
    /// A nullary constructor: e.g., `PZero` → `0`
    Nullary {
        production: String,
        sort: SortName,
    },

    /// A constructor applied to children.
    Apply {
        production: String,
        sort: SortName,
        children: Vec<(String, FuzzTerm)>,
    },

    /// A binder: `^x.body`
    Binder {
        var: VarName,
        var_sort: SortName,
        body: Box<FuzzTerm>,
    },

    /// A variable reference (inside a binder scope).
    Var(VarName),

    /// A bag/multiset of terms.
    Bag {
        sort: SortName,
        elements: Vec<FuzzTerm>,
    },
}

impl FuzzTerm {
    /// The sort of this term.
    pub fn sort(&self) -> &SortName {
        // Static fallback for Var which doesn't carry its own sort
        static VAR_SORT: std::sync::LazyLock<SortName> =
            std::sync::LazyLock::new(|| SortName("?".into()));

        match self {
            FuzzTerm::Nullary { sort, .. } => sort,
            FuzzTerm::Apply { sort, .. } => sort,
            FuzzTerm::Binder { body, .. } => body.sort(),
            FuzzTerm::Var(_) => &VAR_SORT,
            FuzzTerm::Bag { sort, .. } => sort,
        }
    }

    /// The depth (number of production steps) of this term.
    pub fn depth(&self) -> usize {
        match self {
            FuzzTerm::Nullary { .. } => 0,
            FuzzTerm::Apply { children, .. } => {
                1 + children
                    .iter()
                    .map(|(_, c)| c.depth())
                    .max()
                    .unwrap_or(0)
            }
            FuzzTerm::Binder { body, .. } => body.depth(),
            FuzzTerm::Var(_) => 0,
            FuzzTerm::Bag { elements, .. } => {
                elements.iter().map(|e| e.depth()).max().unwrap_or(0)
            }
        }
    }

    /// Total number of nodes in the term tree.
    pub fn size(&self) -> usize {
        match self {
            FuzzTerm::Nullary { .. } => 1,
            FuzzTerm::Apply { children, .. } => {
                1 + children.iter().map(|(_, c)| c.size()).sum::<usize>()
            }
            FuzzTerm::Binder { body, .. } => 1 + body.size(),
            FuzzTerm::Var(_) => 1,
            FuzzTerm::Bag { elements, .. } => {
                1 + elements.iter().map(|e| e.size()).sum::<usize>()
            }
        }
    }

    /// Collect all production names used in this term.
    pub fn productions_used(&self) -> Vec<&str> {
        match self {
            FuzzTerm::Nullary { production, .. } => vec![production.as_str()],
            FuzzTerm::Apply {
                production,
                children,
                ..
            } => {
                let mut prods = vec![production.as_str()];
                for (_, child) in children {
                    prods.extend(child.productions_used());
                }
                prods
            }
            FuzzTerm::Binder { body, .. } => body.productions_used(),
            FuzzTerm::Var(_) => vec![],
            FuzzTerm::Bag { elements, .. } => {
                elements.iter().flat_map(|e| e.productions_used()).collect()
            }
        }
    }
}

impl fmt::Display for FuzzTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FuzzTerm::Nullary { production, .. } => write!(f, "{}", production),
            FuzzTerm::Apply {
                production,
                children,
                ..
            } => {
                write!(f, "({}", production)?;
                for (name, child) in children {
                    write!(f, " {}={}", name, child)?;
                }
                write!(f, ")")
            }
            FuzzTerm::Binder {
                var, body, ..
            } => write!(f, "^{}.{}", var, body),
            FuzzTerm::Var(v) => write!(f, "{}", v),
            FuzzTerm::Bag { elements, .. } => {
                write!(f, "{{")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, "}}")
            }
        }
    }
}

// ─── Fuzzer ────────────────────────────────────────────────────────────────

/// Statistics about a fuzzing run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FuzzStats {
    /// Number of terms generated.
    pub count: usize,
    /// Distribution of depths.
    pub depth_distribution: HashMap<usize, usize>,
    /// Distribution of sizes.
    pub size_distribution: HashMap<usize, usize>,
    /// Distribution of productions used.
    pub production_distribution: HashMap<String, usize>,
    /// Min/max/mean depth.
    pub min_depth: usize,
    pub max_depth: usize,
    pub mean_depth: f64,
    /// Min/max/mean size.
    pub min_size: usize,
    pub max_size: usize,
    pub mean_size: f64,
}

/// Configuration for the fuzzer.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FuzzerConfig {
    /// Maximum depth (production steps from the empty program).
    pub max_depth: usize,
    /// Number of terms to generate.
    pub count: usize,
    /// Target sort to generate.
    pub target_sort: SortName,
    /// Probability of choosing a variable reference when in scope.
    /// Only relevant inside binders. Default: 0.3.
    pub var_ref_probability: f64,
    /// Depth decay factor: at each level, non-nullary weights are multiplied
    /// by this factor. Encourages termination. Default: 0.8.
    pub depth_decay: f64,
    /// Minimum elements in variadic slots. Default: 2.
    pub variadic_min: usize,
    /// Maximum elements in variadic slots. Default: 5.
    pub variadic_max: usize,
}

impl Default for FuzzerConfig {
    fn default() -> Self {
        FuzzerConfig {
            max_depth: 5,
            count: 10,
            target_sort: SortName::new("Proc"),
            var_ref_probability: 0.3,
            depth_decay: 0.8,
            variadic_min: 2,
            variadic_max: 5,
        }
    }
}

/// The weighted term fuzzer.
///
/// Generates random terms from a `LanguageSpec` by walking the grammar
/// top-down, choosing productions weighted by their annotations, and
/// recursively filling child slots up to a depth bound.
pub struct Fuzzer<'a> {
    spec: &'a LanguageSpec,
    config: FuzzerConfig,
    rng: rand::rngs::ThreadRng,
    /// Fresh variable counter for generating unique binder names.
    var_counter: u64,
}

impl<'a> Fuzzer<'a> {
    /// Create a new fuzzer with default configuration.
    pub fn new(spec: &'a LanguageSpec) -> Self {
        Fuzzer {
            spec,
            config: FuzzerConfig::default(),
            rng: rand::thread_rng(),
            var_counter: 0,
        }
    }

    /// Create a fuzzer with custom configuration.
    pub fn with_config(spec: &'a LanguageSpec, config: FuzzerConfig) -> Self {
        Fuzzer {
            spec,
            config,
            rng: rand::thread_rng(),
            var_counter: 0,
        }
    }

    /// Generate a fresh variable name.
    fn fresh_var(&mut self, sort: &SortName) -> VarName {
        self.var_counter += 1;
        VarName(format!(
            "{}{}",
            sort.0.to_lowercase().chars().next().unwrap_or('x'),
            self.var_counter
        ))
    }

    /// Generate a single random term of the given sort.
    ///
    /// `remaining_depth` is the number of production steps still allowed.
    /// `scope` is the set of variables currently in scope (from enclosing binders).
    fn generate_term(
        &mut self,
        sort: &SortName,
        remaining_depth: usize,
        scope: &[(VarName, SortName)],
    ) -> FuzzTerm {
        // If we have variables of the right sort in scope, maybe use one
        if !scope.is_empty() {
            let matching_vars: Vec<&(VarName, SortName)> = scope
                .iter()
                .filter(|(_, s)| s == sort)
                .collect();
            if !matching_vars.is_empty() {
                let r: f64 = self.rng.gen();
                if r < self.config.var_ref_probability {
                    let idx = self.rng.gen_range(0..matching_vars.len());
                    return FuzzTerm::Var(matching_vars[idx].0.clone());
                }
            }
        }

        // Get candidate productions
        let candidates = self.spec.productions_for_sort(sort);
        if candidates.is_empty() {
            // Fallback: return a nullary placeholder
            return FuzzTerm::Nullary {
                production: format!("?{}", sort),
                sort: sort.clone(),
            };
        }

        // At depth 0, we must choose nullary productions (if available)
        let (eligible, weights): (Vec<&Production>, Vec<f64>) = if remaining_depth == 0 {
            let nullary: Vec<&Production> = candidates
                .iter()
                .filter(|p| p.is_nullary())
                .copied()
                .collect();
            if nullary.is_empty() {
                // No nullary productions — force the lightest non-nullary
                // This handles mutual recursion where base cases aren't always available
                let ws: Vec<f64> = candidates.iter().map(|p| p.weight).collect();
                (candidates, ws)
            } else {
                let ws: Vec<f64> = nullary.iter().map(|p| p.weight).collect();
                (nullary, ws)
            }
        } else {
            // Apply depth decay to non-nullary productions
            let decay = self.config.depth_decay.powi(
                (self.config.max_depth - remaining_depth) as i32,
            );
            let ws: Vec<f64> = candidates
                .iter()
                .map(|p| {
                    if p.is_nullary() {
                        p.weight
                    } else {
                        p.weight * decay
                    }
                })
                .collect();
            (candidates, ws)
        };

        // Weighted selection
        let dist = match WeightedIndex::new(&weights) {
            Ok(d) => d,
            Err(_) => {
                // All weights zero — pick uniformly
                return FuzzTerm::Nullary {
                    production: eligible[0].name.clone(),
                    sort: sort.clone(),
                };
            }
        };
        let chosen = eligible[dist.sample(&mut self.rng)];

        // Generate the term
        if chosen.is_nullary() {
            FuzzTerm::Nullary {
                production: chosen.name.clone(),
                sort: sort.clone(),
            }
        } else {
            let mut children = Vec::new();
            for slot in &chosen.children {
                match slot {
                    ChildSlot::Simple { name, sort: child_sort } => {
                        let child_term = self.generate_term(
                            child_sort,
                            remaining_depth - 1,
                            scope,
                        );
                        children.push((name.clone(), child_term));
                    }
                    ChildSlot::Binder {
                        var_name: _,
                        var_sort,
                        body_name,
                        body_sort,
                    } => {
                        let var = self.fresh_var(var_sort);
                        let mut new_scope = scope.to_vec();
                        new_scope.push((var.clone(), var_sort.clone()));
                        let body = self.generate_term(
                            body_sort,
                            remaining_depth - 1,
                            &new_scope,
                        );
                        let binder_term = FuzzTerm::Binder {
                            var,
                            var_sort: var_sort.clone(),
                            body: Box::new(body),
                        };
                        children.push((body_name.clone(), binder_term));
                    }
                    ChildSlot::Variadic {
                        name,
                        element_sort,
                        min_count,
                        max_count,
                    } => {
                        let min = (*min_count).max(self.config.variadic_min);
                        let max = (*max_count).min(self.config.variadic_max);
                        let count = self.rng.gen_range(min..=max);
                        let elements: Vec<FuzzTerm> = (0..count)
                            .map(|_| {
                                self.generate_term(
                                    element_sort,
                                    remaining_depth - 1,
                                    scope,
                                )
                            })
                            .collect();
                        let bag_term = FuzzTerm::Bag {
                            sort: element_sort.clone(),
                            elements,
                        };
                        children.push((name.clone(), bag_term));
                    }
                }
            }
            FuzzTerm::Apply {
                production: chosen.name.clone(),
                sort: sort.clone(),
                children,
            }
        }
    }

    /// Generate `k` random terms of the target sort, each at most `n` steps
    /// from the empty program.
    pub fn generate(
        &mut self,
        target_sort: impl Into<String>,
        max_depth: usize,
        count: usize,
    ) -> Vec<FuzzTerm> {
        let sort = SortName::new(target_sort);
        self.config.max_depth = max_depth;
        (0..count)
            .map(|_| self.generate_term(&sort, max_depth, &[]))
            .collect()
    }

    /// Generate terms and return both the terms and statistics.
    pub fn generate_with_stats(
        &mut self,
        target_sort: impl Into<String>,
        max_depth: usize,
        count: usize,
    ) -> (Vec<FuzzTerm>, FuzzStats) {
        let terms = self.generate(target_sort, max_depth, count);
        let stats = compute_stats(&terms);
        (terms, stats)
    }
}

/// Compute statistics over a set of generated terms.
pub fn compute_stats(terms: &[FuzzTerm]) -> FuzzStats {
    let mut depth_dist: HashMap<usize, usize> = HashMap::new();
    let mut size_dist: HashMap<usize, usize> = HashMap::new();
    let mut prod_dist: HashMap<String, usize> = HashMap::new();

    let mut depths = Vec::new();
    let mut sizes = Vec::new();

    for term in terms {
        let d = term.depth();
        let s = term.size();
        depths.push(d);
        sizes.push(s);
        *depth_dist.entry(d).or_insert(0) += 1;
        *size_dist.entry(s).or_insert(0) += 1;
        for prod in term.productions_used() {
            *prod_dist.entry(prod.to_string()).or_insert(0) += 1;
        }
    }

    let min_depth = depths.iter().copied().min().unwrap_or(0);
    let max_depth = depths.iter().copied().max().unwrap_or(0);
    let mean_depth = if depths.is_empty() {
        0.0
    } else {
        depths.iter().sum::<usize>() as f64 / depths.len() as f64
    };

    let min_size = sizes.iter().copied().min().unwrap_or(0);
    let max_size = sizes.iter().copied().max().unwrap_or(0);
    let mean_size = if sizes.is_empty() {
        0.0
    } else {
        sizes.iter().sum::<usize>() as f64 / sizes.len() as f64
    };

    FuzzStats {
        count: terms.len(),
        depth_distribution: depth_dist,
        size_distribution: size_dist,
        production_distribution: prod_dist,
        min_depth,
        max_depth,
        mean_depth,
        min_size,
        max_size,
        mean_size,
    }
}

// ─── Integration Helper: Connecting Fuzzed Terms to the Simulator ──────────

/// Convert a fuzzed term into a `TermRef` for use with the Gillespie simulator.
///
/// This bridges the fuzzer output to the simulation input, allowing
/// developers to generate random programs and then simulate them.
pub fn fuzz_term_to_term_ref(
    term: &FuzzTerm,
    id: u64,
) -> crate::augmented_rule::TermRef {
    crate::augmented_rule::TermRef::new(
        id,
        term.sort().0.clone(),
        term.to_string(),
    )
}

// ─── Predefined Language Specs ──────────────────────────────────────────────

/// Create a `LanguageSpec` for the rho-calculus (as in the MeTTaIL README).
///
/// This is useful for testing and as a reference for how to define specs.
pub fn rhocalc_spec() -> LanguageSpec {
    LanguageSpec::new("RhoCalc")
        .add_type("Proc")
        .add_type("Name")
        // PZero: base case for Proc
        .add_production(
            Production::new("PZero", "Proc")
                .weight(5.0)
                .template("0"),
        )
        // PDrop: *(@n) : Proc — dereference
        .add_production(
            Production::new("PDrop", "Proc")
                .child("n", "Name")
                .weight(2.0)
                .template("*({n})"),
        )
        // POutput: n!(q) : Proc — send
        .add_production(
            Production::new("POutput", "Proc")
                .child("n", "Name")
                .child("q", "Proc")
                .weight(3.0)
                .template("{n}!({q})"),
        )
        // PInput: n?(^x.p) : Proc — receive with binder
        .add_production(
            Production::new("PInput", "Proc")
                .child("n", "Name")
                .binder("x", "Name", "p", "Proc")
                .weight(3.0)
                .template("{n}?{p}"),
        )
        // PPar: {ps} : Proc — parallel composition
        .add_production(
            Production::new("PPar", "Proc")
                .variadic("ps", "Proc")
                .weight(1.0)
                .template("{{{ps}}}"),
        )
        // NQuote: @(p) : Name — quote a process into a name
        .add_production(
            Production::new("NQuote", "Name")
                .child("p", "Proc")
                .weight(5.0)
                .template("@({p})"),
        )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rhocalc_spec_valid() {
        let spec = rhocalc_spec();
        assert!(spec.validate().is_ok());
    }

    #[test]
    fn test_generate_terms() {
        let spec = rhocalc_spec();
        let mut fuzzer = Fuzzer::new(&spec);
        let terms = fuzzer.generate("Proc", 3, 20);
        assert_eq!(terms.len(), 20);
        for term in &terms {
            assert!(term.depth() <= 5); // may exceed slightly due to variadic
        }
    }

    #[test]
    fn test_generate_depth_zero() {
        let spec = rhocalc_spec();
        let mut fuzzer = Fuzzer::new(&spec);
        let terms = fuzzer.generate("Proc", 0, 10);
        // All should be PZero (the only nullary Proc production)
        for term in &terms {
            assert_eq!(term.depth(), 0);
            if let FuzzTerm::Nullary { production, .. } = term {
                assert_eq!(production, "PZero");
            } else {
                panic!("Expected nullary at depth 0");
            }
        }
    }

    #[test]
    fn test_stats() {
        let spec = rhocalc_spec();
        let mut fuzzer = Fuzzer::new(&spec);
        let (terms, stats) = fuzzer.generate_with_stats("Proc", 4, 50);
        assert_eq!(stats.count, 50);
        assert!(stats.min_depth <= stats.max_depth);
        assert!(stats.min_size <= stats.max_size);
        assert!(!stats.production_distribution.is_empty());
    }

    #[test]
    fn test_custom_weights() {
        // Create a spec where POutput is heavily weighted
        let spec = LanguageSpec::new("Test")
            .add_type("Proc")
            .add_type("Name")
            .add_production(Production::new("PZero", "Proc").weight(1.0))
            .add_production(
                Production::new("POutput", "Proc")
                    .child("n", "Name")
                    .child("q", "Proc")
                    .weight(100.0), // very high weight
            )
            .add_production(
                Production::new("NQuote", "Name")
                    .child("p", "Proc")
                    .weight(1.0),
            );

        let mut fuzzer = Fuzzer::new(&spec);
        let (_, stats) = fuzzer.generate_with_stats("Proc", 3, 100);

        // POutput should be the most-used non-nullary production
        let poutput_count = stats
            .production_distribution
            .get("POutput")
            .copied()
            .unwrap_or(0);
        assert!(
            poutput_count > 0,
            "POutput should appear with weight 100.0"
        );
    }

    #[test]
    fn test_binder_scope() {
        let spec = rhocalc_spec();
        let config = FuzzerConfig {
            max_depth: 4,
            count: 100,
            target_sort: SortName::new("Proc"),
            var_ref_probability: 0.9, // very high — should use vars when available
            depth_decay: 0.5,
            variadic_min: 2,
            variadic_max: 3,
        };
        let mut fuzzer = Fuzzer::with_config(&spec, config);
        let terms = fuzzer.generate("Proc", 4, 50);
        // Just verify they all generate without panicking
        assert_eq!(terms.len(), 50);
    }

    #[test]
    fn test_term_display() {
        let term = FuzzTerm::Apply {
            production: "POutput".into(),
            sort: SortName::new("Proc"),
            children: vec![
                (
                    "n".into(),
                    FuzzTerm::Apply {
                        production: "NQuote".into(),
                        sort: SortName::new("Name"),
                        children: vec![(
                            "p".into(),
                            FuzzTerm::Nullary {
                                production: "PZero".into(),
                                sort: SortName::new("Proc"),
                            },
                        )],
                    },
                ),
                (
                    "q".into(),
                    FuzzTerm::Nullary {
                        production: "PZero".into(),
                        sort: SortName::new("Proc"),
                    },
                ),
            ],
        };
        let s = term.to_string();
        assert!(s.contains("POutput"));
        assert!(s.contains("NQuote"));
        assert!(s.contains("PZero"));
    }

    #[test]
    fn test_fuzz_to_term_ref() {
        let term = FuzzTerm::Nullary {
            production: "PZero".into(),
            sort: SortName::new("Proc"),
        };
        let tr = fuzz_term_to_term_ref(&term, 42);
        assert_eq!(tr.id, 42);
        assert_eq!(tr.sort, "Proc");
    }
}
