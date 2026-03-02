//! Automata representation for rholang synchronization trees.
//!
//! This module provides types for representing the automata extracted from
//! symbolic execution of rholang expressions. The synchronization tree of
//! a rholang process unfolds the comm events (channel sends/receives) into
//! a tree structure; this module captures the automaton derived from that tree.
//!
//! # Pipeline
//!
//! ```text
//! rholang expr → symbolic execution → sync tree → automata → triangularize → GPU
//! ```
//!
//! This module handles the `automata → triangularize` step, providing:
//! - [`CommEvent`] — labeled communication events (send, receive, tau)
//! - [`Automaton`] — states + labeled transitions extracted from a sync tree
//! - [`automaton_to_triangular`] — compile an automaton to upper triangular form
//! - [`TriangularAutomatonResult`] — the result, preserving comm event labels

use crate::{triangularize, TriangularError, TriangularResult};
use petgraph::graph::DiGraph;
use std::collections::{HashMap, HashSet};
use std::fmt;

// ---------------------------------------------------------------------------
// Rholang comm event types
// ---------------------------------------------------------------------------

/// A channel name in rholang. In production rholang, channels are names
/// (quoted processes), but for the automata representation we use string
/// identifiers that the symbolic executor resolves.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ChannelName(pub String);

impl fmt::Display for ChannelName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The data payload carried by a comm event.
/// Covers the rholang data extensions: arithmetic, booleans, strings, collections.
#[derive(Debug, Clone, PartialEq)]
pub enum RhoData {
    /// Integer value (rholang arithmetic)
    Int(i64),
    /// Boolean value
    Bool(bool),
    /// String value
    Str(String),
    /// List collection
    List(Vec<RhoData>),
    /// Set collection (represented as sorted vec for determinism)
    Set(Vec<RhoData>),
    /// Map collection (key-value pairs)
    Map(Vec<(RhoData, RhoData)>),
    /// A channel/name reference (quoted process)
    Name(ChannelName),
    /// Wildcard — pattern variable not yet bound
    Wildcard,
    /// Symbolic variable from symbolic execution (not yet resolved)
    Symbolic(String),
}

impl fmt::Display for RhoData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RhoData::Int(n) => write!(f, "{}", n),
            RhoData::Bool(b) => write!(f, "{}", b),
            RhoData::Str(s) => write!(f, "\"{}\"", s),
            RhoData::List(items) => {
                write!(f, "[")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, "]")
            }
            RhoData::Set(items) => {
                write!(f, "Set(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
            RhoData::Map(entries) => {
                write!(f, "{{")?;
                for (i, (k, v)) in entries.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, "}}")
            }
            RhoData::Name(ch) => write!(f, "@{}", ch),
            RhoData::Wildcard => write!(f, "_"),
            RhoData::Symbolic(s) => write!(f, "?{}", s),
        }
    }
}

/// A communication event in the rholang synchronization tree.
///
/// These are the observable actions (labels on transitions) that arise from
/// symbolic execution of a rholang process.
#[derive(Debug, Clone, PartialEq)]
pub enum CommEvent {
    /// A send on a channel: `channel!(data)`
    Send {
        channel: ChannelName,
        data: Vec<RhoData>,
    },
    /// A receive on a channel: `for(pattern <- channel) { ... }`
    Receive {
        channel: ChannelName,
        /// Patterns being matched (as data for the automata representation)
        patterns: Vec<RhoData>,
    },
    /// A synchronized communication (comm rule fired).
    /// This is the key event — a send and receive on the same channel
    /// have been matched by the rho calculus COMM rule.
    Comm {
        channel: ChannelName,
        data: Vec<RhoData>,
    },
    /// Internal/silent transition (tau). Arises from:
    /// - Arithmetic evaluation
    /// - Boolean reduction
    /// - String operations
    /// - Collection operations (list append, map lookup, etc.)
    /// - `new` name generation
    Tau {
        /// Optional description of what internal computation occurred
        description: Option<String>,
    },
    /// A peek (persistent receive): `for(pattern <= channel) { ... }`
    Peek {
        channel: ChannelName,
        patterns: Vec<RhoData>,
    },
}

impl fmt::Display for CommEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommEvent::Send { channel, data } => {
                write!(f, "{}!(", channel)?;
                for (i, d) in data.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", d)?;
                }
                write!(f, ")")
            }
            CommEvent::Receive { channel, patterns } => {
                write!(f, "for(")?;
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, " <- {})", channel)
            }
            CommEvent::Comm { channel, data } => {
                write!(f, "τ@{}(", channel)?;
                for (i, d) in data.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", d)?;
                }
                write!(f, ")")
            }
            CommEvent::Tau { description } => match description {
                Some(desc) => write!(f, "τ[{}]", desc),
                None => write!(f, "τ"),
            },
            CommEvent::Peek { channel, patterns } => {
                write!(f, "for(")?;
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, " <= {})", channel)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Automaton
// ---------------------------------------------------------------------------

/// Identifier for an automaton state.
pub type StateId = usize;

/// A transition in the automaton: from one state to another, labeled with a comm event.
#[derive(Debug, Clone)]
pub struct Transition {
    pub from: StateId,
    pub to: StateId,
    pub label: CommEvent,
}

/// An automaton extracted from a rholang synchronization tree.
///
/// States represent process continuations after comm events.
/// Transitions are labeled with the comm events that drive the process forward.
///
/// This is a nondeterministic finite automaton (NFA) since a rholang process
/// may have multiple possible comm events from a given state (nondeterministic
/// choice, parallel composition offering multiple interactions).
#[derive(Debug, Clone)]
pub struct Automaton {
    /// Number of states
    pub num_states: usize,
    /// The initial state (root of the synchronization tree)
    pub initial: StateId,
    /// Terminal/accepting states (processes that have completed)
    pub accepting: HashSet<StateId>,
    /// All transitions
    pub transitions: Vec<Transition>,
    /// Optional labels for states (e.g., the rholang process term at that point)
    pub state_labels: HashMap<StateId, String>,
}

impl Automaton {
    /// Create a new empty automaton with a given number of states.
    pub fn new(num_states: usize, initial: StateId) -> Self {
        Automaton {
            num_states,
            initial,
            accepting: HashSet::new(),
            transitions: Vec::new(),
            state_labels: HashMap::new(),
        }
    }

    /// Add a transition.
    pub fn add_transition(&mut self, from: StateId, to: StateId, label: CommEvent) {
        assert!(from < self.num_states, "from state out of bounds");
        assert!(to < self.num_states, "to state out of bounds");
        self.transitions.push(Transition { from, to, label });
    }

    /// Mark a state as accepting (process terminated).
    pub fn set_accepting(&mut self, state: StateId) {
        assert!(state < self.num_states, "state out of bounds");
        self.accepting.insert(state);
    }

    /// Label a state with a description (e.g., the process continuation).
    pub fn label_state(&mut self, state: StateId, label: impl Into<String>) {
        self.state_labels.insert(state, label.into());
    }

    /// Get the set of channels mentioned in all transitions.
    pub fn channels(&self) -> HashSet<&ChannelName> {
        let mut channels = HashSet::new();
        for t in &self.transitions {
            match &t.label {
                CommEvent::Send { channel, .. }
                | CommEvent::Receive { channel, .. }
                | CommEvent::Comm { channel, .. }
                | CommEvent::Peek { channel, .. } => {
                    channels.insert(channel);
                }
                CommEvent::Tau { .. } => {}
            }
        }
        channels
    }

    /// Convert this automaton into a petgraph DiGraph for triangularization.
    /// Node weights are state labels, edge weights carry the comm event index
    /// into the returned event list.
    pub fn to_digraph(&self) -> (DiGraph<String, usize>, Vec<CommEvent>) {
        let mut graph = DiGraph::new();
        let mut events: Vec<CommEvent> = Vec::new();

        // Add nodes
        let nodes: Vec<_> = (0..self.num_states)
            .map(|i| {
                let label = self
                    .state_labels
                    .get(&i)
                    .cloned()
                    .unwrap_or_else(|| format!("S{}", i));
                graph.add_node(label)
            })
            .collect();

        // Add edges
        for t in &self.transitions {
            let event_idx = events.len();
            events.push(t.label.clone());
            graph.add_edge(nodes[t.from], nodes[t.to], event_idx);
        }

        (graph, events)
    }
}

// ---------------------------------------------------------------------------
// Triangularization result with comm event labels
// ---------------------------------------------------------------------------

/// The result of triangularizing an automaton, preserving communication event labels.
#[derive(Debug, Clone)]
pub struct TriangularAutomatonResult {
    /// The underlying triangular result (matrix + groups of states).
    pub triangular: TriangularResult<String>,

    /// The comm events that label transitions.
    /// Indexed by the values stored as edge weights in the internal digraph.
    pub events: Vec<CommEvent>,

    /// Labeled transition matrix: `labeled_matrix[(i,j)]` contains the indices
    /// into `events` for all transitions from group `i` to group `j`.
    pub transition_labels: HashMap<(usize, usize), Vec<usize>>,

    /// Which groups contain accepting states.
    pub accepting_groups: HashSet<usize>,

    /// Which group contains the initial state.
    pub initial_group: usize,
}

impl TriangularAutomatonResult {
    /// Get all comm events on transitions from group `i` to group `j`.
    pub fn events_between(&self, i: usize, j: usize) -> Vec<&CommEvent> {
        self.transition_labels
            .get(&(i, j))
            .map(|indices| indices.iter().map(|&idx| &self.events[idx]).collect())
            .unwrap_or_default()
    }

    /// Get the wavefront parallel schedule.
    /// Returns groups of state-groups that can execute in parallel.
    /// Each "wave" depends only on previous waves.
    pub fn wavefront_schedule(&self) -> Vec<Vec<usize>> {
        let n = self.triangular.matrix.nrows();
        if n == 0 {
            return vec![];
        }

        // Compute in-degree for each group in the upper triangular matrix
        let mut in_degree = vec![0usize; n];
        for i in 0..n {
            for j in (i + 1)..n {
                if self.triangular.matrix[(i, j)] > 0.0 {
                    in_degree[j] += 1;
                }
            }
        }

        let mut waves = Vec::new();
        let mut remaining: HashSet<usize> = (0..n).collect();

        while !remaining.is_empty() {
            // Collect all nodes with in_degree 0 among remaining
            let wave: Vec<usize> = remaining
                .iter()
                .filter(|&&node| in_degree[node] == 0)
                .copied()
                .collect();

            if wave.is_empty() {
                // Shouldn't happen with upper triangular, but safety valve
                break;
            }

            // Remove this wave and update in-degrees
            for &node in &wave {
                remaining.remove(&node);
                for j in 0..n {
                    if self.triangular.matrix[(node, j)] > 0.0 && remaining.contains(&j) {
                        in_degree[j] -= 1;
                    }
                }
            }

            waves.push(wave);
        }

        waves
    }
}

// ---------------------------------------------------------------------------
// Triangularization
// ---------------------------------------------------------------------------

/// Compile an automaton (from a rholang synchronization tree) into an upper
/// triangular matrix, preserving comm event labels on transitions.
///
/// # How it works
///
/// 1. The automaton states become graph nodes
/// 2. Transitions (labeled with comm events) become directed edges
/// 3. SCCs (mutually reachable states) are collapsed — these represent
///    cyclic communication patterns in the rholang process
/// 4. The condensed DAG is topologically sorted
/// 5. The result is an upper triangular matrix where entry (i,j) indicates
///    a comm event path from state-group i to state-group j
///
/// # GPU execution model
///
/// The resulting matrix directly maps to a wavefront parallel schedule:
/// - Groups with no incoming edges (row with all zeros to the left) can
///   execute as a GPU kernel immediately
/// - Each subsequent "wave" depends only on prior waves completing
/// - SCCs (collapsed groups) require iterative fixpoint within a single kernel
pub fn automaton_to_triangular(
    automaton: &Automaton,
) -> Result<TriangularAutomatonResult, TriangularError> {
    let (graph, events) = automaton.to_digraph();
    let triangular = triangularize(&graph)?;

    // Build the labeled transition map
    let mut transition_labels: HashMap<(usize, usize), Vec<usize>> = HashMap::new();

    for (event_idx, t) in automaton.transitions.iter().enumerate() {
        let from_group = triangular.node_to_group.get(&t.from);
        let to_group = triangular.node_to_group.get(&t.to);

        if let (Some(&fg), Some(&tg)) = (from_group, to_group) {
            if fg != tg {
                let (row, col) = if fg < tg { (fg, tg) } else { (tg, fg) };
                transition_labels
                    .entry((row, col))
                    .or_default()
                    .push(event_idx);
            }
        }
    }

    // Determine which groups contain accepting states
    let mut accepting_groups = HashSet::new();
    for &state in &automaton.accepting {
        if let Some(&group) = triangular.node_to_group.get(&state) {
            accepting_groups.insert(group);
        }
    }

    // Find the initial state's group
    let initial_group = triangular
        .node_to_group
        .get(&automaton.initial)
        .copied()
        .unwrap_or(0);

    Ok(TriangularAutomatonResult {
        triangular,
        events,
        transition_labels,
        accepting_groups,
        initial_group,
    })
}

/// Pretty-print the triangularized automaton, showing states, comm events, and the matrix.
pub fn pretty_print_automaton(result: &TriangularAutomatonResult) -> String {
    let mut out = String::new();
    out.push_str("=== Triangularized Rholang Automaton ===\n\n");

    out.push_str(&format!("Initial group: [{}]\n", result.initial_group));
    out.push_str(&format!(
        "Accepting groups: {:?}\n\n",
        result.accepting_groups
    ));

    out.push_str("State groups (rows/columns):\n");
    for (i, group) in result.triangular.groups.iter().enumerate() {
        let marker = if result.accepting_groups.contains(&i) {
            " ✓"
        } else {
            ""
        };
        let init_marker = if i == result.initial_group {
            " →"
        } else {
            ""
        };
        if group.len() == 1 {
            out.push_str(&format!("  [{}]{}{} {}\n", i, init_marker, marker, group[0]));
        } else {
            out.push_str(&format!(
                "  [{}]{}{} SCC {{ {} }}\n",
                i,
                init_marker,
                marker,
                group.join(", ")
            ));
        }
    }

    out.push_str("\nTransition labels:\n");
    let mut sorted_keys: Vec<_> = result.transition_labels.keys().collect();
    sorted_keys.sort();
    for &&(i, j) in &sorted_keys {
        let events = result.events_between(i, j);
        for event in events {
            out.push_str(&format!("  [{}] → [{}] : {}\n", i, j, event));
        }
    }

    out.push_str("\nUpper Triangular Matrix:\n");
    let n = result.triangular.matrix.nrows();
    out.push_str("     ");
    for j in 0..n {
        out.push_str(&format!("{:>4}", j));
    }
    out.push('\n');
    out.push_str("     ");
    for _ in 0..n {
        out.push_str("----");
    }
    out.push('\n');
    for i in 0..n {
        out.push_str(&format!(" {:>2} |", i));
        for j in 0..n {
            let v = result.triangular.matrix[(i, j)];
            if v == 0.0 {
                out.push_str("   .");
            } else {
                out.push_str(&format!("{:>4}", v as i64));
            }
        }
        out.push('\n');
    }

    // Wavefront schedule
    let waves = result.wavefront_schedule();
    out.push_str("\nWavefront parallel schedule (GPU kernel dispatch order):\n");
    for (i, wave) in waves.iter().enumerate() {
        let labels: Vec<String> = wave
            .iter()
            .map(|&g| {
                let group = &result.triangular.groups[g];
                if group.len() == 1 {
                    format!("[{}] {}", g, group[0])
                } else {
                    format!("[{}] SCC({})", g, group.join(", "))
                }
            })
            .collect();
        out.push_str(&format!("  Wave {}: {}\n", i, labels.join("  |  ")));
    }

    out
}

// ---------------------------------------------------------------------------
// Builder — ergonomic API for constructing automata from sync trees
// ---------------------------------------------------------------------------

/// Builder for constructing automata incrementally from symbolic execution.
///
/// This provides a convenient interface for the symbolic executor to
/// build up the automaton as it unfolds the synchronization tree.
///
/// # Example
/// ```
/// use dag_triangular::automata::*;
///
/// let mut builder = AutomatonBuilder::new();
/// let s0 = builder.add_state("init");
/// let s1 = builder.add_state("sent");
/// let s2 = builder.add_state("done");
///
/// builder.set_initial(s0);
/// builder.set_accepting(s2);
///
/// builder.add_send(s0, s1, "x", vec![RhoData::Int(42)]);
/// builder.add_receive(s1, s2, "y", vec![RhoData::Wildcard]);
///
/// let automaton = builder.build();
/// ```
pub struct AutomatonBuilder {
    states: Vec<Option<String>>,
    initial: Option<StateId>,
    accepting: HashSet<StateId>,
    transitions: Vec<Transition>,
}

impl AutomatonBuilder {
    pub fn new() -> Self {
        AutomatonBuilder {
            states: Vec::new(),
            initial: None,
            accepting: HashSet::new(),
            transitions: Vec::new(),
        }
    }

    /// Add a state with an optional label. Returns the state ID.
    pub fn add_state(&mut self, label: impl Into<String>) -> StateId {
        let id = self.states.len();
        self.states.push(Some(label.into()));
        id
    }

    /// Add an unlabeled state. Returns the state ID.
    pub fn add_anonymous_state(&mut self) -> StateId {
        let id = self.states.len();
        self.states.push(None);
        id
    }

    /// Set the initial state.
    pub fn set_initial(&mut self, state: StateId) {
        self.initial = Some(state);
    }

    /// Mark a state as accepting.
    pub fn set_accepting(&mut self, state: StateId) {
        self.accepting.insert(state);
    }

    /// Add a send transition: `channel!(data)`.
    pub fn add_send(
        &mut self,
        from: StateId,
        to: StateId,
        channel: impl Into<String>,
        data: Vec<RhoData>,
    ) {
        self.transitions.push(Transition {
            from,
            to,
            label: CommEvent::Send {
                channel: ChannelName(channel.into()),
                data,
            },
        });
    }

    /// Add a receive transition: `for(patterns <- channel)`.
    pub fn add_receive(
        &mut self,
        from: StateId,
        to: StateId,
        channel: impl Into<String>,
        patterns: Vec<RhoData>,
    ) {
        self.transitions.push(Transition {
            from,
            to,
            label: CommEvent::Receive {
                channel: ChannelName(channel.into()),
                patterns,
            },
        });
    }

    /// Add a comm (synchronized send/receive) transition.
    pub fn add_comm(
        &mut self,
        from: StateId,
        to: StateId,
        channel: impl Into<String>,
        data: Vec<RhoData>,
    ) {
        self.transitions.push(Transition {
            from,
            to,
            label: CommEvent::Comm {
                channel: ChannelName(channel.into()),
                data,
            },
        });
    }

    /// Add a tau (internal) transition.
    pub fn add_tau(&mut self, from: StateId, to: StateId, description: Option<String>) {
        self.transitions.push(Transition {
            from,
            to,
            label: CommEvent::Tau { description },
        });
    }

    /// Add a peek (persistent receive) transition.
    pub fn add_peek(
        &mut self,
        from: StateId,
        to: StateId,
        channel: impl Into<String>,
        patterns: Vec<RhoData>,
    ) {
        self.transitions.push(Transition {
            from,
            to,
            label: CommEvent::Peek {
                channel: ChannelName(channel.into()),
                patterns,
            },
        });
    }

    /// Add a generic transition with an arbitrary CommEvent.
    pub fn add_transition(&mut self, from: StateId, to: StateId, label: CommEvent) {
        self.transitions.push(Transition { from, to, label });
    }

    /// Build the automaton.
    pub fn build(self) -> Automaton {
        let num_states = self.states.len();
        let initial = self.initial.unwrap_or(0);

        let mut automaton = Automaton::new(num_states, initial);
        automaton.accepting = self.accepting;
        automaton.transitions = self.transitions;

        for (i, label) in self.states.into_iter().enumerate() {
            if let Some(l) = label {
                automaton.label_state(i, l);
            }
        }

        automaton
    }
}

impl Default for AutomatonBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a simple linear automaton
    /// S0 --send x!(42)--> S1 --recv y--> S2
    fn simple_linear() -> Automaton {
        let mut b = AutomatonBuilder::new();
        let s0 = b.add_state("for(x <- chan){ x!(42) | for(y <- result){ Nil } }");
        let s1 = b.add_state("for(y <- result){ Nil }");
        let s2 = b.add_state("Nil");

        b.set_initial(s0);
        b.set_accepting(s2);

        b.add_send(s0, s1, "chan", vec![RhoData::Int(42)]);
        b.add_receive(s1, s2, "result", vec![RhoData::Wildcard]);

        b.build()
    }

    #[test]
    fn test_simple_linear_automaton() {
        let automaton = simple_linear();
        let result = automaton_to_triangular(&automaton).unwrap();

        assert_eq!(result.triangular.matrix.nrows(), 3);
        assert!(is_upper_triangular(&result.triangular.matrix));
        assert_eq!(result.initial_group, 0);
        assert!(!result.accepting_groups.is_empty());

        let waves = result.wavefront_schedule();
        // Linear chain: 3 waves of 1 each
        assert_eq!(waves.len(), 3);
    }

    #[test]
    fn test_parallel_composition() {
        // Model: P | Q where P and Q communicate independently
        // S0 --> S1 (send on x)
        // S0 --> S2 (send on y)
        // S1 --> S3 (recv on x_result)
        // S2 --> S3 (recv on y_result)
        let mut b = AutomatonBuilder::new();
        let s0 = b.add_state("P | Q");
        let s1 = b.add_state("P sent");
        let s2 = b.add_state("Q sent");
        let s3 = b.add_state("Nil");

        b.set_initial(s0);
        b.set_accepting(s3);

        b.add_send(s0, s1, "x", vec![RhoData::Int(1)]);
        b.add_send(s0, s2, "y", vec![RhoData::Int(2)]);
        b.add_receive(s1, s3, "x_result", vec![RhoData::Wildcard]);
        b.add_receive(s2, s3, "y_result", vec![RhoData::Wildcard]);

        let result = automaton_to_triangular(&b.build()).unwrap();
        assert!(is_upper_triangular(&result.triangular.matrix));

        let waves = result.wavefront_schedule();
        // S1 and S2 should be in the same wave (parallel)
        assert!(waves.len() < 4, "Parallel branches should reduce wave count");
    }

    #[test]
    fn test_cyclic_communication() {
        // Model a ping-pong pattern (cycle in the automaton)
        // S0 --send ping--> S1 --recv pong--> S0 (cycle!)
        // S0 --tau(done)--> S2 (exit)
        let mut b = AutomatonBuilder::new();
        let s0 = b.add_state("ready");
        let s1 = b.add_state("waiting_pong");
        let s2 = b.add_state("done");

        b.set_initial(s0);
        b.set_accepting(s2);

        b.add_send(s0, s1, "ping", vec![RhoData::Str("hello".into())]);
        b.add_receive(s1, s0, "pong", vec![RhoData::Wildcard]); // cycle!
        b.add_tau(s0, s2, Some("loop_exit".into()));

        let result = automaton_to_triangular(&b.build()).unwrap();
        assert!(is_upper_triangular(&result.triangular.matrix));

        // S0 and S1 form an SCC, so matrix should be 2x2
        assert_eq!(result.triangular.matrix.nrows(), 2);

        // The SCC group should contain both states
        let scc_group = result
            .triangular
            .groups
            .iter()
            .find(|g| g.len() == 2)
            .expect("Should have an SCC group for the ping-pong cycle");
        assert!(scc_group.iter().any(|s| s.contains("ready")));
        assert!(scc_group.iter().any(|s| s.contains("waiting_pong")));
    }

    #[test]
    fn test_rholang_contract_pattern() {
        // Model a simple rholang contract:
        //   new self in {
        //     contract self(@method, return) = {
        //       if (method == "get") { return!(state) }
        //       else { return!(false) }
        //     }
        //   }
        let mut b = AutomatonBuilder::new();
        let s0 = b.add_state("contract_listening");
        let s1 = b.add_state("method_received");
        let s2 = b.add_state("dispatching_get");
        let s3 = b.add_state("dispatching_unknown");
        let s4 = b.add_state("returned_state");
        let s5 = b.add_state("returned_false");

        b.set_initial(s0);
        b.set_accepting(s4);
        b.set_accepting(s5);

        // Receive the method call
        b.add_receive(
            s0,
            s1,
            "self",
            vec![RhoData::Symbolic("method".into()), RhoData::Symbolic("return".into())],
        );

        // Internal dispatch based on method value
        b.add_tau(s1, s2, Some("match method == \"get\"".into()));
        b.add_tau(s1, s3, Some("match method != \"get\"".into()));

        // Send results back on return channel
        b.add_send(s2, s4, "return", vec![RhoData::Symbolic("state".into())]);
        b.add_send(s3, s5, "return", vec![RhoData::Bool(false)]);

        let automaton = b.build();
        let result = automaton_to_triangular(&automaton).unwrap();

        assert!(is_upper_triangular(&result.triangular.matrix));
        assert_eq!(result.accepting_groups.len(), 2);

        let waves = result.wavefront_schedule();
        println!("{}", pretty_print_automaton(&result));

        // The two dispatch branches should be parallelizable
        assert!(
            waves.iter().any(|w| w.len() >= 2),
            "Dispatch branches should be parallelizable in the same wave"
        );
    }

    #[test]
    fn test_comm_event_display() {
        let send = CommEvent::Send {
            channel: ChannelName("x".into()),
            data: vec![RhoData::Int(42), RhoData::Str("hello".into())],
        };
        assert_eq!(format!("{}", send), "x!(42, \"hello\")");

        let recv = CommEvent::Receive {
            channel: ChannelName("y".into()),
            patterns: vec![RhoData::Wildcard],
        };
        assert_eq!(format!("{}", recv), "for(_ <- y)");

        let comm = CommEvent::Comm {
            channel: ChannelName("z".into()),
            data: vec![RhoData::Bool(true)],
        };
        assert_eq!(format!("{}", comm), "τ@z(true)");

        let tau = CommEvent::Tau {
            description: Some("eval 2+3".into()),
        };
        assert_eq!(format!("{}", tau), "τ[eval 2+3]");
    }

    #[test]
    fn test_wavefront_schedule_ordering() {
        // S0 -> S1 -> S2 -> S3 (pure chain)
        let mut b = AutomatonBuilder::new();
        let s0 = b.add_state("S0");
        let s1 = b.add_state("S1");
        let s2 = b.add_state("S2");
        let s3 = b.add_state("S3");

        b.set_initial(s0);
        b.set_accepting(s3);

        b.add_comm(s0, s1, "a", vec![]);
        b.add_comm(s1, s2, "b", vec![]);
        b.add_comm(s2, s3, "c", vec![]);

        let result = automaton_to_triangular(&b.build()).unwrap();
        let waves = result.wavefront_schedule();

        // Strict chain => 4 waves of 1 each
        assert_eq!(waves.len(), 4);
        for wave in &waves {
            assert_eq!(wave.len(), 1);
        }
    }

    #[test]
    fn test_collection_data_types() {
        let mut b = AutomatonBuilder::new();
        let s0 = b.add_state("init");
        let s1 = b.add_state("done");

        b.set_initial(s0);
        b.set_accepting(s1);

        // Send a complex data structure: a map containing a list
        b.add_send(
            s0,
            s1,
            "data_channel",
            vec![RhoData::Map(vec![
                (
                    RhoData::Str("items".into()),
                    RhoData::List(vec![RhoData::Int(1), RhoData::Int(2), RhoData::Int(3)]),
                ),
                (
                    RhoData::Str("count".into()),
                    RhoData::Int(3),
                ),
            ])],
        );

        let result = automaton_to_triangular(&b.build()).unwrap();
        assert!(is_upper_triangular(&result.triangular.matrix));
        assert_eq!(result.events.len(), 1);

        // Verify the complex data round-trips through display
        let event_str = format!("{}", result.events[0]);
        assert!(event_str.contains("data_channel"));
        assert!(event_str.contains("items"));
    }
}
