//! # dag-triangular
//!
//! Compile directed graphs into upper triangular adjacency matrices.
//!
//! Given a directed graph (possibly with cycles), this crate:
//! 1. Computes strongly connected components (SCCs)
//! 2. Condenses the graph into a DAG of SCCs
//! 3. Topologically sorts the condensed DAG
//! 4. Produces an upper triangular adjacency matrix
//!
//! This is useful for dependency analysis, scheduling in concurrent systems,
//! compiler pass ordering, and similar applications.

use nalgebra::DMatrix;
use petgraph::algo::{kosaraju_scc, toposort};
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::EdgeRef;
use std::collections::HashMap;

pub mod automata;
mod error;
pub use error::TriangularError;

/// The result of triangularizing a directed graph.
#[derive(Debug, Clone)]
pub struct TriangularResult<N: Clone> {
    /// Upper triangular adjacency matrix.
    /// `matrix[(i, j)] = 1.0` means there is an edge from group `i` to group `j`, where `i < j`.
    pub matrix: DMatrix<f64>,

    /// The ordered groups (rows/columns of the matrix).
    /// Each group is a `Vec<N>` representing either a single node or
    /// a strongly connected component (cycle) that was collapsed.
    pub groups: Vec<Vec<N>>,

    /// Maps each original node weight to its group index in the matrix.
    pub node_to_group: HashMap<usize, usize>,
}

/// Weighted edge information preserved through condensation.
#[derive(Debug, Clone)]
pub struct EdgeWeight {
    /// Accumulated weight (number of edges between groups, or sum of weights).
    pub weight: f64,
}

/// Compile a directed graph into an upper triangular adjacency matrix.
///
/// Nodes in cycles (strongly connected components with >1 node) are collapsed
/// into a single row/column in the resulting matrix.
///
/// # Arguments
/// * `graph` - A directed graph with node weights of type `N` and edge weights of type `E`.
///
/// # Returns
/// A `TriangularResult` containing the upper triangular matrix, the ordered groups,
/// and a mapping from original node indices to group indices.
///
/// # Example
/// ```
/// use petgraph::graph::DiGraph;
/// use dag_triangular::triangularize;
///
/// let mut graph = DiGraph::<&str, ()>::new();
/// let a = graph.add_node("A");
/// let b = graph.add_node("B");
/// let c = graph.add_node("C");
/// graph.add_edge(a, b, ());
/// graph.add_edge(b, c, ());
///
/// let result = triangularize(&graph).unwrap();
/// assert_eq!(result.matrix.nrows(), 3);
/// // All edges are in the upper triangle
/// assert_eq!(result.matrix[(0, 1)], 1.0); // A -> B
/// assert_eq!(result.matrix[(1, 2)], 1.0); // B -> C
/// assert_eq!(result.matrix[(1, 0)], 0.0); // No lower triangle entries
/// ```
pub fn triangularize<N, E>(graph: &DiGraph<N, E>) -> Result<TriangularResult<N>, TriangularError>
where
    N: Clone,
{
    if graph.node_count() == 0 {
        return Ok(TriangularResult {
            matrix: DMatrix::zeros(0, 0),
            groups: vec![],
            node_to_group: HashMap::new(),
        });
    }

    // Step 1: Find strongly connected components
    let sccs = kosaraju_scc(graph);

    // Step 2: Map each node to its SCC index
    let mut node_to_scc: HashMap<NodeIndex, usize> = HashMap::new();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for &node in scc {
            node_to_scc.insert(node, scc_idx);
        }
    }

    // Step 3: Build the condensed DAG
    let num_sccs = sccs.len();
    let mut condensed = DiGraph::<usize, ()>::new();
    let mut scc_nodes: Vec<NodeIndex> = Vec::with_capacity(num_sccs);
    for i in 0..num_sccs {
        scc_nodes.push(condensed.add_node(i));
    }

    // Track which condensed edges we've already added (avoid duplicates)
    let mut condensed_edges: HashMap<(usize, usize), bool> = HashMap::new();
    for edge in graph.edge_references() {
        let src_scc = node_to_scc[&edge.source()];
        let tgt_scc = node_to_scc[&edge.target()];
        if src_scc != tgt_scc && !condensed_edges.contains_key(&(src_scc, tgt_scc)) {
            condensed.add_edge(scc_nodes[src_scc], scc_nodes[tgt_scc], ());
            condensed_edges.insert((src_scc, tgt_scc), true);
        }
    }

    // Step 4: Topological sort of the condensed DAG
    let topo_order = toposort(&condensed, None).map_err(|_| {
        TriangularError::InternalError(
            "Topological sort failed on condensed graph (this should not happen)".into(),
        )
    })?;

    // Step 5: Build the position map (topo index -> matrix row/col)
    let mut scc_to_pos: Vec<usize> = vec![0; num_sccs];
    for (pos, &node) in topo_order.iter().enumerate() {
        let scc_idx = *condensed.node_weight(node).unwrap();
        scc_to_pos[scc_idx] = pos;
    }

    // Step 6: Build the upper triangular matrix
    let n = num_sccs;
    let mut matrix = DMatrix::zeros(n, n);

    for edge in graph.edge_references() {
        let src_scc = node_to_scc[&edge.source()];
        let tgt_scc = node_to_scc[&edge.target()];
        if src_scc != tgt_scc {
            let r = scc_to_pos[src_scc];
            let c = scc_to_pos[tgt_scc];
            // In a correct topological order, r < c for all DAG edges
            let (row, col) = if r < c { (r, c) } else { (c, r) };
            matrix[(row, col)] = 1.0;
        }
    }

    // Step 7: Build ordered groups with original node weights
    let mut groups: Vec<Vec<N>> = vec![Vec::new(); num_sccs];
    for (scc_idx, scc) in sccs.iter().enumerate() {
        let pos = scc_to_pos[scc_idx];
        groups[pos] = scc
            .iter()
            .map(|&node| graph.node_weight(node).unwrap().clone())
            .collect();
    }

    // Step 8: Build node-to-group mapping (by original node index)
    let mut node_to_group: HashMap<usize, usize> = HashMap::new();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        let pos = scc_to_pos[scc_idx];
        for &node in scc {
            node_to_group.insert(node.index(), pos);
        }
    }

    Ok(TriangularResult {
        matrix,
        groups,
        node_to_group,
    })
}

/// Compile a directed graph into an upper triangular adjacency matrix with edge weights.
///
/// Similar to `triangularize`, but preserves edge weight information by summing
/// weights of edges between groups.
///
/// # Arguments
/// * `graph` - A directed graph with edge weights convertible to `f64`.
pub fn triangularize_weighted<N, E>(
    graph: &DiGraph<N, E>,
) -> Result<TriangularResult<N>, TriangularError>
where
    N: Clone,
    E: Clone + Into<f64>,
{
    if graph.node_count() == 0 {
        return Ok(TriangularResult {
            matrix: DMatrix::zeros(0, 0),
            groups: vec![],
            node_to_group: HashMap::new(),
        });
    }

    let sccs = kosaraju_scc(graph);
    let mut node_to_scc: HashMap<NodeIndex, usize> = HashMap::new();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for &node in scc {
            node_to_scc.insert(node, scc_idx);
        }
    }

    let num_sccs = sccs.len();
    let mut condensed = DiGraph::<usize, ()>::new();
    let mut scc_nodes: Vec<NodeIndex> = Vec::with_capacity(num_sccs);
    for i in 0..num_sccs {
        scc_nodes.push(condensed.add_node(i));
    }

    let mut condensed_edges: HashMap<(usize, usize), bool> = HashMap::new();
    for edge in graph.edge_references() {
        let src_scc = node_to_scc[&edge.source()];
        let tgt_scc = node_to_scc[&edge.target()];
        if src_scc != tgt_scc && !condensed_edges.contains_key(&(src_scc, tgt_scc)) {
            condensed.add_edge(scc_nodes[src_scc], scc_nodes[tgt_scc], ());
            condensed_edges.insert((src_scc, tgt_scc), true);
        }
    }

    let topo_order = toposort(&condensed, None).map_err(|_| {
        TriangularError::InternalError(
            "Topological sort failed on condensed graph".into(),
        )
    })?;

    let mut scc_to_pos: Vec<usize> = vec![0; num_sccs];
    for (pos, &node) in topo_order.iter().enumerate() {
        let scc_idx = *condensed.node_weight(node).unwrap();
        scc_to_pos[scc_idx] = pos;
    }

    let n = num_sccs;
    let mut matrix = DMatrix::zeros(n, n);

    // Sum edge weights between groups
    for edge in graph.edge_references() {
        let src_scc = node_to_scc[&edge.source()];
        let tgt_scc = node_to_scc[&edge.target()];
        if src_scc != tgt_scc {
            let r = scc_to_pos[src_scc];
            let c = scc_to_pos[tgt_scc];
            let (row, col) = if r < c { (r, c) } else { (c, r) };
            let w: f64 = edge.weight().clone().into();
            matrix[(row, col)] += w;
        }
    }

    let mut groups: Vec<Vec<N>> = vec![Vec::new(); num_sccs];
    for (scc_idx, scc) in sccs.iter().enumerate() {
        let pos = scc_to_pos[scc_idx];
        groups[pos] = scc
            .iter()
            .map(|&node| graph.node_weight(node).unwrap().clone())
            .collect();
    }

    let mut node_to_group: HashMap<usize, usize> = HashMap::new();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        let pos = scc_to_pos[scc_idx];
        for &node in scc {
            node_to_group.insert(node.index(), pos);
        }
    }

    Ok(TriangularResult {
        matrix,
        groups,
        node_to_group,
    })
}

/// Check if a matrix is upper triangular (all entries below the diagonal are zero).
pub fn is_upper_triangular(matrix: &DMatrix<f64>) -> bool {
    let n = matrix.nrows().min(matrix.ncols());
    for i in 0..n {
        for j in 0..i {
            if matrix[(i, j)].abs() > f64::EPSILON {
                return false;
            }
        }
    }
    true
}

/// Pretty-print the triangular result, showing groups and the matrix.
pub fn pretty_print<N: Clone + std::fmt::Debug>(result: &TriangularResult<N>) -> String {
    let mut out = String::new();
    out.push_str("=== Triangularized Graph ===\n\n");

    out.push_str("Groups (rows/columns):\n");
    for (i, group) in result.groups.iter().enumerate() {
        if group.len() == 1 {
            out.push_str(&format!("  [{}] {:?}\n", i, group[0]));
        } else {
            out.push_str(&format!("  [{}] SCC {:?}\n", i, group));
        }
    }

    out.push_str("\nUpper Triangular Adjacency Matrix:\n");
    let n = result.matrix.nrows();
    // Header
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
            let v = result.matrix[(i, j)];
            if v == 0.0 {
                out.push_str("   .");
            } else {
                out.push_str(&format!("{:>4}", v as i64));
            }
        }
        out.push('\n');
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::DiGraph;

    #[test]
    fn test_simple_dag() {
        // A -> B -> C
        let mut g = DiGraph::<&str, ()>::new();
        let a = g.add_node("A");
        let b = g.add_node("B");
        let c = g.add_node("C");
        g.add_edge(a, b, ());
        g.add_edge(b, c, ());

        let result = triangularize(&g).unwrap();
        assert_eq!(result.matrix.nrows(), 3);
        assert!(is_upper_triangular(&result.matrix));
    }

    #[test]
    fn test_diamond_dag() {
        //   A
        //  / \
        // B   C
        //  \ /
        //   D
        let mut g = DiGraph::<&str, ()>::new();
        let a = g.add_node("A");
        let b = g.add_node("B");
        let c = g.add_node("C");
        let d = g.add_node("D");
        g.add_edge(a, b, ());
        g.add_edge(a, c, ());
        g.add_edge(b, d, ());
        g.add_edge(c, d, ());

        let result = triangularize(&g).unwrap();
        assert_eq!(result.matrix.nrows(), 4);
        assert!(is_upper_triangular(&result.matrix));
    }

    #[test]
    fn test_graph_with_cycle() {
        // A -> B -> C -> B (cycle), A -> D
        let mut g = DiGraph::<&str, ()>::new();
        let a = g.add_node("A");
        let b = g.add_node("B");
        let c = g.add_node("C");
        let d = g.add_node("D");
        g.add_edge(a, b, ());
        g.add_edge(b, c, ());
        g.add_edge(c, b, ()); // cycle B <-> C
        g.add_edge(a, d, ());

        let result = triangularize(&g).unwrap();
        // B and C are collapsed into one SCC, so 3 groups: A, {B,C}, D
        assert_eq!(result.matrix.nrows(), 3);
        assert!(is_upper_triangular(&result.matrix));

        // Find the SCC group
        let has_scc = result.groups.iter().any(|g| g.len() == 2);
        assert!(has_scc, "Should have an SCC group with B and C");
    }

    #[test]
    fn test_empty_graph() {
        let g = DiGraph::<&str, ()>::new();
        let result = triangularize(&g).unwrap();
        assert_eq!(result.matrix.nrows(), 0);
        assert_eq!(result.groups.len(), 0);
    }

    #[test]
    fn test_single_node() {
        let mut g = DiGraph::<&str, ()>::new();
        g.add_node("A");
        let result = triangularize(&g).unwrap();
        assert_eq!(result.matrix.nrows(), 1);
        assert_eq!(result.matrix[(0, 0)], 0.0);
    }

    #[test]
    fn test_disconnected_nodes() {
        let mut g = DiGraph::<&str, ()>::new();
        g.add_node("A");
        g.add_node("B");
        g.add_node("C");

        let result = triangularize(&g).unwrap();
        assert_eq!(result.matrix.nrows(), 3);
        assert!(is_upper_triangular(&result.matrix));
        // All zeros since no edges
        for i in 0..3 {
            for j in 0..3 {
                assert_eq!(result.matrix[(i, j)], 0.0);
            }
        }
    }

    #[test]
    fn test_weighted_graph() {
        let mut g = DiGraph::<&str, f64>::new();
        let a = g.add_node("A");
        let b = g.add_node("B");
        let c = g.add_node("C");
        g.add_edge(a, b, 2.5);
        g.add_edge(b, c, 3.0);
        g.add_edge(a, c, 1.0);

        let result = triangularize_weighted(&g).unwrap();
        assert_eq!(result.matrix.nrows(), 3);
        assert!(is_upper_triangular(&result.matrix));
    }
}
