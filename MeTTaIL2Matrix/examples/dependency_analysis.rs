//! Example: Compile a dependency graph into an upper triangular matrix.
//!
//! Run with: cargo run --example dependency_analysis

use petgraph::graph::DiGraph;

fn main() {
    println!("=== Example 1: Simple DAG (build dependencies) ===\n");
    simple_dag_example();

    println!("\n=== Example 2: Graph with cycles (module dependencies) ===\n");
    cycle_example();

    println!("\n=== Example 3: Weighted edges (call frequency) ===\n");
    weighted_example();
}

fn simple_dag_example() {
    // Simulating build dependencies:
    //   main.rs depends on lib.rs
    //   lib.rs depends on utils.rs and config.rs
    //   utils.rs depends on config.rs
    let mut graph = DiGraph::<&str, ()>::new();
    let main = graph.add_node("main.rs");
    let lib = graph.add_node("lib.rs");
    let utils = graph.add_node("utils.rs");
    let config = graph.add_node("config.rs");

    graph.add_edge(main, lib, ());
    graph.add_edge(lib, utils, ());
    graph.add_edge(lib, config, ());
    graph.add_edge(utils, config, ());

    let result = dag_triangular::triangularize(&graph).unwrap();
    println!("{}", dag_triangular::pretty_print(&result));
    println!(
        "Is upper triangular: {}",
        dag_triangular::is_upper_triangular(&result.matrix)
    );

    println!("\nBuild order (topological):");
    for (i, group) in result.groups.iter().enumerate() {
        println!("  Step {}: {:?}", i + 1, group);
    }
}

fn cycle_example() {
    // Module dependency graph with mutual recursion:
    //   parser -> lexer -> tokens
    //   parser <-> type_checker  (mutual dependency / cycle)
    //   type_checker -> tokens
    //   codegen -> parser
    //   codegen -> type_checker
    let mut graph = DiGraph::<&str, ()>::new();
    let parser = graph.add_node("parser");
    let lexer = graph.add_node("lexer");
    let tokens = graph.add_node("tokens");
    let type_checker = graph.add_node("type_checker");
    let codegen = graph.add_node("codegen");

    graph.add_edge(parser, lexer, ());
    graph.add_edge(lexer, tokens, ());
    graph.add_edge(parser, type_checker, ()); // cycle
    graph.add_edge(type_checker, parser, ()); // cycle
    graph.add_edge(type_checker, tokens, ());
    graph.add_edge(codegen, parser, ());
    graph.add_edge(codegen, type_checker, ());

    let result = dag_triangular::triangularize(&graph).unwrap();
    println!("{}", dag_triangular::pretty_print(&result));
    println!(
        "Is upper triangular: {}",
        dag_triangular::is_upper_triangular(&result.matrix)
    );

    println!("\nNote: parser and type_checker form a cycle and are collapsed into one group.");
    println!("This is common in compilers where type checking and parsing are mutually recursive.");
}

fn weighted_example() {
    // Call frequency graph: edges weighted by how often one module calls another
    let mut graph = DiGraph::<&str, f64>::new();
    let api = graph.add_node("api");
    let auth = graph.add_node("auth");
    let db = graph.add_node("db");
    let cache = graph.add_node("cache");

    graph.add_edge(api, auth, 100.0); // api calls auth 100 times
    graph.add_edge(api, db, 50.0); // api calls db 50 times
    graph.add_edge(api, cache, 200.0); // api calls cache 200 times
    graph.add_edge(auth, db, 30.0); // auth calls db 30 times
    graph.add_edge(cache, db, 75.0); // cache calls db 75 times

    let result = dag_triangular::triangularize_weighted(&graph).unwrap();
    println!("{}", dag_triangular::pretty_print(&result));
    println!(
        "Is upper triangular: {}",
        dag_triangular::is_upper_triangular(&result.matrix)
    );

    println!("\nWeighted values show call frequencies between service layers.");
}
