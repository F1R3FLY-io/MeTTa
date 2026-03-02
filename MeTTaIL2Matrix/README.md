# dag-triangular

Compile directed graphs and automata into upper triangular adjacency matrices, with first-class support for rholang synchronization trees targeting GPU execution.

## Pipeline

```
rholang expr → symbolic execution → synchronization tree → automata → triangularize → GPU
                                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                                                           this crate handles this part
```

## What it does

**Core graph triangularization:**
1. Computes **strongly connected components** (SCCs) to detect cycles
2. **Condenses** the graph into a DAG by collapsing cycles into single nodes
3. **Topologically sorts** the condensed DAG
4. Produces an **upper triangular adjacency matrix**

**Rholang automata frontend (`automata` module):**
1. Accepts an automaton with states and **comm event**–labeled transitions
2. Supports rholang communication primitives: `send`, `receive`, `comm`, `peek`, `tau`
3. Handles rholang data types: integers, booleans, strings, lists, sets, maps, names
4. Triangularizes the automaton preserving transition labels
5. Computes a **wavefront parallel schedule** for GPU kernel dispatch

## Quick Start

### Basic graph triangularization

```rust
use petgraph::graph::DiGraph;
use dag_triangular::{triangularize, is_upper_triangular, pretty_print};

let mut graph = DiGraph::<&str, ()>::new();
let a = graph.add_node("parser");
let b = graph.add_node("lexer");
let c = graph.add_node("tokens");
graph.add_edge(a, b, ());
graph.add_edge(b, c, ());

let result = triangularize(&graph).unwrap();
assert!(is_upper_triangular(&result.matrix));
```

### Rholang synchronization tree automaton

```rust
use dag_triangular::automata::*;

// Build an automaton from symbolic execution of a rholang process
let mut b = AutomatonBuilder::new();
let s0 = b.add_state("x!(42) | for(y <- result){ Nil }");
let s1 = b.add_state("for(y <- result){ Nil }");
let s2 = b.add_state("Nil");

b.set_initial(s0);
b.set_accepting(s2);

b.add_send(s0, s1, "x", vec![RhoData::Int(42)]);
b.add_receive(s1, s2, "result", vec![RhoData::Wildcard]);

let result = automaton_to_triangular(&b.build()).unwrap();

// Get the GPU execution schedule
let waves = result.wavefront_schedule();
for (i, wave) in waves.iter().enumerate() {
    println!("Wave {}: {} parallel groups", i, wave.len());
}
```

## Comm Events

The automata module models rholang communication primitives:

| Event | Rholang syntax | Description |
|---|---|---|
| `Send` | `channel!(data)` | Send data on a channel |
| `Receive` | `for(pattern <- channel){...}` | Receive (consume) from a channel |
| `Comm` | τ@channel(data) | Synchronized communication (COMM rule fired) |
| `Peek` | `for(pattern <= channel){...}` | Persistent receive (read without consuming) |
| `Tau` | τ | Internal computation (arithmetic, boolean, string, collection ops) |

## Data Types

The `RhoData` enum covers rholang's data extensions:

| Variant | Description |
|---|---|
| `Int(i64)` | Arithmetic values |
| `Bool(bool)` | Boolean values |
| `Str(String)` | String values |
| `List(Vec<RhoData>)` | List collections |
| `Set(Vec<RhoData>)` | Set collections |
| `Map(Vec<(RhoData, RhoData)>)` | Map collections |
| `Name(ChannelName)` | Channel/name references |
| `Wildcard` | Pattern wildcard |
| `Symbolic(String)` | Symbolic variables (from symbolic execution) |

## GPU Execution Model

The upper triangular matrix maps directly to wavefront parallelism:

- **Wave 0**: All groups with no incoming edges launch as GPU kernels simultaneously
- **Wave 1**: Groups depending only on Wave 0 launch next
- Each subsequent wave depends only on prior waves
- **SCCs** (collapsed cyclic states) require iterative fixpoint within a single kernel

```
Wave 0: [init]              → GPU kernel 0
Wave 1: [branch_a | branch_b] → GPU kernels 1a, 1b (parallel!)
Wave 2: [join_point]         → GPU kernel 2
```

## Handling Cycles

Cyclic communication patterns (e.g., ping-pong protocols, recursive contracts) are collapsed into single matrix entries. The states within an SCC would need iterative execution on the GPU — the matrix tells you *which* groups cycle and *what* their external dependencies are.

## API Reference

### Core (`dag_triangular`)

| Function | Description |
|---|---|
| `triangularize(&graph)` | DiGraph → upper triangular matrix |
| `triangularize_weighted(&graph)` | Same, with summed edge weights |
| `is_upper_triangular(&matrix)` | Verify matrix form |
| `pretty_print(&result)` | Display the result |

### Automata (`dag_triangular::automata`)

| Type / Function | Description |
|---|---|
| `Automaton` | States + comm event transitions |
| `AutomatonBuilder` | Ergonomic builder for symbolic executors |
| `CommEvent` | Send, Receive, Comm, Peek, Tau |
| `RhoData` | Rholang data types |
| `automaton_to_triangular(&automaton)` | Automaton → triangular matrix |
| `TriangularAutomatonResult` | Result with labels + wavefront schedule |
| `pretty_print_automaton(&result)` | Display with comm events and GPU schedule |

## Running the Examples

```sh
# Basic dependency analysis
cargo run --example dependency_analysis

# Rholang synchronization tree (token transfer contract)
cargo run --example rholang_sync_tree
```

## License

MIT
