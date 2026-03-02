//! Example: Rholang synchronization tree → upper triangular matrix → GPU schedule
//!
//! This models the synchronization tree from symbolic execution of a rholang
//! process that implements a simple token transfer contract.
//!
//! The rholang source (conceptually):
//! ```rholang
//! new balances, transfer, lookup in {
//!   // Initialize balances
//!   balances!({"alice": 100, "bob": 50}) |
//!
//!   // Transfer contract
//!   contract transfer(@from, @to, @amount, return) = {
//!     for (@state <- balances) {
//!       if (state.get(from) >= amount) {
//!         balances!(state.set(from, state.get(from) - amount)
//!                       .set(to, state.get(to) + amount)) |
//!         return!(true)
//!       } else {
//!         balances!(state) |
//!         return!(false)
//!       }
//!     }
//!   } |
//!
//!   // Lookup contract
//!   contract lookup(@who, return) = {
//!     for (@state <= balances) {
//!       return!(state.get(who))
//!     }
//!   } |
//!
//!   // Client: transfer then lookup
//!   transfer!("alice", "bob", 25, *ack) |
//!   for (_ <- ack) { lookup!("bob", *result) }
//! }
//! ```
//!
//! Run with: cargo run --example rholang_sync_tree

use dag_triangular::automata::*;

fn main() {
    println!("=== Rholang Synchronization Tree → GPU Execution Plan ===\n");
    println!("Modeling: token transfer contract with client interaction\n");

    let mut b = AutomatonBuilder::new();

    // States representing process continuations discovered by symbolic execution
    let s0 = b.add_state("init: balances!(init_state) | transfer_contract | lookup_contract | client");
    let s1 = b.add_state("balances_stored | transfer_contract | lookup_contract | client");
    let s2 = b.add_state("transfer_invoked: for(@state <- balances){...}");
    let s3 = b.add_state("state_received: if(state.get(from) >= amount)");
    let s4 = b.add_state("sufficient_funds: balances!(updated) | return!(true)");
    let s5 = b.add_state("insufficient_funds: balances!(state) | return!(false)");
    let s6 = b.add_state("transfer_complete: ack received, lookup invoked");
    let s7 = b.add_state("lookup_invoked: for(@state <= balances){...}");
    let s8 = b.add_state("lookup_peeked: return!(state.get(who))");
    let s9 = b.add_state("done: result received");

    b.set_initial(s0);
    b.set_accepting(s9);

    // --- Transition 1: Initialize balances channel ---
    b.add_send(
        s0,
        s1,
        "balances",
        vec![RhoData::Map(vec![
            (RhoData::Str("alice".into()), RhoData::Int(100)),
            (RhoData::Str("bob".into()), RhoData::Int(50)),
        ])],
    );

    // --- Transition 2: Client invokes transfer ---
    b.add_send(
        s1,
        s2,
        "transfer",
        vec![
            RhoData::Str("alice".into()),
            RhoData::Str("bob".into()),
            RhoData::Int(25),
            RhoData::Name(ChannelName("ack".into())),
        ],
    );

    // --- Transition 3: Transfer contract receives from balances ---
    b.add_comm(
        s2,
        s3,
        "balances",
        vec![RhoData::Symbolic("state".into())],
    );

    // --- Transition 4a: Sufficient funds branch (tau = arithmetic check) ---
    b.add_tau(s3, s4, Some("eval state.get(\"alice\") >= 25 => true".into()));

    // --- Transition 4b: Insufficient funds branch ---
    b.add_tau(s3, s5, Some("eval state.get(\"alice\") >= 25 => false".into()));

    // --- Transition 5a: Update balances + send ack (sufficient funds path) ---
    b.add_send(
        s4,
        s6,
        "ack",
        vec![RhoData::Bool(true)],
    );

    // --- Transition 5b: Restore balances + send ack (insufficient funds path) ---
    // (In this trace, we follow the sufficient funds path, but the automaton
    //  captures both possibilities from symbolic execution)
    b.add_send(
        s5,
        s6,
        "ack",
        vec![RhoData::Bool(false)],
    );

    // --- Transition 6: Client receives ack, invokes lookup ---
    b.add_comm(
        s6,
        s7,
        "ack",
        vec![RhoData::Symbolic("ack_val".into())],
    );

    // --- Transition 7: Lookup peeks at balances ---
    b.add_peek(
        s7,
        s8,
        "balances",
        vec![RhoData::Symbolic("state".into())],
    );

    // --- Transition 8: Lookup returns result ---
    b.add_send(
        s8,
        s9,
        "result",
        vec![RhoData::Int(75)], // bob's new balance
    );

    let automaton = b.build();

    // Report channels discovered
    let channels = automaton.channels();
    println!("Channels discovered by symbolic execution:");
    for ch in &channels {
        println!("  @{}", ch);
    }

    // Triangularize
    let result = automaton_to_triangular(&automaton).unwrap();

    println!("\n{}", pretty_print_automaton(&result));

    // GPU execution analysis
    let waves = result.wavefront_schedule();
    println!("--- GPU Execution Analysis ---\n");
    println!("Total state groups: {}", result.triangular.matrix.nrows());
    println!("Total waves (sequential steps): {}", waves.len());
    println!(
        "Max parallelism (widest wave): {}",
        waves.iter().map(|w| w.len()).max().unwrap_or(0)
    );

    let total_events: usize = result.transition_labels.values().map(|v| v.len()).sum();
    println!("Total inter-group comm events: {}", total_events);

    println!("\nSCC groups (require iterative fixpoint on GPU):");
    let scc_groups: Vec<_> = result
        .triangular
        .groups
        .iter()
        .enumerate()
        .filter(|(_, g)| g.len() > 1)
        .collect();
    if scc_groups.is_empty() {
        println!("  None — fully acyclic synchronization tree");
    } else {
        for (i, group) in scc_groups {
            println!("  Group [{}]: {} states in cycle", i, group.len());
        }
    }
}
