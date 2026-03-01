//! # Example: Stochastic Rho-Calculus
//!
//! Demonstrates using augmented rewrite rules to simulate a simple
//! rho-calculus program with both classical (stochastic π-machine) and
//! quantum (CTMC) modes.
//!
//! ## The Program
//!
//! ```rholang
//! // A simple client-server interaction with competing channels
//! { server!(request) | server?(x).{handler!(*(x))} | handler?(y).{done!(*(y))} }
//! ```
//!
//! In classical mode, the COMM rule fires stochastically based on channel rates.
//! In quantum mode, amplitudes interfere when multiple communication paths exist.

use mettail_gillespie::augmented_rule::{AugmentedRewriteRule, AugmentedRewriteSystem, TermRef};
use mettail_gillespie::language_ext::RuleBuilder;
use mettail_gillespie::rate_map::RateMap;
use mettail_gillespie::rate_value::RateValue;
use mettail_gillespie::simulator::{Simulator, SimulatorMode};
use mettail_gillespie::spatial_behavior::SpatialBehavior;

fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("  MeTTaIL Gillespie Simulator — Stochastic Rho-Calculus Demo");
    println!("═══════════════════════════════════════════════════════════════\n");

    classical_example();
    println!("\n");
    quantum_example();
}

fn classical_example() {
    println!("━━━ Classical Mode (Stochastic π-machine) ━━━\n");

    // Build the rewrite system with real-valued rates
    let mut system = AugmentedRewriteSystem::new();

    // COMM rule on 'server' channel: rate 0.7
    // server!(request) | server?(x).P  ~>  P{request/x}
    let comm_server = RuleBuilder::new("COMM_server")
        .lhs(1, "Proc", "{ server!(request) | server?(x).{handler!(*(x))} | handler?(y).{done!(*(y))} }")
        .rhs(2, "Proc", "{ handler!(*(request)) | handler?(y).{done!(*(y))} }")
        .where_rate(SpatialBehavior::interaction("server", "server"), 0.7)
        .producing_rate(SpatialBehavior::local("handler"), 0.8)
        .build()
        .unwrap();
    system.add_rule(comm_server);

    // COMM rule on 'handler' channel: rate 0.5
    let comm_handler = RuleBuilder::new("COMM_handler")
        .lhs(2, "Proc", "{ handler!(*(request)) | handler?(y).{done!(*(y))} }")
        .rhs(3, "Proc", "{ done!(*(request)) }")
        .where_rate(SpatialBehavior::interaction("handler", "handler"), 0.5)
        .producing_rate(SpatialBehavior::local("done"), 1.0)
        .build()
        .unwrap();
    system.add_rule(comm_handler);

    // Initial state
    let initial = TermRef::new(
        1,
        "Proc",
        "{ server!(request) | server?(x).{handler!(*(x))} | handler?(y).{done!(*(y))} }",
    );
    let mut initial_map = RateMap::new();
    initial_map.insert(
        SpatialBehavior::interaction("server", "server"),
        RateValue::real(1.0).unwrap(),
    );

    println!("Initial term: {}\n", initial);
    println!("Rules:");
    for rule in &system.rules {
        println!("  {}", rule);
    }
    println!();

    // Run simulation
    let mut sim = Simulator::new(initial, initial_map, system);
    let trace = sim.run(10);

    println!("Simulation trace ({} steps):", trace.num_steps());
    for step in &trace.steps {
        println!("  {}", step);
    }
    println!("\nTotal time: {:.6}", trace.total_time());
}

fn quantum_example() {
    println!("━━━ Quantum Mode (CTMC Model Checking) ━━━\n");

    let s = 1.0 / 2.0_f64.sqrt(); // 1/√2

    let mut system = AugmentedRewriteSystem::new();

    // Quantum COMM on 'server': amplitude 1/√2
    // This creates a superposition of having communicated or not
    let q_comm_server = RuleBuilder::new("Q_COMM_server")
        .lhs(1, "Proc", "{ server!(req) | server?(x).P }")
        .rhs(2, "Proc", "P{req/x}")
        .where_amplitude(SpatialBehavior::interaction("server", "server"), s, 0.0)
        .producing_amplitude(SpatialBehavior::local("server"), s, 0.0)
        .build()
        .unwrap();
    system.add_rule(q_comm_server);

    // Second path with a phase shift: amplitude i/√2
    // This creates interference with the first path
    let q_comm_alt = RuleBuilder::new("Q_COMM_alt")
        .lhs(1, "Proc", "{ server!(req) | server?(x).P }")
        .rhs(3, "Proc", "Q{req/x}")
        .where_amplitude(SpatialBehavior::local("server"), 0.0, s) // i/√2
        .producing_amplitude(SpatialBehavior::local("alt"), 0.0, s)
        .build()
        .unwrap();
    system.add_rule(q_comm_alt);

    let initial = TermRef::new(1, "Proc", "{ server!(req) | server?(x).P }");
    let initial_map = RateMap::new();

    println!("Initial term: {}\n", initial);
    println!("Rules (complex amplitudes):");
    for rule in &system.rules {
        println!("  {}", rule);
    }
    println!();

    // Run quantum simulation
    let mut sim = Simulator::with_mode(
        initial,
        initial_map,
        system,
        SimulatorMode::Quantum,
    );

    let trace = sim.run(5);

    println!("Quantum simulation trace ({} steps):", trace.num_steps());
    for step in &trace.steps {
        println!("  {}", step);
    }
    println!("\nTotal time: {:.6}", trace.total_time());

    // Show measurement distribution
    if let Simulator::Quantum(ref qsim) = sim {
        println!("\nFinal measurement distribution:");
        for (id, term, prob) in qsim.distribution() {
            println!("  [{}] {} → p = {:.6}", id, term, prob);
        }
    }
}
