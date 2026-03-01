//! # Example: Fuzzing the Rho-Calculus
//!
//! Generates random rho-calculus programs using weighted productions,
//! then optionally feeds them into the Gillespie simulator.

use mettail_gillespie::fuzzer::*;

fn main() {
    println!("═══════════════════════════════════════════════════════════");
    println!("  MeTTaIL Weighted Fuzzer — Rho-Calculus Demo");
    println!("═══════════════════════════════════════════════════════════\n");

    // Use the built-in rho-calculus spec
    let spec = rhocalc_spec();
    println!("Language: {}", spec.name);
    println!("Sorts: {:?}", spec.sorts);
    println!(
        "Productions: {}",
        spec.productions
            .iter()
            .map(|p| format!("{}:{} [w={:.1}]", p.name, p.result_sort, p.weight))
            .collect::<Vec<_>>()
            .join(", ")
    );

    // ── Depth 0: only base cases ──────────────────────────────────────
    println!("\n━━━ Depth 0 (base cases only) ━━━\n");
    let mut fuzzer = Fuzzer::new(&spec);
    let terms = fuzzer.generate("Proc", 0, 5);
    for (i, term) in terms.iter().enumerate() {
        println!("  [{}] {} (depth={}, size={})", i, term, term.depth(), term.size());
    }

    // ── Depth 2: small terms ──────────────────────────────────────────
    println!("\n━━━ Depth 2 (small terms) ━━━\n");
    let terms = fuzzer.generate("Proc", 2, 10);
    for (i, term) in terms.iter().enumerate() {
        println!("  [{}] {} (depth={}, size={})", i, term, term.depth(), term.size());
    }

    // ── Depth 5: complex terms with statistics ────────────────────────
    println!("\n━━━ Depth 5 (complex terms, k=100) ━━━\n");
    let (terms, stats) = fuzzer.generate_with_stats("Proc", 5, 100);

    // Show first 10
    println!("First 10 terms:");
    for (i, term) in terms.iter().take(10).enumerate() {
        println!("  [{}] {} (depth={}, size={})", i, term, term.depth(), term.size());
    }

    println!("\nStatistics:");
    println!("  Count: {}", stats.count);
    println!(
        "  Depth: min={}, max={}, mean={:.2}",
        stats.min_depth, stats.max_depth, stats.mean_depth
    );
    println!(
        "  Size:  min={}, max={}, mean={:.2}",
        stats.min_size, stats.max_size, stats.mean_size
    );
    println!("\n  Production usage:");
    let mut prods: Vec<_> = stats.production_distribution.iter().collect();
    prods.sort_by(|a, b| b.1.cmp(a.1));
    for (name, count) in prods {
        println!("    {}: {} times", name, count);
    }

    // ── Custom weights: heavily bias toward POutput ───────────────────
    println!("\n━━━ Custom weights (POutput=50.0) ━━━\n");
    let custom_spec = LanguageSpec::new("RhoCalc-OutputHeavy")
        .add_type("Proc")
        .add_type("Name")
        .add_production(Production::new("PZero", "Proc").weight(3.0))
        .add_production(
            Production::new("POutput", "Proc")
                .child("n", "Name")
                .child("q", "Proc")
                .weight(50.0),
        )
        .add_production(
            Production::new("PInput", "Proc")
                .child("n", "Name")
                .binder("x", "Name", "p", "Proc")
                .weight(2.0),
        )
        .add_production(
            Production::new("NQuote", "Name")
                .child("p", "Proc")
                .weight(5.0),
        );

    let mut custom_fuzzer = Fuzzer::new(&custom_spec);
    let (terms, stats) = custom_fuzzer.generate_with_stats("Proc", 3, 50);

    println!("First 5 terms:");
    for (i, term) in terms.iter().take(5).enumerate() {
        println!("  [{}] {}", i, term);
    }

    println!("\n  Production usage:");
    let mut prods: Vec<_> = stats.production_distribution.iter().collect();
    prods.sort_by(|a, b| b.1.cmp(a.1));
    for (name, count) in prods {
        println!("    {}: {} times", name, count);
    }

    // ── Bridge to simulator ───────────────────────────────────────────
    println!("\n━━━ Fuzz → Simulate pipeline ━━━\n");
    let mut fuzzer = Fuzzer::new(&spec);
    let terms = fuzzer.generate("Proc", 3, 3);
    for (i, term) in terms.iter().enumerate() {
        let term_ref = fuzz_term_to_term_ref(term, i as u64);
        println!("  TermRef {{ id: {}, sort: {}, display: {} }}", term_ref.id, term_ref.sort, term_ref.display);
    }
    println!("\n  (These TermRefs can be fed directly into the Gillespie simulator)");
}
