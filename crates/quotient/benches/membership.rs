// Part of this repository. The harness (`bench`, the allocator, tracing) is leanVM's
// (https://github.com/leanEthereum/leanVM, commit c445e3d5), MIT OR Apache-2.0; see NOTICE.md.
//! One membership proof, timed stage by stage, with its sizes and the prover's peak memory.
//!
//! `cargo bench -p quotient --bench membership`; `TRACING=1` for the span tree.

use std::time::Instant;

use fiat_shamir::transcript::Proof as WhirProof;
use primitives::test_rng::Rng;
use quotient::circuit::{membership, membership_inputs};
use quotient::opening::commit;
use quotient::protocol::{Index, Randomness, digest, open, prove_with_randomness, verify, verify_openings};
use quotient::statement::{DEPTH, Secret};

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

fn opening_bytes(proof: &WhirProof) -> usize {
    24 * proof.stream.len()
        + proof
            .merkle
            .iter()
            .map(|m| 32 * m.sibling_hashes.len() + m.leaf_data.iter().map(|row| 8 * row.len()).sum::<usize>())
            .sum::<usize>()
}

fn main() {
    bench::init_tracing_from_env();
    let mut rng = Rng::new(0x5EC);
    let time = |label: &str, start: Instant| {
        let secs = start.elapsed().as_secs_f64();
        println!("{label:<34}: {secs:>8.3} s");
        secs
    };

    let start = Instant::now();
    let circuit = membership();
    time("circuit", start);
    println!(
        "{:<34}: {} of {} ({:.1}%)",
        "rows used",
        circuit.used_rows,
        1usize << circuit.log_rows,
        100.0 * circuit.used_rows as f64 / (1usize << circuit.log_rows) as f64
    );
    // The peak resident set so far: it only grows, so read after each stage it says which one reached it.
    let peak = || bench::peak_rss_bytes() as f64 / f64::powi(1024.0, 3);
    let start = Instant::now();
    let index = Index::new(&circuit);
    let index_committed = commit(&index.table);
    time("index (wiring table, committed)", start);
    let peak_index = peak();

    let secret = Secret {
        x: std::array::from_fn(|_| rng.next_u64() as u8),
        siblings: std::array::from_fn::<_, DEPTH, _>(|_| std::array::from_fn(|_| rng.next_u64() as u8)),
        directions: rng.next_u64() as u32,
    };
    let statement = secret.statement();
    // The proof's seed, from the test generator so that the proof digest repeats: `prove` draws a fresh one from
    // the operating system. The randomness is derived from it as `prove` derives it, in the timed stage.
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);

    let start = Instant::now();
    let cells = circuit.cells(&membership_inputs(&secret));
    let witness_secs = time("witness (cells)", start);
    let start = Instant::now();
    let randomness = Randomness::derive(&seed, &index_committed.root, &statement, &cells);
    let proved = prove_with_randomness(&circuit, &index, &index_committed.root, &statement, &cells, &randomness);
    let reduction_secs = time("reduction (commit both tables)", start);
    let peak_reduction = peak();
    assert!(proved.fits);
    let start = Instant::now();
    let openings = open(proved.tables, &proved.claims, &index, &index_committed);
    let opening_secs = time("openings (three WHIR)", start);
    let peak_openings = peak();
    println!(
        "{:<34}: {:>8.3} s",
        "prover total (witness .. openings)",
        witness_secs + reduction_secs + opening_secs
    );

    let start = Instant::now();
    let (roots, claims) = verify(&index_committed.root, &statement, &proved.proof, circuit.log_rows).expect("accepts");
    time("verify: reduction", start);
    assert_eq!(roots, proved.roots);
    let start = Instant::now();
    verify_openings(circuit.log_rows, &index_committed.root, &roots, &claims, &openings).expect("openings hold");
    time("verify: openings", start);

    println!(
        "{:<34}: {} bytes (statement 64, two roots, {} field elements)",
        "calldata",
        64 + 64 + 24 * (proved.proof.stream.len() - 4),
        proved.proof.stream.len() - 4
    );
    for (name, proof) in [
        ("opening: witness", &openings.witness),
        ("opening: wiring", &openings.wiring),
        ("opening: quotient (two claims)", &openings.quotient),
    ] {
        println!("{name:<34}: {:.1} KiB", opening_bytes(proof) as f64 / 1024.0);
    }
    // Pinned by hand: `dfcbadec8510a4f447488cef75b7c0b12ac17d40bdb4114a181e0df1c27a63e2` since the hidden layouts
    // took the gadget (HIDING.md); `b93236c8…` before, since the randomness is derived from one seed and the
    // openings' transcripts have leanVM's shape; `2d6342b8…fcb` before that.
    let hex: String = digest(&proved.proof, &openings)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    println!("{:<34}: {hex}", "proof digest");
    println!(
        "{:<34}: {peak_index:.2} / {peak_reduction:.2} / {peak_openings:.2} GiB",
        "peak after index / reduction / open"
    );
    println!("{:<34}: {:.2} GiB", "peak memory", peak());
}
