// Part of this repository. The harness (`bench`, the allocator, tracing) is leanVM's
// (https://github.com/leanEthereum/leanVM, commit c445e3d5), MIT OR Apache-2.0; see NOTICE.md.
//! One membership proof, timed stage by stage, with its sizes and the prover's peak memory.
//!
//! `cargo bench -p quotient --bench membership`; `TRACING=1` for the span tree.

use std::time::Instant;

use fiat_shamir::transcript::Proof as WhirProof;
use primitives::field::F64;
use primitives::test_rng::Rng;
use quotient::circuit::{membership, membership_inputs};
use quotient::opening::commit;
use quotient::protocol::{Index, open, prove, verify, verify_openings};
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
    let start = Instant::now();
    let index = Index::new(&circuit);
    let index_committed = commit(&index.table);
    time("index (wiring table, committed)", start);

    let secret = Secret {
        x: std::array::from_fn(|_| rng.next_u64() as u8),
        siblings: std::array::from_fn::<_, DEPTH, _>(|_| std::array::from_fn(|_| rng.next_u64() as u8)),
        directions: rng.next_u64() as u32,
    };
    let statement = secret.statement();
    let masks = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));

    let start = Instant::now();
    let cells = circuit.cells(&membership_inputs(&secret));
    let witness_secs = time("witness (cells)", start);
    let start = Instant::now();
    let proved = prove(&circuit, &index, &index_committed.root, &statement, &cells, &masks);
    let reduction_secs = time("reduction (commit both tables)", start);
    assert!(proved.fits);
    let start = Instant::now();
    let openings = open(&proved, &index, &index_committed);
    let opening_secs = time("openings (three WHIR)", start);
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
    println!(
        "{:<34}: {:.2} GiB",
        "peak memory",
        bench::peak_rss_bytes() as f64 / f64::powi(1024.0, 3)
    );
}
