// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! SPEC-REC.md §2: the Merkle-path quotient SNARK (`crates/quotient`) as `π2`'s reference: its rows per Keccak-f,
//! the membership circuit's use of its `2^22` rows, and its commitments' words per row.
//!
//! `cargo test --release -p leanvm_rec --test quotient_reference -- --nocapture`

use quotient::circuit::{Builder, PUBLIC_ROWS, Src, membership};
use quotient::protocol::{MAX_LOG_ROWS, quotient_layout, wiring_layout, witness_layout};
use quotient::statement::DEPTH;

#[test]
fn the_merkle_path_circuit_per_keccak_f() {
    let mut b = Builder::new();
    let message: Vec<Src> = (0..512).map(|_| b.input()).collect();
    let before = b.len();
    let _ = b.keccak256_64(&message);
    let per_permutation = b.len() - before;
    let circuit = membership();
    let hashes = 2 + DEPTH;
    let rows = 1usize << circuit.log_rows;
    println!("rows per Keccak-f[1600] (one Keccak-256 of a 64-byte block): {per_permutation}");
    println!(
        "membership: {hashes} permutations, {} rows used of 2^{} = {rows} ({:.1}%), {} public rows, {} free input bits",
        circuit.used_rows,
        circuit.log_rows,
        100.0 * circuit.used_rows as f64 / rows as f64,
        PUBLIC_ROWS,
        circuit.n_inputs()
    );
    let m = MAX_LOG_ROWS;
    let (wit, wir, quo) = (
        witness_layout(m).placed(),
        wiring_layout(m).placed(),
        quotient_layout(m).placed(),
    );
    let r = 1usize << m;
    println!(
        "at 2^{m} rows (4 cells a row): witness {wit} words (2^{:.2}, {:.2} a row, hidden), wiring {wir} (2^{:.2}, {:.2} a \
         row), quotient {quo} (2^{:.2}, {:.2} a row, hidden); permutations at most {}",
        (wit as f64).log2(),
        wit as f64 / r as f64,
        (wir as f64).log2(),
        wir as f64 / r as f64,
        (quo as f64).log2(),
        quo as f64 / r as f64,
        (rows - PUBLIC_ROWS) / per_permutation
    );
    assert!(circuit.used_rows <= rows);
}
