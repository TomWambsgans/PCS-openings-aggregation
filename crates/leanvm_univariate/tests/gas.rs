// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! What a call of the univariate verifier costs, over leanVM's measured shapes, next to the baseline's.
//!
//! `cargo test --release -p leanvm_univariate --test gas -- --ignored --nocapture gas_report`

use leanvm_flock_gas::shapes::{PROGRAM_IV, WORKLOADS};
use leanvm_univariate::{Blake2s, Claims, FLOCK_BIT_SLICE, FLOCK_LEANVM_SKIP, FLOCK_MAIN, Shape};
use leanvm_univariate::contract::{GasReport, measure, rust_verifier, record_verifier, sample_stream};

/// Run `f` on a thread with a deep stack: the code generator recurses along the graph.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn grouped(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, digit) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(digit);
    }
    out
}

fn print_report(name: &str, report: &GasReport) {
    println!("\n### {name}");
    println!(
        "calldata {} bytes ({} zero), stream {} bytes; code {} bytes; FIELD_MUL {}, XOR {}, KECCAK256 {} ({} bytes), \
         checks {}, memory {} words; PCS_OPEN {} claims in {} calls, {} words written, {} relations combined",
        grouped(report.calldata_bytes as u64),
        report.calldata_zero_bytes,
        grouped(report.stream_bytes as u64),
        grouped(report.code_bytes as u64),
        grouped(report.field_muls as u64),
        grouped(report.xors as u64),
        report.hashes,
        grouped(report.hashed_bytes as u64),
        report.checks,
        grouped(report.memory_words as u64),
        report.claims,
        report.calls,
        grouped(report.pcs_words as u64),
        report.relations,
    );
    for (name, terms, words) in &report.terms {
        println!("  claim on {name}: {terms} terms, {words} words");
    }
    println!("| part | execution gas |");
    println!("|---|---:|");
    for phase in &report.phases {
        println!("| {} | {} |", phase.phase, grouped(phase.gas));
    }
    println!("| **execution** | **{}** |", grouped(report.execution));
    println!("| calldata (16/4 a byte) | {} |", grouped(report.calldata_gas()));
    println!();
    println!("| c | execution | tx EIP-7623 (−21,000) | tx EIP-7976 (−21,000) |");
    println!("|---:|---:|---:|---:|");
    for c in [0, 2_000, 5_000, 20_000] {
        println!(
            "| {} | {} | {} | {} |",
            grouped(c),
            grouped(report.execution_at(c)),
            grouped(report.transaction(c, 40)),
            grouped(report.transaction(c, 64))
        );
    }
    println!();
    println!("| stream read by | bytes | scalars (24 B; a root 32 B) |");
    println!("|---|---:|---:|");
    for &(phase, bytes) in &report.stream_by_phase {
        println!("| {phase} | {} | {} |", grouped(bytes as u64), bytes / 24);
    }
}

/// `cargo test --release -p leanvm_univariate --test gas -- --ignored --nocapture gas_report`
#[test]
#[ignore]
fn gas_report() {
    deep(|| {
        let variants = [
            ("ABI point claims, Flock (a')", Blake2s::Flock(FLOCK_MAIN), Claims::Point),
            ("ABI point claims, Flock (a) [ext. B]", Blake2s::Flock(FLOCK_BIT_SLICE), Claims::Point),
            ("weighted claims [ext. W], Flock (a')", Blake2s::Flock(FLOCK_MAIN), Claims::Weighted),
            ("weighted claims [ext. W], Flock (a) [ext. B]", Blake2s::Flock(FLOCK_BIT_SLICE), Claims::Weighted),
            ("ABI point claims, Flock leanVM's skip 6", Blake2s::Flock(FLOCK_LEANVM_SKIP), Claims::Point),
            ("ABI point claims, no BLAKE2s argument", Blake2s::Omitted, Claims::Point),
            ("weighted claims [ext. W], no BLAKE2s argument", Blake2s::Omitted, Claims::Weighted),
        ];
        let mut rows = Vec::new();
        for workload in &WORKLOADS {
            let shape = Shape::of(&workload.shape);
            for (name, blake2s, mode) in variants {
                let report = measure(&shape, &PROGRAM_IV, blake2s, mode);
                if workload.xmss == 1000 {
                    print_report(&format!("{}, {name}", workload.name), &report);
                }
                rows.push((workload, name, report));
            }
        }
        println!("\n### Over the shapes (transaction gas without the 21,000 base)");
        println!(
            "| signatures | cycles | variant | calldata bytes | execution (c = 0) | claims / calls | tx EIP-7623, c = 0 / \
             2,000 / 5,000 / 20,000 | tx EIP-7976, c = 0 / 20,000 |"
        );
        println!("|---:|---:|---|---:|---:|---:|---|---|");
        for (workload, name, report) in &rows {
            let tx = |c, floor| grouped(report.transaction(c, floor));
            println!(
                "| {} | {} | {} | {} | {} | {} / {} | {} / {} / {} / {} | {} / {} |",
                grouped(workload.xmss as u64),
                grouped(workload.cycles),
                name,
                grouped(report.calldata_bytes as u64),
                grouped(report.execution),
                report.claims,
                report.calls,
                tx(0, 40),
                tx(2_000, 40),
                tx(5_000, 40),
                tx(20_000, 40),
                tx(0, 64),
                tx(20_000, 64),
            );
        }
    });
}

/// The Rust verifier reads exactly the stream the recorded contract is built for, on random streams of every shape.
#[test]
fn rust_verifier_reads_the_recorded_stream() {
    deep(|| {
        for workload in &WORKLOADS {
            let shape = Shape::of(&workload.shape);
            for mode in [Claims::Point, Claims::Weighted] {
                let recorded = record_verifier(&shape, Blake2s::Flock(FLOCK_MAIN), mode);
                let stream = sample_stream(recorded.stream_len, 7);
                let (reduced, _, _) =
                    rust_verifier(&shape, &PROGRAM_IV, &[3; 32], &stream, Blake2s::Flock(FLOCK_MAIN), mode)
                        .expect("the stream's length");
                assert_eq!(reduced.openings.len(), recorded.reduced.openings.len(), "{}", workload.name);
            }
        }
    });
}

/// The contract writes, word for word, the claims the Rust verifier makes on the same calldata, and checks the same
/// values: on random streams of the reference shape, with and without Flock.
#[test]
fn contract_is_the_rust_verifier() {
    deep(|| {
        let workload = leanvm_flock_gas::shapes::reference();
        let shape = Shape::of(&workload.shape);
        for blake2s in [Blake2s::Flock(FLOCK_MAIN), Blake2s::Flock(FLOCK_BIT_SLICE), Blake2s::Omitted] {
            for mode in [Claims::Point, Claims::Weighted] {
                let recorded = record_verifier(&shape, blake2s, mode);
                for seed in [1u64, 2] {
                    let stream = sample_stream(recorded.stream_len, seed);
                    let public: [u8; 32] = std::array::from_fn(|i| (seed as u8).wrapping_mul(31) ^ i as u8);
                    leanvm_univariate::contract::parity(&shape, &PROGRAM_IV, &public, &stream, blake2s, mode);
                }
            }
        }
    });
}
