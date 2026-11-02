// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The contract computes what the Rust verifier computes, and what a call of it costs.

use leanvm_flock_gas::LincheckTerminal;
use leanvm_flock_gas::evm::contract::{GasReport, measure, parity, record_verifier, sample_stream};
use leanvm_flock_gas::shapes::{PROGRAM_IV, WORKLOADS, benchmark};

/// Run `f` on a thread with a deep stack: the code generator recurses along the graph.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// On streams of the benchmark's shape, the contract (without its calls, returning the claims and every value it
/// checks) and the Rust verifier on the Keccak chain agree word for word: the claims for `PCS_OPEN`, and every
/// identity's residual.
#[test]
fn contract_is_the_rust_verifier() {
    deep(|| {
        let shape = benchmark().shape;
        let recorded = record_verifier(&shape, LincheckTerminal::Matrices);
        for seed in [1, 2, 3] {
            let stream = sample_stream(&shape, &recorded, seed);
            let public_input: [u8; 32] = std::array::from_fn(|i| (seed as u8).wrapping_mul(31) ^ i as u8);
            parity(&shape, &PROGRAM_IV, &public_input, &stream, LincheckTerminal::Matrices);
        }
    });
}

/// The contract reads leanVM's PIOP stream (the real proofs' length, `shapes.rs`) and what it adds: the bytecode's
/// value, the matrices' reduction (12 rounds of two scalars, then two values) and the stack's batching sumcheck (two
/// scalars a round, then the value). A root is 32 bytes, a scalar 24.
#[test]
fn stream_is_leanvms_and_the_additions() {
    deep(|| {
        for workload in &WORKLOADS {
            for (lincheck, matrices) in [(LincheckTerminal::Matrices, 2 * 12 + 2), (LincheckTerminal::Walk, 0)] {
                let recorded = record_verifier(&workload.shape, lincheck);
                let stack_log = recorded.reduced.layout_stack_log;
                let scalars = workload.piop_elements - 2 + 1 + matrices + 2 * stack_log + 1;
                assert_eq!(recorded.stream_len, 32 + 24 * scalars, "{} {lincheck:?}", workload.name);
            }
        }
    });
}

/// The same with the lincheck's terminal walked in the contract, as leanVM's verifier does.
#[test]
#[ignore]
fn walking_contract_is_the_rust_verifier() {
    deep(|| {
        let shape = benchmark().shape;
        let recorded = record_verifier(&shape, LincheckTerminal::Walk);
        let stream = sample_stream(&shape, &recorded, 7);
        parity(&shape, &PROGRAM_IV, &[0x42; 32], &stream, LincheckTerminal::Walk);
    });
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
         checks {}, memory {} words; PCS_OPEN {} claims in {} calls",
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
    );
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
}

/// What a call costs: `cargo test --release -p leanvm_flock_gas --test evm -- --ignored --nocapture gas_report`.
#[test]
#[ignore]
fn gas_report() {
    deep(|| {
        for workload in &WORKLOADS {
            for lincheck in [LincheckTerminal::Matrices, LincheckTerminal::Walk] {
                let report = measure(&workload.shape, &PROGRAM_IV, lincheck);
                print_report(&format!("{} ({:?})", workload.name, lincheck), &report);
            }
        }
    });
}
