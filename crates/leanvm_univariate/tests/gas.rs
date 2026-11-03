// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! What a call of the univariate verifier costs, over leanVM's measured shapes, next to the baseline's.
//!
//! `cargo test --release -p leanvm_univariate --test gas -- --ignored --nocapture gas_report`

use leanvm_flock_gas::shapes::{PROGRAM_IV, WORKLOADS};
use leanvm_univariate::{Blake2s, Claims, FLOCK_BIT_SLICE, FLOCK_LEANVM_SKIP, FLOCK_MAIN, FLOCK_REC, Shape};
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
            // Review M1, F3: a proof stack below 2^24 words has no certified level-0 list; such shapes are not
            // reported.
            let proof_stacks = leanvm_univariate::verifier::layouts(&shape);
            if proof_stacks.iter().any(|(c, l)| *c != leanvm_univariate::claims::Commitment::Setup && l.vars < 24) {
                println!("\n({}: a proof stack below 2^24 words, no certified list: not reported)", workload.name);
                continue;
            }
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

/// The deployable build (contracts of at most 24,576 bytes, `crates/evm_link`) returns, word for word, what the Rust
/// verifier computes, for the main line and the extensions.
#[test]
fn deployable_is_the_rust_verifier() {
    deep(|| {
        let shape = Shape::of(&leanvm_flock_gas::shapes::reference().shape);
        for (blake2s, mode) in [
            (Blake2s::Flock(FLOCK_MAIN), Claims::Point),
            (Blake2s::Flock(FLOCK_BIT_SLICE), Claims::Weighted),
        ] {
            let recorded = record_verifier(&shape, blake2s, mode);
            let stream = sample_stream(recorded.stream_len, 11);
            let contracts = leanvm_univariate::contract::parity_deployable(
                &shape,
                &PROGRAM_IV,
                &[0x42; 32],
                &stream,
                blake2s,
                mode,
                leanvm_flock_gas::evm::codegen::MAX_CODE,
            );
            assert!(contracts >= 1);
        }
    });
}

/// π1-rec (`FLOCK_REC`, SPEC-REC.md §1.4): the contract writes, word for word, what the Rust verifier computes, on
/// random streams of the reference shape, in both claim modes.
#[test]
fn rec_contract_is_the_rust_verifier() {
    deep(|| {
        let shape = Shape::of(&leanvm_flock_gas::shapes::reference().shape);
        for mode in [Claims::Point, Claims::Weighted] {
            let recorded = record_verifier(&shape, Blake2s::Flock(FLOCK_REC), mode);
            for seed in [1u64, 2] {
                let stream = sample_stream(recorded.stream_len, seed);
                let public: [u8; 32] = std::array::from_fn(|i| (seed as u8).wrapping_mul(29) ^ i as u8);
                leanvm_univariate::contract::parity(&shape, &PROGRAM_IV, &public, &stream, Blake2s::Flock(FLOCK_REC), mode);
            }
        }
    });
}

/// π1-rec: the deployable build returns, word for word, what the Rust verifier computes.
#[test]
fn rec_deployable_is_the_rust_verifier() {
    deep(|| {
        let shape = Shape::of(&leanvm_flock_gas::shapes::reference().shape);
        let recorded = record_verifier(&shape, Blake2s::Flock(FLOCK_REC), Claims::Point);
        let stream = sample_stream(recorded.stream_len, 13);
        let contracts = leanvm_univariate::contract::parity_deployable(
            &shape,
            &PROGRAM_IV,
            &[0x24; 32],
            &stream,
            Blake2s::Flock(FLOCK_REC),
            Claims::Point,
            leanvm_flock_gas::evm::codegen::MAX_CODE,
        );
        assert!(contracts >= 1);
    });
}

/// π1-rec's gas next to the main line's, at the reference shape, straight and deployed.
/// `cargo test --release -p leanvm_univariate --test gas -- --ignored --nocapture rec_gas_report`
#[test]
#[ignore]
fn rec_gas_report() {
    deep(|| {
        let shape = Shape::of(&leanvm_flock_gas::shapes::reference().shape);
        println!(
            "| variant | calldata bytes | KECCAK256 (bytes) | FIELD_MUL | execution, straight | deployed (contracts) | tx \
             EIP-7623, c = 0, straight / deployed |"
        );
        println!("|---|---:|---:|---:|---:|---:|---:|");
        for (name, variant) in [("main line (FLOCK_MAIN)", FLOCK_MAIN), ("π1-rec (FLOCK_REC)", FLOCK_REC)] {
            let d = leanvm_univariate::contract::measure_deployable(
                &shape,
                &PROGRAM_IV,
                Blake2s::Flock(variant),
                Claims::Point,
                leanvm_flock_gas::evm::codegen::MAX_CODE,
            );
            let r = measure(&shape, &PROGRAM_IV, Blake2s::Flock(variant), Claims::Point);
            println!(
                "| {name} | {} | {} ({}) | {} | {} | {} ({}) | {} / {} |",
                grouped(r.calldata_bytes as u64),
                r.hashes,
                grouped(r.hashed_bytes as u64),
                grouped(r.field_muls as u64),
                grouped(d.straight),
                grouped(d.report.execution),
                d.contracts.len(),
                grouped(r.transaction(0, 40)),
                grouped(d.report.transaction(0, 40)),
            );
            print_report(name, &r);
        }
    });
}

/// The straight contract's instructions by phase: how many of each kind, and the gas per `FIELD_MUL` (the code
/// generator's overhead). `cargo test --release -p leanvm_univariate --test gas -- --ignored --nocapture op_report`
#[test]
#[ignore]
fn op_report() {
    use leanvm_flock_gas::evm::codegen::MEASURE;
    use leanvm_univariate::contract::compile_verifier;
    deep(|| {
        let shape = Shape::of(&leanvm_flock_gas::shapes::reference().shape);
        for (name, blake2s, mode) in [
            ("ABI point claims, Flock (a')", Blake2s::Flock(FLOCK_MAIN), Claims::Point),
            ("weighted claims [ext. W], Flock (a) [ext. B]", Blake2s::Flock(FLOCK_BIT_SLICE), Claims::Weighted),
        ] {
            let recorded = record_verifier(&shape, blake2s, mode);
            let contract = compile_verifier(&recorded, &PROGRAM_IV, true);
            // Kinds: FIELD_MUL, XOR, MLOAD, MSTORE, PUSH, DUP, SWAP, CALLDATALOAD, other.
            let mut by_phase: Vec<(&'static str, [u64; 9])> = Vec::new();
            let mut pc = 0;
            while pc < contract.code.len() {
                let op = contract.code[pc];
                let phase = contract.phase_of[pc];
                let kind = match op {
                    0x0c => 0,
                    0x18 => 1,
                    0x51 => 2,
                    0x52 => 3,
                    0x5f..=0x7f => 4,
                    0x80..=0x8f => 5,
                    0x90..=0x9f => 6,
                    0x35 => 7,
                    _ => 8,
                };
                match by_phase.iter_mut().find(|(p, _)| *p == phase) {
                    Some((_, counts)) => counts[kind] += 1,
                    None => {
                        let mut counts = [0; 9];
                        counts[kind] = 1;
                        by_phase.push((phase, counts));
                    }
                }
                pc += 1 + if (0x60..=0x7f).contains(&op) { (op - 0x5f) as usize } else { 0 };
            }
            by_phase.retain(|(p, _)| *p != MEASURE);
            by_phase.sort_by_key(|(_, c)| std::cmp::Reverse(c[0] * 10 + c[1..].iter().sum::<u64>() * 3));
            println!("\n### {name}: instructions by phase (straight contract)");
            println!("| phase | FIELD_MUL | XOR | MLOAD | MSTORE | PUSH | DUP | SWAP | CALLDATALOAD | other | gas/FIELD_MUL (approx.) |");
            println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
            let mut total = [0u64; 9];
            for (phase, c) in &by_phase {
                for k in 0..9 {
                    total[k] += c[k];
                }
                let approx = 10 * c[0] + 3 * c[1..8].iter().sum::<u64>() + 3 * c[8];
                let per = if c[0] > 0 { format!("{:.1}", approx as f64 / c[0] as f64) } else { "-".into() };
                println!(
                    "| {phase} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {per} |",
                    c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7], c[8]
                );
            }
            let approx = 10 * total[0] + 3 * total[1..].iter().sum::<u64>();
            println!(
                "| **total** | {} | {} | {} | {} | {} | {} | {} | {} | {} | {:.1} |",
                total[0],
                total[1],
                total[2],
                total[3],
                total[4],
                total[5],
                total[6],
                total[7],
                total[8],
                approx as f64 / total[0] as f64
            );
        }
    });
}

/// `cargo test --release -p leanvm_univariate --test gas -- --ignored --nocapture deployable_report`
#[test]
#[ignore]
fn deployable_report() {
    deep(|| {
        let shape = Shape::of(&leanvm_flock_gas::shapes::reference().shape);
        for (name, blake2s, mode) in [
            ("ABI point claims, Flock (a')", Blake2s::Flock(FLOCK_MAIN), Claims::Point),
            ("ABI point claims, Flock (a) [ext. B]", Blake2s::Flock(FLOCK_BIT_SLICE), Claims::Point),
            ("weighted claims [ext. W], Flock (a')", Blake2s::Flock(FLOCK_MAIN), Claims::Weighted),
            ("weighted claims [ext. W], Flock (a) [ext. B]", Blake2s::Flock(FLOCK_BIT_SLICE), Claims::Weighted),
            ("ABI point claims, no BLAKE2s argument", Blake2s::Omitted, Claims::Point),
            ("weighted claims [ext. W], no BLAKE2s argument", Blake2s::Omitted, Claims::Weighted),
        ] {
            let d = leanvm_univariate::contract::measure_deployable(
                &shape,
                &PROGRAM_IV,
                blake2s,
                mode,
                leanvm_flock_gas::evm::codegen::MAX_CODE,
            );
            let sizes: Vec<String> = d.contracts.iter().map(|c| grouped(c.code_bytes as u64)).collect();
            let deployment: u64 = d.contracts.iter().map(|c| c.deployment_tx).sum();
            println!(
                "| {name} | {} | {} | +{} | {} contracts: {} bytes | {} | {} / {} / {} / {} | {} / {} |",
                grouped(d.straight),
                grouped(d.report.execution),
                grouped(d.report.execution - d.straight),
                d.contracts.len(),
                sizes.join(", "),
                grouped(deployment),
                grouped(d.report.transaction(0, 40)),
                grouped(d.report.transaction(2_000, 40)),
                grouped(d.report.transaction(5_000, 40)),
                grouped(d.report.transaction(20_000, 40)),
                grouped(d.report.transaction(0, 64)),
                grouped(d.report.transaction(20_000, 64)),
            );
        }
    });
}
