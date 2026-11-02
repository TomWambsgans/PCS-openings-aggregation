// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The port is leanVM's verifier: it accepts the proofs leanVM 42422001 makes, and rejects them tampered.
//!
//! The proofs are made by leanVM itself (`dump/apply.sh`, `README.md`): set `LEANVM_DUMP` to the directory holding one
//! subdirectory per proof (`bytecode.bin`, `public_input.bin`, `stream.bin`, `merkle.bin`) and run
//! `cargo test --release -p leanvm_flock_gas --test real_proofs -- --ignored --nocapture`.

use leanvm_flock_gas::shapes::{PROGRAM_IV, WORKLOADS};
use leanvm_flock_gas::{Bytecode, Proof, VerifierError, verify_execution};

fn read(dir: &std::path::Path, name: &str) -> Vec<u8> {
    std::fs::read(dir.join(name)).unwrap_or_else(|e| panic!("{}/{name}: {e}", dir.display()))
}

#[test]
#[ignore]
fn accepts_real_leanvm_proofs() {
    let Ok(root) = std::env::var("LEANVM_DUMP") else {
        println!("LEANVM_DUMP (the directory of leanVM's dumped proofs) is not set: nothing to check");
        return;
    };
    let mut dirs: Vec<_> = std::fs::read_dir(&root)
        .expect("a directory")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| path.join("stream.bin").exists())
        .collect();
    dirs.sort();
    assert!(!dirs.is_empty(), "no proof in {root}");
    // One program, the aggregation guest, whatever the signatures: a proof's directory may leave its bytecode out.
    let shared = dirs
        .iter()
        .find(|dir| dir.join("bytecode.bin").exists())
        .expect("a bytecode.bin")
        .clone();
    let mut bytecode: Option<(Vec<u8>, Bytecode)> = None;
    for dir in dirs {
        let words_bytes = match dir.join("bytecode.bin").exists() {
            true => read(&dir, "bytecode.bin"),
            false => read(&shared, "bytecode.bin"),
        };
        if bytecode.as_ref().is_none_or(|(bytes, _)| *bytes != words_bytes) {
            let words: Vec<u64> = words_bytes
                .as_chunks::<8>()
                .0
                .iter()
                .map(|w| u64::from_le_bytes(*w))
                .collect();
            bytecode = Some((words_bytes, Bytecode::new(&words)));
        }
        let program = &bytecode.as_ref().expect("a bytecode").1;
        let public_input: [u8; 32] = read(&dir, "public_input.bin").try_into().expect("32 bytes");
        let proof = Proof::load(&read(&dir, "stream.bin"), &read(&dir, "merkle.bin")).expect("a proof");
        let started = std::time::Instant::now();
        let (shape, _) = verify_execution(program, &public_input, &proof).expect("leanVM's proof verifies");
        println!(
            "{}: verified in {:.1} ms, shape {shape:?}",
            dir.display(),
            started.elapsed().as_secs_f64() * 1e3
        );
        println!("  program IV {:02x?}", program.fiat_shamir_iv());
        assert_eq!(program.fiat_shamir_iv(), PROGRAM_IV, "the aggregation guest's IV");
        if let Some(workload) = WORKLOADS.iter().find(|w| w.shape == shape) {
            assert_eq!(proof.stream.len(), workload.stream_elements, "{}", workload.name);
        } else {
            println!("  (no workload of this shape in shapes.rs)");
        }

        // Tampered: a scalar of the PIOP (a GKR message), of the flock reduction, and of the opening.
        for at in [40, 700, proof.stream.len() - 3] {
            let mut tampered = proof.clone();
            tampered.stream[at].c1 ^= 1;
            let verdict = verify_execution(program, &public_input, &tampered);
            assert!(verdict.is_err(), "scalar {at} tampered");
            println!("  scalar {at} tampered: {:?}", verdict.err());
        }
        let mut other = public_input;
        other[3] ^= 1;
        assert!(matches!(
            verify_execution(program, &other, &proof),
            Err(VerifierError::GkrLayer(_) | VerifierError::TableSumcheckTerminal | VerifierError::WhirTerminal)
                | Err(_)
        ));
    }
}
