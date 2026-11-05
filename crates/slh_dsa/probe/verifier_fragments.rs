// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Probe for `crates/slh_dsa/SPEC-FAST.md` (appendix A): the size of the hash arguments' verifiers at SLH-DSA's
//! scale (4,096 = 2^12 Keccak-f), measured the way `keccak_estimate` measures them at 2^18. Not part of the build:
//! copy it to `crates/leanvm_flock_gas/tests/` and run
//! `cargo test --release -p leanvm_flock_gas --test verifier_fragments -- --ignored --nocapture`.

use leanvm_flock_gas::evm::contract::{FragmentGas, measure_fragment};
use leanvm_flock_gas::keccak_gkr::{KeccakShape, STATE_LANES, verify_keccak};
use leanvm_flock_gas::flock_min::{self, Slices, Variant};
use leanvm_flock_gas::transcript::{Channel, FsShape};
use leanvm_flock_gas::{LincheckTerminal, verify_flock};

fn deep<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new().stack_size(1 << 30).spawn(f).unwrap().join().unwrap()
}

/// Keccak-f permutations of a Keccak-256 chain that hashed `hashes` times `stream` bytes besides the 32-byte states:
/// each call's 32-byte state plus its share of the stream, 136 bytes a block (an estimate: the calls' shares are
/// not recorded, so the stream is taken as spread evenly).
fn perms(f: &FragmentGas) -> usize {
    let per = f.stream_bytes as f64 / f.hashes.max(1) as f64;
    (f.hashes as f64 * ((32.0 + per + 1.0) / 136.0).ceil()) as usize
}

fn show(name: &str, f: &FragmentGas) {
    println!(
        "{name}: stream {} B ({} scalars), KECCAK256 {}, ~Keccak-f {}, FIELD_MUL {}, XOR {}, execution {}",
        f.stream_bytes,
        f.stream_bytes / 24,
        f.hashes,
        perms(f),
        f.field_muls,
        f.xors,
        f.execution
    );
}

#[test]
#[ignore]
fn slh_scale_fragments() {
    deep(|| {
        // Flock (BLAKE2s block, k_log 14) at log_n = 26 and 28: Keccak-f blocks at k_log 16 and 2^12 blocks give
        // log_n = 28 with two more lincheck rounds than this.
        for log_n in [26, 28, 32] {
            let flock = measure_fragment(|recorder| {
                let flock = verify_flock(log_n, recorder, LincheckTerminal::Walk).expect("recorded");
                [flock.point(), flock.s.clone()].concat()
            });
            show(&format!("Flock 42422001, log_n {log_n}, walk"), &flock);
        }
        // π1-rec3's Flock shape (skip 3, slices sent, the lincheck terminal walked, eq point by squares) at
        // log_n 28..30: what π2 proves (the walk here is BLAKE2s's; the Keccak block's terminal replaces it).
        for log_n in [28, 29, 30] {
            let variant = Variant { skip: 3, slices: Slices::TowerWalk, fs: FsShape::Rec3 };
            let flock = measure_fragment(|recorder| {
                let (point, end) = flock_min::verify_walked(log_n, variant, recorder).expect("recorded");
                let mut outputs = point;
                match end {
                    flock_min::End::Ring { map, target, .. } => outputs.extend(map.into_iter().chain([target])),
                    flock_min::End::Combination { weights, value } => outputs.extend(weights.into_iter().chain([value])),
                }
                outputs
            });
            show(&format!("Flock rec3 shape, log_n {log_n}"), &flock);
        }
        // leanVM 4af2cddd's Keccak GKR on 2^12 and 2^18 permutations, depth 12 (its own) and 24 (one segment).
        for (log_rows, depth) in [(12, 12), (12, 24), (12, 6), (18, 12)] {
            let keccak = measure_fragment(|recorder| {
                let instance = recorder.next_scalars(log_rows).expect("recorded");
                let output = recorder.next_scalars(STATE_LANES).expect("recorded");
                let shape = KeccakShape { log_steps: log_rows, depth };
                let openings = verify_keccak(recorder, shape, &instance, &output).expect("recorded");
                let (point, slices) = openings.inputs;
                let mut outputs = [point, slices].concat();
                if let Some((point, word)) = openings.outputs {
                    outputs.extend(point.into_iter().chain([word]));
                }
                outputs
            });
            show(&format!("Keccak GKR 4af2cddd, 2^{log_rows} permutations, depth {depth}"), &keccak);
        }
    });
}
