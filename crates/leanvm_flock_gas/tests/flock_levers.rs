// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! What Flock's verifier costs, lever by lever (`flock_min`), measured as `keccak_estimate` measures Flock alone:
//! the recorded verifier compiled and run on revm, on a stream of the right length, its outputs (the claims) kept
//! live and not counted.
//! `cargo test --release -p leanvm_flock_gas --test flock_levers -- --ignored --nocapture`.

use leanvm_flock_gas::evm::contract::measure_fragment;
use leanvm_flock_gas::flock_min::{End, Slices, Variant, verify};

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

#[test]
#[ignore]
fn flock_levers() {
    deep(|| {
        let variants = [
            (
                Variant::LEANVM,
                "leanVM: slices sent, ring switch in the contract (map, coefficients, target, weight)",
            ),
            (
                Variant {
                    skip: 6,
                    slices: Slices::Weighted,
                },
                "(a') slices sent, target only; weight to a weighted claim",
            ),
            (
                Variant {
                    skip: 6,
                    slices: Slices::Claim,
                },
                "(a) no slices: one bit-slice combination claim",
            ),
            (
                Variant {
                    skip: 5,
                    slices: Slices::Claim,
                },
                "(a) + (c) skip 5",
            ),
            (
                Variant {
                    skip: 4,
                    slices: Slices::Claim,
                },
                "(a) + (c) skip 4",
            ),
            (
                Variant {
                    skip: 3,
                    slices: Slices::Claim,
                },
                "(a) + (c) skip 3",
            ),
            (
                Variant {
                    skip: 1,
                    slices: Slices::Claim,
                },
                "(a) + (c) skip 1",
            ),
            (
                Variant {
                    skip: 0,
                    slices: Slices::Claim,
                },
                "(a) + (c) no skip",
            ),
            (
                Variant {
                    skip: 3,
                    slices: Slices::Weighted,
                },
                "(a') + (c) skip 3",
            ),
            (
                Variant {
                    skip: 0,
                    slices: Slices::Weighted,
                },
                "(a') + (c) no skip",
            ),
        ];
        for (log_instances, signatures) in [(18, "1,290 signatures"), (13, "32 signatures")] {
            let log_n = 14 + log_instances;
            println!("\n### Flock at {signatures}: 2^{log_instances} compressions, log_n = {log_n}");
            println!(
                "| variant | scalars | calldata bytes | execution | FIELD_MUL | KECCAK256 | claims (q_flock, A0, B0) | \
                 tx share at 40 B (floor) | 16 B + execution |"
            );
            println!("|---|---:|---:|---:|---:|---:|---|---:|---:|");
            for (variant, name) in variants {
                let fragment = measure_fragment(|recorder| {
                    let reduced = verify(log_n, variant, recorder).expect("recorded");
                    let mut outputs = reduced.point.clone();
                    outputs.extend(
                        reduced
                            .matrices
                            .point
                            .iter()
                            .copied()
                            .chain([reduced.matrices.a, reduced.matrices.b]),
                    );
                    match reduced.end {
                        End::Ring { map, target, weight } => {
                            outputs.extend(map);
                            outputs.push(target);
                            outputs.extend(weight);
                        }
                        End::Combination { weights, value } => {
                            outputs.extend(weights);
                            outputs.push(value);
                        }
                    }
                    outputs
                });
                assert_eq!(fragment.stream_bytes, 24 * variant.scalars(log_n));
                let claim = match variant.slices {
                    Slices::InContract => "ring switch reduced in the contract, A0, B0",
                    Slices::Weighted => "1 weighted (Φ(eq)), A0, B0",
                    Slices::Claim => "1 bit-slice combination, A0, B0",
                };
                let bytes = fragment.stream_bytes as u64;
                println!(
                    "| {name} | {} | {} | {} | {} | {} | {claim} | {} | {} |",
                    variant.scalars(log_n),
                    grouped(bytes),
                    grouped(fragment.execution),
                    grouped(fragment.field_muls as u64),
                    fragment.hashes,
                    grouped(40 * bytes),
                    grouped(16 * bytes + fragment.execution),
                );
                if log_instances == 18 {
                    for phase in &fragment.phases {
                        eprintln!("    {name}: {:<55} {:>9}", phase.phase, grouped(phase.gas));
                    }
                }
            }
        }
    });
}
