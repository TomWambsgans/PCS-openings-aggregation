// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Test vectors for the Lean transcription of the verifier (`formal/UniStatement`): random, accepting and mutated
//! streams, each with the Rust verifier's verdict and its intermediate values (every challenge, every value it
//! requires to be zero, the claims it hands `PCS_OPEN`).
//!
//! `UNI_VECTORS_OUT=vectors.txt cargo test --release -p leanvm_univariate --test lean_vectors -- --ignored --nocapture`
//!
//! **Accepting streams.** The verifier's identities are checked once, at the end of a phase, on values that are
//! affine in the last scalar read before them (Flock's matrix terminal in `b`, the batching sumcheck's in the last
//! stack value). Starting from a random stream whose six row counts (its first 24 bytes, iteration 2's F1) fit the
//! heights, each check in turn is made to hold by solving for that scalar (two runs give the affine map), so the
//! reduction accepts and hands its claims to `PCS_OPEN`.
//!
//! **Iteration 2** (`SPEC.md` §13): the seed's IV is the contract's (`contract::contract_iv` of the program's IV, the
//! shape and the reference setup roots, F2), but for one vector a configuration under another program IV; the kinds
//! `counts` (accepting streams announcing other row counts that fit: none, one, the fewest a height sizes for, a full
//! table, random) and `badcount` (an accepting stream with one count made out of its range) exercise F1 and F1b.
//!
//! **Format** (one record a line, tokens separated by one space; an element of `E` is `c0:c1:c2`, each limb lowercase
//! hex; byte strings lowercase hex):
//!
//! ```text
//! VECTOR <id> <shape> <flock> <claims> <kind>
//! IV <hex> / PUBLIC <hex> / STREAM <nbytes> <hex>
//! RESULT OK | RESULT ERR <VerifierError>
//! CHALLENGES <n> <e>... / ZEROS <n> <e>... / NONZEROS <n> <e>... / ACCEPT <0|1>
//! (when OK) RELATIONS <n> / STACKVARS <k> (<commitment> <vars>)... / OPENINGS <k> / OPENING ... / MATRICES ...
//! END
//! ```

use std::fmt::Write as _;

use leanvm_flock_gas::shapes::WORKLOADS;
use leanvm_univariate::contract::{record_verifier, sample_stream};
use leanvm_univariate::{Blake2s, Claims, FLOCK_BIT_SLICE, FLOCK_LEANVM_SKIP, FLOCK_MAIN, Shape};

mod lean_format;
use lean_format::{Config, Rng, Writer, accepting, accepting_with_counts, count_bytes};

/// Run `f` on a thread with a deep stack, as `tests/gas.rs` does.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// `UNI_VECTORS_OUT=vectors.txt cargo test --release -p leanvm_univariate --test lean_vectors -- --ignored --nocapture`
#[test]
#[ignore]
fn lean_vectors() {
    deep(|| {
        let started = std::time::Instant::now();
        let path = std::env::var("UNI_VECTORS_OUT").unwrap_or_else(|_| "target/uni_vectors.txt".to_string());
        let by_name = |name: &str| WORKLOADS.iter().find(|w| w.name == name).expect("a workload");
        let flocks = [
            ("main", Blake2s::Flock(FLOCK_MAIN)),
            ("bitslice", Blake2s::Flock(FLOCK_BIT_SLICE)),
            ("leanvm", Blake2s::Flock(FLOCK_LEANVM_SKIP)),
            ("omitted", Blake2s::Omitted),
        ];
        let point = ("point", Claims::Point);
        let weighted = ("weighted", Claims::Weighted);
        // The 7 configurations of tests/gas.rs, at the reference shape, and leanVM's skip in weighted mode (the
        // ring switch's map in leanVM's order with Flock's matrices' rounds of its own).
        let reference = by_name("xmss1000");
        let configs = [
            (flocks[0], point),
            (flocks[1], point),
            (flocks[0], weighted),
            (flocks[1], weighted),
            (flocks[2], point),
            (flocks[3], point),
            (flocks[3], weighted),
            (flocks[2], weighted),
        ];
        let mut w = Writer::default();
        writeln!(
            w.out,
            "# leanvm_univariate differential test vectors (tests/lean_vectors.rs)"
        )
        .unwrap();
        let mut rng = Rng(0x5EED_1EA4_0000_0001);
        for (c, &(flock, claims)) in configs.iter().enumerate() {
            let config = Config::of(reference, flock, claims);
            let len = record_verifier(&config.shape(), flock.1, claims.1).stream_len;
            let iv = config.contract_iv();
            for s in 0..2u64 {
                let public = rng.bytes32();
                let mut stream = sample_stream(len, 0x100 + 16 * c as u64 + s);
                // The second random stream announces the shape's row counts (the first's are random bytes).
                if s == 1 {
                    stream[..24].copy_from_slice(&count_bytes(&config.shape().table_rows));
                }
                w.emit(&config, "random", &iv, &public, &stream);
            }
            let mut accepted = Vec::new();
            for s in 0..2u64 {
                let public = rng.bytes32();
                // One main-line accepting vector under another program IV.
                let mut config = config.clone();
                if c == 0 && s == 1 {
                    config.program_iv = [7u8; 32];
                }
                let iv = config.contract_iv();
                let stream = accepting(&config, &iv, &public, len, 0x200 + 16 * c as u64 + s);
                w.emit(&config, "accept", &iv, &public, &stream);
                accepted.push((iv, public, stream));
            }
            // Other row counts that fit (F1, F1b): each table's from its own list, by configuration.
            let heights = config.shape().heights();
            let counts_of = |pick: u64, rng: &mut Rng| -> [u64; 6] {
                std::array::from_fn(|t| {
                    let r = heights[t];
                    let full = 1u64 << r;
                    match (pick + t as u64) % 6 {
                        0 => 0,
                        1 => 1,
                        2 => Shape::least_rows(r),
                        3 => full,
                        4 => full - 1,
                        _ => rng.next() % (full + 1),
                    }
                })
            };
            for s in 0..2u64 {
                let public = rng.bytes32();
                let counts = counts_of(2 * c as u64 + s, &mut rng);
                let stream = accepting_with_counts(&config, &iv, &public, len, 0x280 + 16 * c as u64 + s, &counts);
                w.emit(&config, "counts", &iv, &public, &stream);
            }
            // A count out of its range: above 2^r, or 2^r with a low bit set.
            {
                let (_, public, base) = accepted[0].clone();
                let t = c % 6;
                let r = heights[t];
                let mut stream = base.clone();
                let bad = if c % 2 == 0 { (1u64 << (r + 1)) + 3 } else { (1u64 << r) | 1 };
                stream[4 * t..4 * t + 4].copy_from_slice(&(bad as u32).to_be_bytes());
                w.emit(&config, "badcount", &iv, &public, &stream);
            }
            let (_, public, base) = accepted[0].clone();
            let last_scalar = base.len() - 24;
            let positions = [
                (rng.next() as usize) % base.len(),
                // C1's root (after the 24 bytes of row counts)
                24 + (rng.next() as usize) % 32,
                last_scalar + (rng.next() as usize) % 24,
            ];
            for position in positions {
                let mut stream = base.clone();
                stream[position] ^= rng.nonzero_byte();
                w.emit(&config, "mutate", &iv, &public, &stream);
            }
            w.emit(&config, "truncate", &iv, &public, &base[..base.len() - 1]);
            let mut extended = base.clone();
            extended.extend([0u8; 24]);
            w.emit(&config, "extend", &iv, &public, &extended);
        }
        // The other measured shapes, the main line (and at the largest, extension W with B too).
        let others = [
            ("xmss32", (flocks[0], point)),
            ("xmss128", (flocks[0], point)),
            ("xmss400", (flocks[0], point)),
            ("xmss1290", (flocks[0], point)),
            ("xmss2000", (flocks[0], point)),
            ("xmss2000", (flocks[1], weighted)),
        ];
        for (k, (name, (flock, claims))) in others.into_iter().enumerate() {
            let config = Config::of(by_name(name), flock, claims);
            let len = record_verifier(&config.shape(), config.flock.1, config.claims.1).stream_len;
            let iv = config.contract_iv();
            let salt = 0x300 + 16 * k as u64;
            let public = rng.bytes32();
            w.emit(&config, "random", &iv, &public, &sample_stream(len, salt));
            let public = rng.bytes32();
            let stream = accepting(&config, &iv, &public, len, salt + 1);
            w.emit(&config, "accept", &iv, &public, &stream);
            let mut mutated = stream.clone();
            let position = (rng.next() as usize) % mutated.len();
            mutated[position] ^= rng.nonzero_byte();
            w.emit(&config, "mutate", &iv, &public, &mutated);
        }

        std::fs::write(&path, &w.out).expect("the vectors file");
        println!("{} vectors, {} lines, written to {path}", w.id, w.out.lines().count());
        for (kind, (yes, no)) in &w.tally {
            println!("{kind}: {yes} accepted, {no} rejected");
        }
        println!("in {:.1} s", started.elapsed().as_secs_f64());
    });
}
