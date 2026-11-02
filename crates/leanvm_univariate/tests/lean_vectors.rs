// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Test vectors for the Lean transcription of the verifier (`formal/UniStatement`): random, accepting and mutated
//! streams, each with the Rust verifier's verdict and its intermediate values (every challenge, every value it
//! requires to be zero, the claims it hands `PCS_OPEN`).
//!
//! `UNI_VECTORS_OUT=vectors.txt cargo test --release -p leanvm_univariate --test lean_vectors -- --ignored --nocapture`
//!
//! **Accepting streams.** The verifier's identities are checked once, at the end of a phase, on values that are
//! affine in the last scalar read before them (Flock's matrix terminal in `b`, the batching sumcheck's in the last
//! stack value). Starting from a random stream, each check in turn is made to hold by solving for that scalar
//! (two runs give the affine map), so the reduction accepts and hands its claims to `PCS_OPEN`.
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

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::field::{E, ONE, ZERO};
use leanvm_flock_gas::shapes::{PROGRAM_IV, WORKLOADS, Workload};
use leanvm_flock_gas::transcript::{Channel, Checks, KeccakChannel, keccak_seed, scalar_bytes};
use leanvm_univariate::claims::Combined;
use leanvm_univariate::contract::{NAME, record_verifier, sample_stream};
use leanvm_univariate::{
    Blake2s, Claims, FLOCK_BIT_SLICE, FLOCK_LEANVM_SKIP, FLOCK_MAIN, Opening, Reduced, Shape, reduce,
};

/// Run `f` on a thread with a deep stack, as `tests/gas.rs` does.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// The contract's chain, logging what the verifier draws and checks.
struct Logging<'a> {
    inner: KeccakChannel<'a>,
    cursor: usize,
    challenges: Vec<E>,
    zeros: Vec<E>,
    nonzeros: Vec<E>,
    /// The byte offset of each scalar read.
    scalar_at: Vec<usize>,
    /// For each zero check, how many scalars were read before it.
    zero_after: Vec<usize>,
}

impl Channel<E> for Logging<'_> {
    fn next_scalar(&mut self) -> Result<E, VerifierError> {
        let value = self.inner.next_scalar()?;
        self.scalar_at.push(self.cursor);
        self.cursor += 24;
        Ok(value)
    }

    fn next_root(&mut self) -> Result<[E; 2], VerifierError> {
        let halves = self.inner.next_root()?;
        self.cursor += 32;
        Ok(halves)
    }

    fn sample(&mut self) -> E {
        let challenge = self.inner.sample();
        self.challenges.push(challenge);
        challenge
    }

    fn require_zero(&mut self, value: E, _error: VerifierError) -> Result<(), VerifierError> {
        self.zeros.push(value);
        self.zero_after.push(self.scalar_at.len());
        Ok(())
    }

    fn require_nonzero(&mut self, value: E, _error: VerifierError) -> Result<(), VerifierError> {
        self.nonzeros.push(value);
        Ok(())
    }
}

/// What one run of the verifier gives.
struct Run {
    result: Result<Reduced<E>, VerifierError>,
    challenges: Vec<E>,
    zeros: Vec<E>,
    nonzeros: Vec<E>,
    scalar_at: Vec<usize>,
    zero_after: Vec<usize>,
}

impl Run {
    fn accepts(&self) -> bool {
        self.result.is_ok() && self.zeros.iter().all(|&z| z == ZERO) && self.nonzeros.iter().all(|&z| z != ZERO)
    }
}

/// One configuration of the verifier.
#[derive(Clone, Copy)]
struct Config {
    workload: &'static Workload,
    flock: (&'static str, Blake2s),
    claims: (&'static str, Claims),
}

impl Config {
    fn shape(&self) -> Shape {
        Shape::of(&self.workload.shape)
    }
}

/// The Rust verifier on `stream`, as `contract::rust_verifier` runs it, logging.
fn run(config: &Config, iv: &[u8; 32], public: &[u8; 32], stream: &[u8]) -> Run {
    let seed = keccak_seed(&NAME, iv, public);
    let mut channel = Logging {
        inner: KeccakChannel::new(seed, stream, Checks::Enforce),
        cursor: 0,
        challenges: vec![],
        zeros: vec![],
        nonzeros: vec![],
        scalar_at: vec![],
        zero_after: vec![],
    };
    let words: [E; 4] =
        std::array::from_fn(|k| E::new(u64::from_be_bytes(public[8 * k..8 * k + 8].try_into().unwrap()), 0, 0));
    let result = reduce(&config.shape(), words, &mut channel, config.flock.1, config.claims.1).and_then(|reduced| {
        channel.inner.finish()?;
        Ok(reduced)
    });
    Run {
        result,
        challenges: channel.challenges,
        zeros: channel.zeros,
        nonzeros: channel.nonzeros,
        scalar_at: channel.scalar_at,
        zero_after: channel.zero_after,
    }
}

/// A random stream made to pass every zero check, one check at a time, by solving for the scalar read last before it.
fn accepting(config: &Config, iv: &[u8; 32], public: &[u8; 32], len: usize, seed: u64) -> Vec<u8> {
    let mut stream = sample_stream(len, seed);
    let mut k = 0;
    loop {
        let current = run(config, iv, public, &stream);
        assert!(current.result.is_ok(), "a stream of the shape's length");
        if k >= current.zeros.len() {
            break;
        }
        if current.zeros[k] != ZERO {
            let read = current.zero_after[k];
            assert!(read > 0, "a scalar precedes the check");
            let offset = current.scalar_at[read - 1];
            let value_at = |x: E| {
                let mut patched = stream.clone();
                patched[offset..offset + 24].copy_from_slice(&scalar_bytes(x));
                run(config, iv, public, &patched).zeros[k]
            };
            let (v0, v1) = (value_at(ZERO), value_at(ONE));
            let slope = v0 + v1;
            assert!(slope != ZERO, "check {k} depends on its last scalar");
            let x = v0 * slope.inv();
            stream[offset..offset + 24].copy_from_slice(&scalar_bytes(x));
            assert_eq!(
                run(config, iv, public, &stream).zeros[k],
                ZERO,
                "check {k} holds once solved"
            );
        }
        k += 1;
    }
    let done = run(config, iv, public, &stream);
    assert!(done.accepts(), "the solved stream is accepted");
    stream
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn element(x: E) -> String {
    format!("{:x}:{:x}:{:x}", x.c0, x.c1, x.c2)
}

fn elements(xs: &[E]) -> String {
    let mut out = xs.len().to_string();
    for &x in xs {
        out.push(' ');
        out.push_str(&element(x));
    }
    out
}

fn combined(claim: &Combined<E>) -> String {
    let mut out = format!("P {}", claim.points.len());
    for point in &claim.points {
        write!(out, " {}", elements(point)).unwrap();
    }
    write!(out, " T {}", claim.terms.len()).unwrap();
    for &(column, p, twist, coefficient) in &claim.terms {
        write!(out, " {:x} {p} {twist} {}", column.id(), element(coefficient)).unwrap();
    }
    write!(out, " V {} R {}", element(claim.value), claim.relations).unwrap();
    out
}

/// One vector's record.
fn record(
    out: &mut String,
    id: usize,
    config: &Config,
    kind: &str,
    iv: &[u8; 32],
    public: &[u8; 32],
    stream: &[u8],
) -> bool {
    let r = run(config, iv, public, stream);
    writeln!(
        out,
        "VECTOR {id} {} {} {} {kind}",
        config.workload.name, config.flock.0, config.claims.0
    )
    .unwrap();
    writeln!(out, "IV {}", hex(iv)).unwrap();
    writeln!(out, "PUBLIC {}", hex(public)).unwrap();
    writeln!(out, "STREAM {} {}", stream.len(), hex(stream)).unwrap();
    match &r.result {
        Ok(_) => writeln!(out, "RESULT OK").unwrap(),
        Err(e) => writeln!(out, "RESULT ERR {e:?}").unwrap(),
    }
    writeln!(out, "CHALLENGES {}", elements(&r.challenges)).unwrap();
    writeln!(out, "ZEROS {}", elements(&r.zeros)).unwrap();
    writeln!(out, "NONZEROS {}", elements(&r.nonzeros)).unwrap();
    writeln!(out, "ACCEPT {}", r.accepts() as u8).unwrap();
    if let Ok(reduced) = &r.result {
        writeln!(out, "RELATIONS {}", reduced.relations).unwrap();
        let mut vars = format!("STACKVARS {}", reduced.stack_vars.len());
        for (commitment, v) in &reduced.stack_vars {
            write!(vars, " {commitment:?} {v}").unwrap();
        }
        writeln!(out, "{vars}").unwrap();
        writeln!(out, "OPENINGS {}", reduced.openings.len()).unwrap();
        for (commitment, opening) in &reduced.openings {
            match opening {
                Opening::Point {
                    point,
                    value,
                    bit_slice,
                } => {
                    let slice = match bit_slice {
                        None => "BITSLICE 0".to_string(),
                        Some(claim) => format!("BITSLICE 1 {}", combined(claim)),
                    };
                    writeln!(
                        out,
                        "OPENING {commitment:?} POINT {} VALUE {} {slice}",
                        elements(point),
                        element(*value)
                    )
                    .unwrap();
                }
                Opening::Weighted(claim) => {
                    writeln!(out, "OPENING {commitment:?} WEIGHTED {}", combined(claim)).unwrap()
                }
            }
        }
        match &reduced.matrices {
            None => writeln!(out, "MATRICES 0").unwrap(),
            Some(m) => writeln!(
                out,
                "MATRICES 1 {} A {} B {}",
                elements(&m.point),
                element(m.a),
                element(m.b)
            )
            .unwrap(),
        }
    }
    writeln!(out, "END").unwrap();
    r.accepts()
}

/// The vectors written so far, and the verdicts by kind (accepted, rejected).
#[derive(Default)]
struct Writer {
    out: String,
    id: usize,
    tally: std::collections::BTreeMap<&'static str, (usize, usize)>,
}

impl Writer {
    fn emit(&mut self, config: &Config, kind: &'static str, iv: &[u8; 32], public: &[u8; 32], stream: &[u8]) {
        let accepted = record(&mut self.out, self.id, config, kind, iv, public, stream);
        self.id += 1;
        let entry = self.tally.entry(kind).or_default();
        if accepted {
            entry.0 += 1;
        } else {
            entry.1 += 1;
        }
    }
}

/// Deterministic pseudo-random words.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_le_bytes());
        }
        out
    }

    fn nonzero_byte(&mut self) -> u8 {
        loop {
            let b = (self.next() >> 24) as u8;
            if b != 0 {
                return b;
            }
        }
    }
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
        // The 7 configurations of tests/gas.rs, at the reference shape.
        let reference = by_name("xmss1000");
        let configs = [
            (flocks[0], point),
            (flocks[1], point),
            (flocks[0], weighted),
            (flocks[1], weighted),
            (flocks[2], point),
            (flocks[3], point),
            (flocks[3], weighted),
        ];
        let mut w = Writer::default();
        writeln!(
            w.out,
            "# leanvm_univariate differential test vectors (tests/lean_vectors.rs)"
        )
        .unwrap();
        let mut rng = Rng(0x5EED_1EA4_0000_0001);
        for (c, &(flock, claims)) in configs.iter().enumerate() {
            let config = Config {
                workload: reference,
                flock,
                claims,
            };
            let len = record_verifier(&config.shape(), flock.1, claims.1).stream_len;
            for s in 0..2u64 {
                let public = rng.bytes32();
                let stream = sample_stream(len, 0x100 + 16 * c as u64 + s);
                w.emit(&config, "random", &PROGRAM_IV, &public, &stream);
            }
            let mut accepted = Vec::new();
            for s in 0..2u64 {
                let public = rng.bytes32();
                // One main-line accepting vector under another IV.
                let iv = if c == 0 && s == 1 { [7u8; 32] } else { PROGRAM_IV };
                let stream = accepting(&config, &iv, &public, len, 0x200 + 16 * c as u64 + s);
                w.emit(&config, "accept", &iv, &public, &stream);
                accepted.push((iv, public, stream));
            }
            let (iv, public, base) = accepted[0].clone();
            let last_scalar = base.len() - 24;
            let positions = [
                (rng.next() as usize) % base.len(),
                (rng.next() as usize) % 32,
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
        // A small shape, the main line.
        let config = Config {
            workload: by_name("xmss32"),
            flock: flocks[0],
            claims: point,
        };
        let len = record_verifier(&config.shape(), config.flock.1, config.claims.1).stream_len;
        let public = rng.bytes32();
        w.emit(&config, "random", &PROGRAM_IV, &public, &sample_stream(len, 0x300));
        let public = rng.bytes32();
        let stream = accepting(&config, &PROGRAM_IV, &public, len, 0x301);
        w.emit(&config, "accept", &PROGRAM_IV, &public, &stream);
        let mut mutated = stream.clone();
        let position = (rng.next() as usize) % mutated.len();
        mutated[position] ^= rng.nonzero_byte();
        w.emit(&config, "mutate", &PROGRAM_IV, &public, &mutated);

        std::fs::write(&path, &w.out).expect("the vectors file");
        println!("{} vectors, {} lines, written to {path}", w.id, w.out.lines().count());
        for (kind, (yes, no)) in &w.tally {
            println!("{kind}: {yes} accepted, {no} rejected");
        }
        println!("in {:.1} s", started.elapsed().as_secs_f64());
    });
}
