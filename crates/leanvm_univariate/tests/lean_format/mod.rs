// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The vectors' format and the Rust verifier's run on them, shared by `tests/lean_vectors.rs` (random, accepting and
//! mutated streams at the measured shapes) and `tests/review_honest.rs` (the review's honest proofs). See
//! `lean_vectors.rs` for the format; each vector also has a `SHAPE <log_memory> <log_bytecode> <rows…>` line (the
//! Rust's `Shape`, whose heights `⌈log₂ rows⌉` the contract is built for), its setup (`PROGRAMIV`, `CONTRACTIV`, the
//! five `LAYOUTWORDS`: `contract::contract_iv` and `layout_words` at the reference roots) and the row counts the
//! stream announces (`COUNTS`, iteration 2's F1).

use std::fmt::Write as _;

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::field::{E, ONE, ZERO};
use leanvm_flock_gas::shapes::Workload;
use leanvm_flock_gas::transcript::{Channel, Checks, KeccakChannel, keccak_seed, scalar_bytes};
use leanvm_univariate::claims::Combined;
use leanvm_univariate::contract::{NAME, SetupRoots, contract_iv, layout_words, sample_stream};
use leanvm_univariate::{Blake2s, Claims, Opening, Reduced, Shape, reduce};

/// The contract's chain, logging what the verifier draws and checks.
pub struct Logging<'a> {
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

impl<'a> Logging<'a> {
    fn new(seed: [u8; 32], stream: &'a [u8]) -> Self {
        Self {
            inner: KeccakChannel::new(seed, stream, Checks::Enforce),
            cursor: 0,
            challenges: vec![],
            zeros: vec![],
            nonzeros: vec![],
            scalar_at: vec![],
            zero_after: vec![],
        }
    }
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

    fn next_integer(&mut self, bytes: usize) -> Result<E, VerifierError> {
        let value = self.inner.next_integer(bytes)?;
        self.cursor += bytes;
        Ok(value)
    }
}

/// What one run of the verifier gives.
pub struct Run {
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

/// One configuration of the verifier: a named shape, the BLAKE2s argument, the claims' mode.
#[derive(Clone)]
pub struct Config {
    pub name: String,
    pub shape: Shape,
    pub flock: (&'static str, Blake2s),
    pub claims: (&'static str, Claims),
    /// The program's IV, which the contract's IV is derived from (`contract::contract_iv`, F2).
    pub program_iv: [u8; 32],
}

impl Config {
    /// A measured workload's shape.
    pub fn of(workload: &Workload, flock: (&'static str, Blake2s), claims: (&'static str, Claims)) -> Self {
        Self {
            name: workload.name.to_string(),
            shape: Shape::of(&workload.shape),
            flock,
            claims,
            program_iv: leanvm_flock_gas::shapes::PROGRAM_IV,
        }
    }

    pub fn shape(&self) -> Shape {
        self.shape
    }

    /// The contract's IV for this configuration's program IV, at the reference setup roots.
    pub fn contract_iv(&self) -> [u8; 32] {
        contract_iv(&self.shape, &self.program_iv, &SetupRoots::REFERENCE)
    }
}

/// The six row counts as the stream announces them (iteration 2, F1): 4-byte big-endian integers, XOR to BLAKE2S.
pub fn count_bytes(counts: &[u64; 6]) -> [u8; 24] {
    let mut out = [0u8; 24];
    for (k, &c) in counts.iter().enumerate() {
        out[4 * k..4 * k + 4].copy_from_slice(&(c as u32).to_be_bytes());
    }
    out
}

/// The Rust verifier on `stream`, as `contract::rust_verifier` runs it, logging.
pub fn run(config: &Config, iv: &[u8; 32], public: &[u8; 32], stream: &[u8]) -> Run {
    let seed = keccak_seed(&NAME, iv, public);
    let mut channel = Logging::new(seed, stream);
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
/// Its row counts are the shape's (`Shape::table_rows`), which fit its heights.
pub fn accepting(config: &Config, iv: &[u8; 32], public: &[u8; 32], len: usize, seed: u64) -> Vec<u8> {
    accepting_with_counts(config, iv, public, len, seed, &config.shape.table_rows)
}

/// [`accepting`], the stream announcing `counts` (each at most its height's `2^r`, so that the counts' checks hold).
pub fn accepting_with_counts(
    config: &Config,
    iv: &[u8; 32],
    public: &[u8; 32],
    len: usize,
    seed: u64,
    counts: &[u64; 6],
) -> Vec<u8> {
    let mut stream = sample_stream(len, seed);
    stream[..24].copy_from_slice(&count_bytes(counts));
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

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

pub fn element(x: E) -> String {
    format!("{:x}:{:x}:{:x}", x.c0, x.c1, x.c2)
}

pub fn elements(xs: &[E]) -> String {
    let mut out = xs.len().to_string();
    for &x in xs {
        out.push(' ');
        out.push_str(&element(x));
    }
    out
}

pub fn combined(claim: &Combined<E>) -> String {
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

/// One vector's record, then `extra` (lines of its own, each ending in a newline).
pub fn record(
    out: &mut String,
    id: usize,
    config: &Config,
    kind: &str,
    iv: &[u8; 32],
    public: &[u8; 32],
    stream: &[u8],
    extra: &str,
) -> bool {
    let r = run(config, iv, public, stream);
    writeln!(
        out,
        "VECTOR {id} {} {} {} {kind}",
        config.name, config.flock.0, config.claims.0
    )
    .unwrap();
    let shape = config.shape();
    let rows: Vec<String> = shape.table_rows.iter().map(|r| r.to_string()).collect();
    writeln!(out, "SHAPE {} {} {}", shape.log_memory, shape.log_bytecode, rows.join(" ")).unwrap();
    writeln!(out, "PROGRAMIV {}", hex(&config.program_iv)).unwrap();
    writeln!(out, "CONTRACTIV {}", hex(&config.contract_iv())).unwrap();
    let words: Vec<String> = layout_words(&shape).iter().map(|w| hex(w)).collect();
    writeln!(out, "LAYOUTWORDS {} {}", words.len(), words.join(" ")).unwrap();
    let counts: Vec<String> = (0..6)
        .filter(|k| 4 * k + 4 <= stream.len())
        .map(|k| u32::from_be_bytes(stream[4 * k..4 * k + 4].try_into().unwrap()).to_string())
        .collect();
    writeln!(out, "COUNTS {} {}", counts.len(), counts.join(" ")).unwrap();
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
    out.push_str(extra);
    writeln!(out, "END").unwrap();
    r.accepts()
}

/// The vectors written so far, and the verdicts by kind (accepted, rejected).
#[derive(Default)]
pub struct Writer {
    pub out: String,
    pub id: usize,
    pub tally: std::collections::BTreeMap<&'static str, (usize, usize)>,
}

impl Writer {
    pub fn emit(&mut self, config: &Config, kind: &'static str, iv: &[u8; 32], public: &[u8; 32], stream: &[u8]) {
        self.emit_with(config, kind, iv, public, stream, "");
    }

    /// A vector with lines of its own (`extra`) before its `END`.
    pub fn emit_with(
        &mut self,
        config: &Config,
        kind: &'static str,
        iv: &[u8; 32],
        public: &[u8; 32],
        stream: &[u8],
        extra: &str,
    ) {
        let accepted = record(&mut self.out, self.id, config, kind, iv, public, stream, extra);
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
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    pub fn bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_le_bytes());
        }
        out
    }

    pub fn nonzero_byte(&mut self) -> u8 {
        loop {
            let b = (self.next() >> 24) as u8;
            if b != 0 {
                return b;
            }
        }
    }
}

