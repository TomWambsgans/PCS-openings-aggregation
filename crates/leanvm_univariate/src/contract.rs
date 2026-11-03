// Part of this repository; the contract's assembly and measurement follow crates/leanvm_flock_gas/src/evm/contract.rs.
// MIT OR Apache-2.0; see NOTICE.md.
//! The verifier as a contract (straight-line code compiled from the recorded verifier, `leanvm_flock_gas::evm`), its
//! calldata, and what a call costs.
//!
//! **Calldata**: selector, the public input (four 64-bit words, each big-endian: `(cell0.c0, cell0.c1, cell1.c0,
//! cell1.c1)`; leanVM's 32-byte digest has its words little-endian, so a caller reverses each word's 8 bytes, SPEC.md
//! §4), then the stream: the six row counts, `C1`'s root, Flock's messages, `C2`'s root, the values at `t`, the
//! batching sumcheck (SPEC.md §8, §13). The contract is built for one shape class (the heights), which the
//! transcript's IV binds with the setup roots and the layout words.
//!
//! **Calls**: one `PCS_OPEN` call per commitment, each with one weighted claim (SPEC.md §8): words `root, layout,
//! k = 1, P`, the `P` points (a length, then the coordinates), the claim's `m` terms (`column | point << 32 |
//! twist << 48`, then the coefficient) and its value; `A0` and `B0` as evaluation claims (`root, layout, 1`, the
//! point, the value). The setup roots are constants in the code (no `SLOAD`).
//!
//! **Root words** (`crates/leanvm_rec/REVIEW-REC.md`, R1). `C1`'s and `C2`'s are the stream's 32 bytes as they are:
//! the prover sends each root as its two WHIR scalars (`prover::prove::halves`, `hash_to_scalars`), so those bytes
//! are `PCS_OPEN`'s root word `s_0 · 2^128 + s_1` (`crates/evm/src/machine.rs`), which a decoding precompile reads as
//! the root the opening is of. The setup roots' words are the hashes as they are ([`SetupRoots`]), not their root
//! words: a precompile with machine.rs's decoding reads each as another root (`root_word` of it), so this contract,
//! deployed alone, needs `Word::Const(root_word(..))` there (free: constants). π2's contract, which makes π1's calls,
//! passes their root words (`crates/leanvm_rec`, `circuit::compile`).

use leanvm_flock_gas::evm::codegen::{CALLS, Contract, ENTRY, Ending, Entry, MEASURE, VERIFY, Word, compile, word};
use leanvm_flock_gas::evm::machine::{Outcome, PcsOpen, call};
use leanvm_flock_gas::evm::record::{Graph, Recorder, Sym, record};
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::transcript::{Checks, FsShape, KeccakChannel, keccak_seed};

use crate::claims::{Combined, Commitment};
use crate::verifier::{Blake2s, Claims, Opening, Reduced, Shape, reduce};

/// The transcript's 16-byte name.
pub const NAME: [u8; 16] = *b"leanVM-univar-v1";

/// The setup commitments' roots, constants of the code (review M1, F2): `F` from the program and the shape, `A0` and
/// `B0` from Flock's BLAKE2s R1CS. The prover computes them (`prover::setup::roots`, branch
/// `leanvm-univariate-prover`, PROVER.md); [`SetupRoots::REFERENCE`] are the reference shape's (memory `2^21`,
/// bytecode `2^19`), which the gas reports use for every shape (the gas does not depend on them).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SetupRoots {
    pub f: [u8; 32],
    pub a0: [u8; 32],
    pub b0: [u8; 32],
}

const fn digit(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        _ => c - b'a' + 10,
    }
}

const fn hex32(text: &[u8; 64]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        out[i] = digit(text[2 * i]) << 4 | digit(text[2 * i + 1]);
        i += 1;
    }
    out
}

impl SetupRoots {
    pub const REFERENCE: Self = Self {
        f: hex32(b"9b5a0f9bd796c09b8bc328113956464acf865c99b7dfc088c0c0a3208eab5fb7"),
        a0: hex32(b"93cd9a0352a85dcc663f7068e1f3afa3a00f5220bd2b03d67244f0eb133fd2f7"),
        b0: hex32(b"c07556508c416240dafd47665831fd51d2eb1104a52c63231101479c7f6cd467"),
    };
}

/// The opening a `PCS_OPEN` call is for, its code in the layout word.
fn layout_code(commitment: Commitment) -> u16 {
    match commitment {
        Commitment::C1 => 0x5501,
        Commitment::C2 => 0x5502,
        Commitment::Setup => 0x5503,
    }
}
const A0_CODE: u16 = 0x5504;
const B0_CODE: u16 = 0x5505;

/// The shape's bytes: `log_memory`, `log_bytecode`, then the six heights.
pub fn shape_bytes(shape: &Shape) -> [u8; 8] {
    let heights = shape.heights();
    let mut bytes = [0u8; 8];
    bytes[0] = shape.log_memory as u8;
    bytes[1] = shape.log_bytecode as u8;
    for (k, &h) in heights.iter().enumerate() {
        bytes[2 + k] = h as u8;
    }
    bytes
}

/// A `PCS_OPEN` call's layout word (review M1, F2; the prover's request): the shape's bytes (bytes 0..8), the
/// opening's code (22..24), the stack's variables (24) and the words its blocks fill, `placed` (25..32), which
/// WHIR's verifier needs to know the committed lanes. Each shape's stacks have their own words.
pub fn layout_word(shape: &Shape, code: u16, vars: usize, placed: u64) -> [u8; 32] {
    assert!(vars < 256 && placed < 1 << 56);
    let mut word = [0u8; 32];
    word[..8].copy_from_slice(&shape_bytes(shape));
    word[22..24].copy_from_slice(&code.to_be_bytes());
    word[24] = vars as u8;
    word[25..].copy_from_slice(&placed.to_be_bytes()[1..]);
    word
}

/// The five openings' layout words, in call order: `C1`, `C2`, the setup, `A0`, `B0`.
pub fn layout_words(shape: &Shape) -> [[u8; 32]; 5] {
    let layouts = crate::verifier::layouts(shape);
    let of = |c: Commitment| {
        let layout = &layouts.iter().find(|(k, _)| *k == c).expect("a layout").1;
        layout_word(shape, layout_code(c), layout.vars, layout.words())
    };
    let matrix = |code| layout_word(shape, code, 28, 1 << 28);
    [of(Commitment::C1), of(Commitment::C2), of(Commitment::Setup), matrix(A0_CODE), matrix(B0_CODE)]
}

/// The IV the transcript's seed hashes (review M1, F2): the hash of a tag, the program's IV (leanVM's digest of the
/// bytecode and the R1CS), the setup roots, the shape and the five layout words. The seed then adds the public
/// input. A constant of the code: it costs no gas.
pub fn contract_iv(shape: &Shape, program_iv: &[u8; 32], roots: &SetupRoots) -> [u8; 32] {
    let words = layout_words(shape);
    let mut data = b"leanVM-univar-iv".to_vec();
    data.extend_from_slice(program_iv);
    for root in [roots.f, roots.a0, roots.b0] {
        data.extend_from_slice(&root);
    }
    data.extend_from_slice(&shape_bytes(shape));
    for w in &words {
        data.extend_from_slice(w);
    }
    leanvm_flock_gas::transcript::keccak256(&data)
}

/// What the IV appends for `blake2s` (`crates/leanvm_rec/REVIEW-REC.md`, N2): nothing on the Fiat–Shamir shape
/// `Main` (the main line's IV and its measured variants' are unchanged, as their vectors and the Lean transcription
/// take them); with π1-rec's shape ([`FsShape::Rec`]) the tag `"fs-rec"`, then the skip, the slices' code and, for the
/// variant's batching challenges, their width in bytes. A Rec contract's IV is then the Keccak-256 of a longer
/// preimage than any Main contract's (`contract_iv`'s is of fixed length), so the two never share a seed.
pub fn variant_bytes(blake2s: Blake2s) -> Vec<u8> {
    use leanvm_flock_gas::flock_min::Slices;
    let Blake2s::Flock(v) = blake2s else {
        return vec![];
    };
    if v.fs == FsShape::Main {
        return vec![];
    }
    let slices = match v.slices {
        Slices::InContract => 0,
        Slices::Weighted => 1,
        Slices::Claim => 2,
        Slices::Tower => 3,
        Slices::TowerWalk => 4,
    };
    let mut out = match v.fs {
        FsShape::Rec2 => b"fs-rec2".to_vec(),
        FsShape::Rec3 => b"fs-rec3".to_vec(),
        _ => b"fs-rec".to_vec(),
    };
    out.extend([v.skip as u8, slices]);
    out
}

/// The IV of the contract for `blake2s` (N2): [`contract_iv`], with [`variant_bytes`] appended to its preimage when
/// there are any.
pub fn contract_iv_for(shape: &Shape, blake2s: Blake2s, program_iv: &[u8; 32], roots: &SetupRoots) -> [u8; 32] {
    let extra = variant_bytes(blake2s);
    if extra.is_empty() {
        return contract_iv(shape, program_iv, roots);
    }
    let words = layout_words(shape);
    let mut data = b"leanVM-univar-iv".to_vec();
    data.extend_from_slice(program_iv);
    for root in [roots.f, roots.a0, roots.b0] {
        data.extend_from_slice(&root);
    }
    data.extend_from_slice(&shape_bytes(shape));
    for w in &words {
        data.extend_from_slice(w);
    }
    data.extend_from_slice(&extra);
    leanvm_flock_gas::transcript::keccak256(&data)
}

/// The verifier for one shape, recorded.
pub struct Recorded {
    pub shape: Shape,
    /// The BLAKE2s argument (and so the Fiat–Shamir shape) it was recorded for: the IV binds it ([`contract_iv_for`]).
    pub blake2s: Blake2s,
    pub roots: SetupRoots,
    pub graph: Graph,
    pub reduced: Reduced<Sym>,
    pub stream_len: usize,
    pub roots_at: [usize; 2],
    pub reads: Vec<(&'static str, u32)>,
}

impl Recorded {
    /// The contract's IV for the program's `program_iv` ([`contract_iv_for`] of the shape, the variant and the roots
    /// it was recorded with).
    pub fn iv(&self, program_iv: &[u8; 32]) -> [u8; 32] {
        contract_iv_for(&self.shape, self.blake2s, program_iv, &self.roots)
    }
}

pub fn record_verifier(shape: &Shape, blake2s: Blake2s, mode: Claims) -> Recorded {
    record_verifier_with(shape, blake2s, mode, &SetupRoots::REFERENCE)
}

/// [`record_verifier`] for a contract that binds `setup` (another shape's `F`, say): the graph is the same, the
/// roots are the code's constants.
pub fn record_verifier_with(shape: &Shape, blake2s: Blake2s, mode: Claims, setup: &SetupRoots) -> Recorded {
    let ((reduced, stream_len, roots, reads), graph) = record(|| {
        let mut recorder = Recorder::new();
        let words = Recorder::statement();
        let reduced = reduce(shape, words, &mut recorder, blake2s, mode).expect("a recorder rejects nothing");
        (reduced, recorder.cursor as usize, recorder.roots.clone(), recorder.reads)
    });
    assert_eq!(roots.len(), 2, "two commitments in the stream");
    Recorded {
        shape: *shape,
        blake2s,
        roots: *setup,
        graph,
        reduced,
        stream_len,
        roots_at: [roots[0] as usize, roots[1] as usize],
        reads,
    }
}

fn number(n: u64) -> Word {
    let mut bytes = [0; 32];
    bytes[24..].copy_from_slice(&n.to_be_bytes());
    Word::Const(bytes)
}

fn scalar(sym: Sym) -> Word {
    Word::Node(sym.0)
}

/// A weighted claim's words, after its header: `P`, the points, `m`, the terms, the value.
fn combined_words<T: Copy, W: Clone>(claim: &Combined<T>, word: impl Fn(T) -> W, number: impl Fn(u64) -> W) -> Vec<W> {
    let mut words = vec![number(claim.points.len() as u64)];
    for point in &claim.points {
        words.push(number(point.len() as u64));
        words.extend(point.iter().map(|&x| word(x)));
    }
    words.push(number(claim.terms.len() as u64));
    for &(column, point, twist, coefficient) in &claim.terms {
        words.push(number(column.id() | (point as u64) << 32 | (twist as u64) << 48));
        words.push(word(coefficient));
    }
    words.push(word(claim.value));
    words
}

/// A commitment's call: its header (root, layout, claims), then its claims.
fn opening_words<T: Copy, W: Clone>(
    root: W,
    layout: W,
    opening: &Opening<T>,
    word: impl Fn(T) -> W + Copy,
    number: impl Fn(u64) -> W + Copy,
) -> Vec<W> {
    match opening {
        Opening::Weighted(claim) => [vec![root, layout, number(1)], combined_words(claim, word, number)].concat(),
        Opening::Point { point, value, bit_slice } => {
            let k = 1 + bit_slice.is_some() as u64;
            let mut words = vec![root, layout, number(k)];
            words.extend(point.iter().map(|&x| word(x)));
            words.push(word(*value));
            if let Some(claim) = bit_slice {
                words.extend(combined_words(claim, word, number));
            }
            words
        }
    }
}

/// The calls of `PCS_OPEN`, as runs of output words.
pub fn calls(recorded: &Recorded) -> Vec<Vec<Word>> {
    let reduced = &recorded.reduced;
    let layouts = layout_words(&recorded.shape);
    let roots = recorded.roots;
    let mut out = Vec::new();
    for (commitment, opening) in &reduced.openings {
        let (root, layout) = match commitment {
            Commitment::C1 => (Word::Stream(recorded.roots_at[0]), layouts[0]),
            Commitment::C2 => (Word::Stream(recorded.roots_at[1]), layouts[1]),
            Commitment::Setup => (Word::Const(roots.f), layouts[2]),
        };
        out.push(opening_words(root, Word::Const(layout), opening, scalar, number));
    }
    if let Some(matrices) = &reduced.matrices {
        for (root, layout, value) in [(roots.a0, layouts[3], matrices.a), (roots.b0, layouts[4], matrices.b)] {
            let mut words = vec![Word::Const(root), Word::Const(layout), number(1)];
            words.extend(matrices.point.iter().map(|&x| scalar(x)));
            words.push(scalar(value));
            out.push(words);
        }
    }
    out
}

/// `program_iv` is the program's (leanVM's digest of the bytecode and the R1CS); the contract's IV is derived from it
/// ([`contract_iv`]), as in every function here that takes one.
pub fn compile_verifier(recorded: &Recorded, program_iv: &[u8; 32], measure: bool) -> Contract {
    let entry = Entry {
        name: NAME,
        iv: recorded.iv(program_iv),
        stream_len: recorded.stream_len,
        measure,
    };
    let calls = calls(recorded);
    let ending = Ending::PcsOpen(calls.iter().map(Vec::len).collect());
    compile(&recorded.graph, &calls.concat(), &ending, &entry)
}

pub fn calldata(public_words: &[u8; 32], stream: &[u8]) -> Vec<u8> {
    [&VERIFY[..], public_words, stream].concat()
}

/// A stream of the shape's length, its bytes pseudo-random as a proof's are (the contract's gas does not depend on
/// them; the transaction's does, on its zero bytes only).
pub fn sample_stream(len: usize, seed: u64) -> Vec<u8> {
    let mut state = seed | 1;
    (0..len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state >> 24) as u8
        })
        .collect()
}

/// The Rust verifier on the same calldata: the claims, and the values it requires to be zero, then nonzero.
pub fn rust_verifier(
    shape: &Shape,
    iv: &[u8; 32],
    public_words: &[u8; 32],
    stream: &[u8],
    blake2s: Blake2s,
    mode: Claims,
) -> Result<(Reduced<E>, Vec<E>, Vec<E>), leanvm_flock_gas::VerifierError> {
    rust_verifier_with(shape, iv, &SetupRoots::REFERENCE, public_words, stream, blake2s, mode)
}

/// [`rust_verifier`] for a contract that binds `setup` in its IV.
pub fn rust_verifier_with(
    shape: &Shape,
    iv: &[u8; 32],
    setup: &SetupRoots,
    public_words: &[u8; 32],
    stream: &[u8],
    blake2s: Blake2s,
    mode: Claims,
) -> Result<(Reduced<E>, Vec<E>, Vec<E>), leanvm_flock_gas::VerifierError> {
    let seed = keccak_seed(&NAME, &contract_iv_for(shape, blake2s, iv, setup), public_words);
    let mut channel = KeccakChannel::new(
        seed,
        stream,
        Checks::Collect {
            zero: vec![],
            nonzero: vec![],
        },
    );
    let words: [E; 4] = std::array::from_fn(|k| {
        E::new(
            u64::from_be_bytes(public_words[8 * k..8 * k + 8].try_into().unwrap()),
            0,
            0,
        )
    });
    let reduced = reduce(shape, words, &mut channel, blake2s, mode)?;
    channel.finish()?;
    let Checks::Collect { zero, nonzero } = channel.checks else {
        unreachable!()
    };
    Ok((reduced, zero, nonzero))
}

/// One phase's share of a call.
#[derive(Clone, Debug)]
pub struct PhaseGas {
    pub phase: &'static str,
    pub gas: u64,
}

/// What a verifying call costs.
#[derive(Clone, Debug)]
pub struct GasReport {
    pub calldata_bytes: usize,
    pub calldata_zero_bytes: usize,
    pub stream_bytes: usize,
    pub execution: u64,
    pub phases: Vec<PhaseGas>,
    pub claims: usize,
    pub calls: usize,
    /// Terms of each call's claim, and words written for `PCS_OPEN`.
    pub terms: Vec<(String, usize, usize)>,
    pub pcs_words: usize,
    pub relations: usize,
    pub code_bytes: usize,
    pub field_muls: usize,
    pub xors: usize,
    pub hashes: usize,
    pub hashed_bytes: usize,
    pub checks: usize,
    pub memory_words: usize,
    pub stream_by_phase: Vec<(&'static str, u32)>,
}

impl GasReport {
    pub fn execution_at(&self, c: u64) -> u64 {
        self.execution + c * self.claims as u64
    }

    /// Transaction gas without its 21,000 base: `floor` 40 for EIP-7623 (10 a zero byte), 64 for EIP-7976.
    pub fn transaction(&self, c: u64, floor: u64) -> u64 {
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64;
        let zero = self.calldata_zero_bytes as u64;
        let standard = 16 * nonzero + 4 * zero + self.execution_at(c);
        let floor_gas = floor * nonzero + if floor == 64 { 64 } else { floor / 4 } * zero;
        standard.max(floor_gas)
    }

    pub fn calldata_gas(&self) -> u64 {
        let nonzero = (self.calldata_bytes - self.calldata_zero_bytes) as u64;
        16 * nonzero + 4 * self.calldata_zero_bytes as u64
    }
}

/// Measure the verifier for `shape`: build it, run it on sample calldata with every call attested, and check the
/// run's gas against a run at another claim price and the phases against the total.
pub fn measure(shape: &Shape, iv: &[u8; 32], blake2s: Blake2s, mode: Claims) -> GasReport {
    let recorded = record_verifier(shape, blake2s, mode);
    let contract = compile_verifier(&recorded, iv, true);
    let stream = sample_stream(recorded.stream_len, 0x6A5);
    let data = calldata(&[0x5a; 32], &stream);
    assert_eq!(data.len(), contract.calldata_len);
    let all_calls = calls(&recorded);
    let claims: usize = recorded
        .reduced
        .openings
        .iter()
        .map(|(_, opening)| match opening {
            Opening::Weighted(_) => 1,
            Opening::Point { bit_slice, .. } => 1 + bit_slice.is_some() as usize,
        })
        .sum::<usize>()
        + 2 * recorded.reduced.matrices.is_some() as usize;
    let calls_count = all_calls.len();
    let run = |claim_gas: u64| -> Outcome {
        let block = PcsOpen::attesting_all(claim_gas);
        let outcome = call(&contract.code, &[], &data, &block);
        assert_eq!(outcome.output.as_deref(), Some(&word([1, 0, 0])[..]), "the measuring run returns 1");
        assert_eq!(outcome.pcs_calls.len(), calls_count, "one call per commitment");
        outcome
    };
    let outcome = run(0);
    assert_eq!(run(1000).execution, outcome.execution + 1000 * claims as u64);
    let mut phases: Vec<PhaseGas> = Vec::new();
    for (pc, &gas) in outcome.gas_by_pc.iter().enumerate() {
        if gas == 0 {
            continue;
        }
        let phase = contract.phase_of.get(pc).copied().unwrap_or(CALLS);
        match phases.iter_mut().find(|p| p.phase == phase) {
            Some(p) => p.gas += gas,
            None => phases.push(PhaseGas { phase, gas }),
        }
    }
    let total: u64 = phases.iter().map(|p| p.gas).sum();
    assert_eq!(total, outcome.execution, "the instructions' gas is the execution's");
    let measured = phases.iter().find(|p| p.phase == MEASURE).map_or(0, |p| p.gas);
    assert_eq!(measured, contract.checks as u64 + calls_count as u64, "one JUMPDEST a check and a call");
    phases.retain(|p| p.phase != MEASURE);
    phases.sort_by_key(|p| std::cmp::Reverse(p.gas));
    let mut terms: Vec<(String, usize, usize)> = recorded
        .reduced
        .openings
        .iter()
        .zip(&all_calls)
        .map(|((commitment, opening), words)| {
            let terms = match opening {
                Opening::Weighted(claim) => claim.terms.len(),
                Opening::Point { bit_slice, .. } => 1 + bit_slice.as_ref().map_or(0, |c| c.terms.len()),
            };
            (format!("{commitment:?}"), terms, words.len())
        })
        .collect();
    for (name, words) in ["A0", "B0"].iter().zip(&all_calls[recorded.reduced.openings.len()..]) {
        terms.push((name.to_string(), 1, words.len()));
    }
    let _ = ENTRY;
    GasReport {
        calldata_bytes: data.len(),
        calldata_zero_bytes: data.iter().filter(|&&b| b == 0).count(),
        stream_bytes: stream.len(),
        execution: outcome.execution - measured,
        phases,
        claims,
        calls: calls_count,
        pcs_words: all_calls.iter().map(Vec::len).sum(),
        terms,
        relations: recorded.reduced.relations,
        code_bytes: contract.code.len(),
        field_muls: contract.field_muls,
        xors: contract.xors,
        hashes: contract.hashes,
        hashed_bytes: contract.hashed_bytes,
        checks: contract.checks,
        memory_words: contract.memory_words,
        stream_by_phase: recorded.reads.clone(),
    }
}

/// The words `calls` writes, for the Rust verifier's claims on `stream`: what the contract must write.
fn expected_words(reduced: &Reduced<E>, recorded: &Recorded, stream: &[u8]) -> Vec<[u8; 32]> {
    use leanvm_flock_gas::evm::machine::element_word;
    let number = |n: u64| {
        let mut bytes = [0u8; 32];
        bytes[24..].copy_from_slice(&n.to_be_bytes());
        bytes
    };
    let root = |at: usize| -> [u8; 32] { stream[at..at + 32].try_into().unwrap() };
    let layouts = layout_words(&recorded.shape);
    let roots = recorded.roots;
    let mut out = Vec::new();
    for (commitment, opening) in &reduced.openings {
        let (r, layout) = match commitment {
            Commitment::C1 => (root(recorded.roots_at[0]), layouts[0]),
            Commitment::C2 => (root(recorded.roots_at[1]), layouts[1]),
            Commitment::Setup => (roots.f, layouts[2]),
        };
        out.extend(opening_words(r, layout, opening, element_word, number));
    }
    if let Some(matrices) = &reduced.matrices {
        for (r, layout, value) in [(roots.a0, layouts[3], matrices.a), (roots.b0, layouts[4], matrices.b)] {
            out.extend([r, layout, number(1)]);
            out.extend(matrices.point.iter().map(|&x| element_word(x)));
            out.push(element_word(value));
        }
    }
    out
}

/// The contract, built to return what it would hand `PCS_OPEN` and every value it checks, against the Rust verifier
/// on the same calldata: word for word.
pub fn parity(shape: &Shape, iv: &[u8; 32], public_words: &[u8; 32], stream: &[u8], blake2s: Blake2s, mode: Claims) {
    parity_with(shape, iv, &SetupRoots::REFERENCE, public_words, stream, blake2s, mode);
}

/// [`parity`] for a contract that binds `setup`.
pub fn parity_with(
    shape: &Shape,
    iv: &[u8; 32],
    setup: &SetupRoots,
    public_words: &[u8; 32],
    stream: &[u8],
    blake2s: Blake2s,
    mode: Claims,
) {
    let recorded = record_verifier_with(shape, blake2s, mode, setup);
    let entry = Entry {
        name: NAME,
        iv: recorded.iv(iv),
        stream_len: recorded.stream_len,
        measure: true,
    };
    let checks = recorded.graph.zero.iter().chain(&recorded.graph.nonzero);
    let outputs: Vec<Word> = calls(&recorded)
        .concat()
        .into_iter()
        .chain(checks.map(|&(id, _)| Word::Node(id)))
        .collect();
    let contract = compile(&recorded.graph, &outputs, &Ending::Return, &entry);
    let (reduced, zero, nonzero) =
        rust_verifier_with(shape, iv, setup, public_words, stream, blake2s, mode).expect("the stream's length");
    let mut expected = expected_words(&reduced, &recorded, stream);
    expected.extend(zero.iter().chain(&nonzero).map(|&x| leanvm_flock_gas::evm::machine::element_word(x)));
    let outcome = call(&contract.code, &[], &calldata(public_words, stream), &PcsOpen::default());
    let output = outcome.output.expect("the measuring build does not revert");
    assert_eq!(output.len(), 32 * expected.len(), "words returned");
    for (k, (got, want)) in output.chunks(32).zip(&expected).enumerate() {
        assert_eq!(got, &want[..], "word {k}");
    }
}

/// What the contract writes and how it ends: the calls of `PCS_OPEN` (`verify`), or those words and every checked
/// value returned (`!verify`, for parity).
fn ends(recorded: &Recorded, iv: &[u8; 32], verify: bool, measure: bool) -> (Vec<Word>, Ending, Entry) {
    let entry = Entry {
        name: NAME,
        iv: recorded.iv(iv),
        stream_len: recorded.stream_len,
        measure,
    };
    let calls = calls(recorded);
    if verify {
        let ending = Ending::PcsOpen(calls.iter().map(Vec::len).collect());
        (calls.concat(), ending, entry)
    } else {
        let checks = recorded.graph.zero.iter().chain(&recorded.graph.nonzero);
        let outputs = calls
            .concat()
            .into_iter()
            .chain(checks.map(|&(id, _)| Word::Node(id)))
            .collect();
        (outputs, Ending::Return, entry)
    }
}

/// One deployed contract of a deployable verifier: code bytes, and its deployment (execution, and transaction gas
/// without the base under EIP-7623).
#[derive(Clone, Debug)]
pub struct ContractCost {
    pub code_bytes: usize,
    pub deployment_execution: u64,
    pub deployment_tx: u64,
}

/// The deployable verifier: a verifying call, and the contracts (the driver first).
#[derive(Clone, Debug)]
pub struct DeployableReport {
    pub report: GasReport,
    pub straight: u64,
    pub contracts: Vec<ContractCost>,
}

/// Measure the verifier as contracts of at most `limit` bytes (`leanvm_flock_gas::evm`'s linker, `crates/evm_link`):
/// deploy them, each by a transaction; run the measuring build, cut at the same places, as [`measure`] runs the one
/// contract.
pub fn measure_deployable(
    shape: &Shape,
    iv: &[u8; 32],
    blake2s: Blake2s,
    mode: Claims,
    limit: usize,
) -> DeployableReport {
    use leanvm_flock_gas::evm::codegen::{compile_deployable, compile_deployable_like};
    use leanvm_flock_gas::evm::contract::{deploy, install};
    let recorded = record_verifier(shape, blake2s, mode);
    let (outputs, ending, entry) = ends(&recorded, iv, true, false);
    let real = compile_deployable(&recorded.graph, &outputs, &ending, &entry, limit);
    let deployed = deploy(&real, &[]);
    let (outputs, ending, entry) = ends(&recorded, iv, true, true);
    let measuring = compile_deployable_like(&recorded.graph, &outputs, &ending, &entry, &real);
    assert_eq!(measuring.linked.starts(), real.linked.starts());
    let installed = install(&measuring, &[]);
    let stream = sample_stream(recorded.stream_len, 0x6A5);
    let data = calldata(&[0x5a; 32], &stream);
    let straight = measure(shape, iv, blake2s, mode);
    let calls_count = straight.calls;
    let run = |claim_gas: u64| -> Outcome {
        let outcome = installed
            .chain
            .call(installed.address, &data, &PcsOpen::attesting_all(claim_gas));
        assert_eq!(outcome.output.as_deref(), Some(&word([1, 0, 0])[..]), "the measuring run returns 1");
        assert_eq!(outcome.pcs_calls.len(), calls_count, "one call per commitment");
        outcome
    };
    let outcome = run(0);
    assert_eq!(run(1000).execution, outcome.execution + 1000 * straight.claims as u64);
    let mut phases: Vec<PhaseGas> = Vec::new();
    for (address, gas_by_pc) in &outcome.gas_by_code {
        let tags = &installed
            .contracts
            .iter()
            .find(|c| c.address == *address)
            .expect("a contract of the deployment")
            .tags;
        for (pc, &gas) in gas_by_pc.iter().enumerate() {
            if gas == 0 {
                continue;
            }
            let phase = tags.get(pc).copied().unwrap_or(CALLS);
            match phases.iter_mut().find(|p| p.phase == phase) {
                Some(p) => p.gas += gas,
                None => phases.push(PhaseGas { phase, gas }),
            }
        }
    }
    let measured = phases.iter().find(|p| p.phase == MEASURE).map_or(0, |p| p.gas);
    let parts = real.linked.parts.len();
    assert_eq!(
        measured,
        (real.checks + calls_count + parts + (parts > 0) as usize) as u64,
        "one JUMPDEST a check, a call of PCS_OPEN, a call of a part and the last part's word"
    );
    phases.retain(|p| p.phase != MEASURE);
    phases.sort_by_key(|p| std::cmp::Reverse(p.gas));
    // `deploy` deploys the parts first and the driver last.
    let mut contracts: Vec<ContractCost> = deployed
        .contracts
        .iter()
        .map(|c| ContractCost {
            code_bytes: c.code_bytes,
            deployment_execution: c.execution,
            deployment_tx: c.transaction(40),
        })
        .collect();
    contracts.rotate_right(1);
    let mut report = straight.clone();
    report.execution = outcome.execution - measured;
    report.phases = phases;
    report.code_bytes = real.linked.code_bytes();
    DeployableReport {
        report,
        straight: straight.execution,
        contracts,
    }
}

/// The deployable build against the Rust verifier: its returning build (cut where the verifying one would be) returns
/// the words the Rust verifier computes, word for word. Returns how many contracts it was cut into.
pub fn parity_deployable(
    shape: &Shape,
    iv: &[u8; 32],
    public_words: &[u8; 32],
    stream: &[u8],
    blake2s: Blake2s,
    mode: Claims,
    limit: usize,
) -> usize {
    use leanvm_flock_gas::evm::codegen::{compile_deployable, compile_deployable_like};
    use leanvm_flock_gas::evm::contract::install;
    let recorded = record_verifier(shape, blake2s, mode);
    let (outputs, ending, entry) = ends(&recorded, iv, false, false);
    let returning = compile_deployable(&recorded.graph, &outputs, &ending, &entry, limit);
    let (outputs, ending, entry) = ends(&recorded, iv, false, true);
    let installed = install(
        &compile_deployable_like(&recorded.graph, &outputs, &ending, &entry, &returning),
        &[],
    );
    let output = installed
        .chain
        .call(installed.address, &calldata(public_words, stream), &PcsOpen::default())
        .output
        .expect("a measuring build does not revert");
    let (reduced, zero, nonzero) =
        rust_verifier(shape, iv, public_words, stream, blake2s, mode).expect("the stream's length");
    let mut expected = expected_words(&reduced, &recorded, stream);
    expected.extend(zero.iter().chain(&nonzero).map(|&x| leanvm_flock_gas::evm::machine::element_word(x)));
    assert_eq!(output.len(), 32 * expected.len(), "words returned");
    for (k, (got, want)) in output.chunks(32).zip(&expected).enumerate() {
        assert_eq!(got, &want[..], "word {k}");
    }
    returning.linked.parts.len() + 1
}
