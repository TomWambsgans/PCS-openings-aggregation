// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/lib.rs: its
// errors, `verify_stacked_opening` and `walk`, the walk generic over a `Scalar` and a `Channel`, without the replay
// mode, with the shape it reads checked against the caller's, and ending either in WHIR as leanVM does
// (`verify_execution`) or in the claims a contract hands to `PCS_OPEN` (`reduce`). MIT OR Apache-2.0; see NOTICE.md.
//! The gas of verifying a leanVM proof (commit 42422001: BLAKE2s proven with Flock) in an EVM contract whose PCS
//! openings go to the block's aggregated `PCS_OPEN` precompile. See `README.md`.
//!
//! leanVM's verifier, made generic over the scalar it computes on, runs three ways:
//!
//! - [`verify_execution`]: leanVM's own verifier (BLAKE2s transcript, the bytecode evaluated, the lincheck's terminal
//!   walk, WHIR), which accepts real leanVM 42422001 proofs: the port is the protocol.
//! - [`reduce`] on `E` with the Keccak-256 chain ([`transcript::KeccakChannel`]): the contract's verifier in Rust.
//! - [`reduce`] on the recorder's symbol ([`evm`]): the graph the contract is compiled from, so the contract computes
//!   exactly what [`reduce`] does.

#![forbid(unsafe_code)]

mod bus;
mod bytecode;
pub mod evm;
mod field;
mod flock;
mod hash;
pub mod keccak_gkr;
mod layout;
pub mod matrices;
mod merkle;
mod multilinear;
pub mod scalar;
pub mod shapes;
mod stack;
pub mod transcript;
mod whir;

pub use bytecode::Bytecode;
pub use field::{E, K};
pub use flock::{FlockClaims, LincheckTerminal, verify_flock};
pub use layout::{Layout, N_TABLES, TABLE_NAMES};
pub use merkle::{MerkleOpenings, MerklePath, PrunedMerklePaths};
pub use transcript::Proof;

use bus::{ColumnClaim, table_sumcheck, verify_bus_balance};
use flock::ring_switch;
use hash::Digest;
use layout::{
    BLAKE2S_R1CS_LOG_SIZE, MAX_STACKED_LOG, MEMORY_0, MEMORY_1, MEMORY_2, MIN_STACKED_LOG, OP_BLAKE2S, QFLOCK,
    build_layout,
};
use matrices::MatrixClaim;
use multilinear::{dot, multilinear_eval};
use scalar::{Scalar, enter, powers};
use transcript::{Channel, Transcript};
use whir::verify_whir;

/// Why a proof was rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifierError {
    FieldElementLength,
    DigestHalf,
    MultilinearSize,
    NotPowerOfTwo,
    StreamNotWholeElements,
    StreamExhausted,
    GrindingNonce,
    MerkleOpeningMissing,
    MerkleOpeningShape,
    MerkleRootMismatch,
    StreamNotConsumed,
    MerkleNotConsumed,
    /// The GKR layer whose children do not match its sumcheck.
    GkrLayer(usize),
    BusCountZero,
    TableSumcheckTerminal,
    AnnouncedTableSizes,
    WhirShape,
    QueryCountLadder,
    InducedBasisDimensions,
    WhirTerminal,
    WhirNoTerminalLevel,
    FlockLincheckTerminal,
    AnnouncedHighLimb,
    PcsInverseRate,
    CommittedSize,
    /// New here: the announced sizes are not the shape the verifier was built for.
    AnnouncedShape,
    /// New here: the matrices' reduction does not close ([`matrices`]).
    FlockMatrixTerminal,
    /// New here: the stack claims' batching sumcheck does not close (`stack`).
    StackBatchTerminal,
    /// Of the Keccak GKR (leanVM 4af2cddd), ported for the estimate (`keccak_gkr`).
    KeccakProduct,
    KeccakLayer,
    KeccakOutputOpening,
    KeccakInputOpening,
}

impl std::fmt::Display for VerifierError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for VerifierError {}

fn require(condition: bool, error: VerifierError) -> Result<(), VerifierError> {
    if condition { Ok(()) } else { Err(error) }
}

/// The weight a claim puts on the stack, and the value it claims for it.
pub type StackClaim<'a, S> = (Box<dyn Fn(&[S]) -> S + 'a>, S);

/// What the announced sizes are: the memory's log size, each table's rows and WHIR's log inverse rate; and the
/// stacked bytecode's length, which the program fixes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    pub log_memory: u64,
    pub table_rows: [u64; N_TABLES],
    pub log_inv_rate: u64,
    pub bytecode_len: usize,
}

impl Shape {
    /// The announced scalars, in the order the proof sends them.
    pub fn announced(&self) -> Vec<E> {
        [self.log_memory]
            .into_iter()
            .chain(self.table_rows)
            .chain([self.log_inv_rate])
            .map(|value| E::new(value, 0, 0))
            .collect()
    }

    /// The shape a leanVM proof announces in its first scalars.
    pub fn of_proof(proof: &Proof, bytecode_len: usize) -> Result<Self, VerifierError> {
        let announced = proof.stream.get(..2 + N_TABLES).ok_or(VerifierError::StreamExhausted)?;
        require(
            announced.iter().all(|value| value.c1 == 0 && value.c2 == 0),
            VerifierError::AnnouncedHighLimb,
        )?;
        Ok(Self {
            log_memory: announced[0].c0,
            table_rows: std::array::from_fn(|t| announced[1 + t].c0),
            log_inv_rate: announced[1 + N_TABLES].c0,
            bytecode_len,
        })
    }

    pub fn layout(&self) -> Result<Layout, VerifierError> {
        require((1..=4).contains(&self.log_inv_rate), VerifierError::PcsInverseRate)?;
        let layout = build_layout(self.bytecode_len, self.log_memory, &self.table_rows)?;
        require(
            (MIN_STACKED_LOG..=MAX_STACKED_LOG).contains(&layout.stack_log),
            VerifierError::CommittedSize,
        )?;
        Ok(layout)
    }
}

/// What the walk leaves before the stacked opening.
pub struct Walked<'a, S> {
    pub layout: Layout,
    /// The stack's root, its two halves.
    pub root: [S; 2],
    /// Every claim on the stack, the ring switch's first.
    pub stack_claims: Vec<StackClaim<'a, S>>,
    pub bytecode_point: Vec<S>,
    pub bytecode_value: S,
    pub flock: FlockClaims<S>,
}

/// leanVM's walk, up to the stacked opening. `public_words` are the public input's four 64-bit words, low first.
/// `bytecode_value` gives the stacked bytecode's value at the bus's point: leanVM evaluates the bytecode; a contract
/// reads the value from the proof and leaves it as a claim on the bytecode's commitment.
pub fn walk<'a, S: Scalar + 'a, C: Channel<S>>(
    shape: &Shape,
    public_words: [S; 4],
    transcript: &mut C,
    bytecode_value: impl FnOnce(&mut C, &[S]) -> Result<S, VerifierError>,
    lincheck: LincheckTerminal,
) -> Result<Walked<'a, S>, VerifierError> {
    // 1] memory log-size, table row counts, and log-inv-rate in WHIR
    let layout = shape.layout()?;
    let announced = transcript.next_scalars(2 + N_TABLES)?;
    for (value, expected) in announced.into_iter().zip(shape.announced()) {
        let _phase = enter("announced sizes checked");
        transcript.require_zero(value + S::constant(expected), VerifierError::AnnouncedShape)?;
    }

    // 2] parse WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    let root = transcript.next_root()?;

    // 3] Bus: one batched GKR over the push, pull and count trees, then the leaf decomposition, which leaves each table a degree-2 claim.
    let bus = verify_bus_balance(&layout, transcript, bytecode_value)?;

    // 4] One batched (back-loaded) "table sumcheck" over all six tables, at the bus point, proving the target the three
    // leaf claims derive and that constraints vanish. Every table takes a disjoint range of xi powers for its constraints
    let xi = transcript.sample();
    let n_constraints: usize = layout.tables.iter().map(|table| table.n_constraints()).sum();
    let xi_powers = {
        let _phase = enter("table sumcheck: terminal (constraints, bus forms)");
        powers(xi, n_constraints + 3) // one power per constraint, then one per bus side, shared by every table
    };
    let (constraint_powers, form_powers) = xi_powers.split_at(n_constraints);
    let target = {
        let _phase = enter("table sumcheck: terminal (constraints, bus forms)");
        dot(form_powers, &bus.totals)
    };
    let table_sumcheck_claims = table_sumcheck(
        &layout.tables,
        &layout.table_log_heights,
        &bus.forms,
        constraint_powers,
        form_powers,
        &bus.point,
        target,
        transcript,
    )?;
    let mut claims = bus.claims;
    claims.extend(table_sumcheck_claims);

    // 5] binding the public input: each memory limb's claim is that limb's public line at the challenge, which the verifier
    // evaluates itself, so the prover sends nothing. Both public words are 128-bit, so the top limb's claim is zero.
    let public_challenge = transcript.sample();
    {
        let _phase = enter("public input binding");
        let mut public_point = vec![S::zero(); layout.placements[MEMORY_0].variables];
        public_point[0] = public_challenge;
        let [w0, w1, w2, w3] = public_words;
        let public_pairs = [(w0, w2), (w1, w3), (S::zero(), S::zero())];
        for (column, (low, high)) in [MEMORY_0, MEMORY_1, MEMORY_2].into_iter().zip(public_pairs) {
            claims.push(ColumnClaim {
                column,
                point: public_point.clone(),
                value: multilinear_eval(&[low, high], &[public_challenge])?,
            });
        }
    }

    // 6] BLAKE2s validity via Flock
    let flock_log_n = BLAKE2S_R1CS_LOG_SIZE + layout.table_log_heights[OP_BLAKE2S];
    let flock = verify_flock(flock_log_n, transcript, lincheck)?;

    // 7] Ring-switching
    let (ringswitch_target, ringswitch_weight) = ring_switch(flock.point(), &flock.s, transcript);
    // That claim is supported on q_flock's region of the stack, so its weight carries the
    // placement's selector, and it leads the batch, taking the first power.
    let qflock = layout.placements[QFLOCK];
    let ringswitch: StackClaim<S> = (
        Box::new(move |x| qflock.eq_above(x) * ringswitch_weight.at(&x[..qflock.variables])),
        ringswitch_target,
    );
    let mut stack_claims = vec![ringswitch];
    stack_claims.extend(claims.iter().map(|claim| claim.on_stack(&layout)));
    Ok(Walked {
        layout,
        root,
        stack_claims,
        bytecode_point: bus.bytecode_point,
        bytecode_value: bus.bytecode_value,
        flock,
    })
}

/// Discharge every claim on the committed stack in one opening: the same powers of one challenge
/// batch the values into the target, and the weights into the basis WHIR evaluates at its terminal point.
fn verify_stacked_opening(
    transcript: &mut Transcript,
    root: Digest,
    stack_log: usize,
    placed: u64,
    log_inv_rate: usize,
    claims: &[StackClaim<E>],
) -> Result<(), VerifierError> {
    let values: Vec<E> = claims.iter().map(|(_, value)| *value).collect();
    let scales = powers(transcript.sample(), claims.len());
    let evaluate_basis = |point: &[E]| {
        let weights: Vec<E> = claims.iter().map(|(weight, _)| weight(point)).collect();
        dot(&scales, &weights)
    };
    let target = dot(&scales, &values);
    verify_whir(
        transcript,
        stack_log,
        placed,
        log_inv_rate,
        target,
        root,
        &evaluate_basis,
    )
}

/// The public input's four 64-bit words, little-endian, low first: leanVM's `Digest::words`.
pub fn public_words(public_input: &[u8; 32]) -> [u64; 4] {
    Digest(*public_input).words()
}

/// leanVM 42422001's `verify_execution`, on this port: the BLAKE2s transcript, the bytecode evaluated, the lincheck's
/// terminal walk and WHIR. It accepts the proofs leanVM makes; it returns the shape and the flock claims.
pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[u8; 32],
    proof: &Proof,
) -> Result<(Shape, FlockClaims<E>), VerifierError> {
    let shape = Shape::of_proof(proof, bytecode.len())?;
    let mut transcript = Transcript::new(proof, bytecode.fiat_shamir_iv, Digest(*public_input));
    let words = public_words(public_input).map(|word| E::new(word, 0, 0));
    let walked = walk(
        &shape,
        words,
        &mut transcript,
        |_, point: &[E]| bytecode.evaluate(point),
        LincheckTerminal::Walk,
    )?;
    let root = Digest::from_halves(walked.root[0], walked.root[1])?;
    verify_stacked_opening(
        &mut transcript,
        root,
        walked.layout.stack_log,
        walked.layout.placed,
        shape.log_inv_rate as usize,
        &walked.stack_claims,
    )?;
    transcript.finish()?;
    Ok((shape, walked.flock))
}

/// One evaluation claim: a point and a value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim<S> {
    pub point: Vec<S>,
    pub value: S,
}

/// What the contract hands to `PCS_OPEN`: one claim per commitment.
#[derive(Clone, Debug)]
pub struct Reduced<S> {
    /// The stack's root, its two halves, and the one claim on it.
    pub root: [S; 2],
    pub stack: Claim<S>,
    /// On the stacked bytecode's (fixed) commitment.
    pub bytecode: Claim<S>,
    /// On `A0`'s and `B0`'s (fixed) commitments, at one point, when the lincheck's terminal is left to them.
    pub matrices: Option<[Claim<S>; 2]>,
    /// The stack's variables, the claims batched on it, and the depth of the bus's GKR.
    pub layout_stack_log: usize,
    pub stack_claims: usize,
    pub bus_depth: usize,
}

/// The contract's verifier: leanVM's walk on the Keccak-256 chain, the bytecode's value read from the proof, the
/// lincheck's terminal checked as `lincheck` says, and the stack's claims batched into one. What it leaves are the
/// claims for `PCS_OPEN`.
pub fn reduce<S: Scalar, C: Channel<S>>(
    shape: &Shape,
    public_words: [S; 4],
    transcript: &mut C,
    lincheck: LincheckTerminal,
) -> Result<Reduced<S>, VerifierError> {
    let walked = walk(
        shape,
        public_words,
        transcript,
        |t: &mut C, _: &[S]| t.next_scalar(),
        lincheck,
    )?;
    let (point, value) = stack::batch_stack_claims(transcript, walked.layout.stack_log, &walked.stack_claims)?;
    let matrices = walked.flock.matrices.map(|MatrixClaim { point, a, b }| {
        [
            Claim {
                point: point.clone(),
                value: a,
            },
            Claim { point, value: b },
        ]
    });
    Ok(Reduced {
        root: walked.root,
        stack: Claim { point, value },
        bytecode: Claim {
            point: walked.bytecode_point,
            value: walked.bytecode_value,
        },
        matrices,
        layout_stack_log: walked.layout.stack_log,
        stack_claims: walked.stack_claims.len(),
        bus_depth: bus::bus_depth(&walked.layout),
    })
}
