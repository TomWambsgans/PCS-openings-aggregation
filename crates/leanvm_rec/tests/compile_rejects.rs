// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The compiler's rejections (`circuit::compile`, as the Lean compiler's in `formal/RecCircuit/RecCircuit/Compile.lean`):
//! three kinds of recorded graph it would otherwise compile into a circuit that does not constrain what the graph means,
//! each refused with its message, and a small well-formed graph at each check's boundary still compiled, its circuit
//! holding on its witness and every node's limbs the evaluator's values.
//!
//! - a read never hashed that is not a 24-byte scalar (a root's 16-byte half, a 4-byte integer): its free limbs would
//!   leave the high limbs unconstrained, while the graph's are zero;
//! - a bit field of a 24-byte read: the circuit's field could take bits past the low limb, which `E::bits` ignores;
//! - an empty hashed read (the recorder cannot make one: the graph is built by hand).
//!
//! `cargo test --release -p leanvm_rec --test compile_rejects`

use leanvm_flock_gas::evm::record::{Graph, Node, Recorder, Sym, record};
use leanvm_flock_gas::field::K;
use leanvm_flock_gas::scalar::Scalar;
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_flock_gas::transcript::{Channel, keccak_seed};
use leanvm_rec::REFERENCE;
use leanvm_rec::circuit::compile::{Compiled, Inputs, Layout, pi2};
use leanvm_rec::eval::evaluate;
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{NAME, Recorded, SetupRoots};
use leanvm_univariate::{Blake2s, FLOCK_REC3, Opening, Reduced};

const PUBLIC: [u8; 32] = [3; 32];

/// `f` on a thread with a deep stack, its panic (if any) re-raised as is, so `should_panic` sees its message.
fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    match std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
    {
        Ok(r) => r,
        Err(panic) => std::panic::resume_unwind(panic),
    }
}

fn point(point: Vec<Sym>, value: Sym) -> Opening<Sym> {
    Opening::Point {
        point,
        value,
        bit_slice: None,
    }
}

fn recorded(graph: Graph, reduced: Reduced<Sym>, stream_len: usize, roots_at: [usize; 2]) -> Recorded {
    Recorded {
        shape: REFERENCE,
        blake2s: Blake2s::Flock(FLOCK_REC3),
        roots: SetupRoots::REFERENCE,
        graph,
        reduced,
        stream_len,
        roots_at,
        reads: vec![],
    }
}

fn reduced(roots: [[Sym; 2]; 2], openings: Vec<(Commitment, Opening<Sym>)>) -> Reduced<Sym> {
    Reduced {
        roots,
        openings,
        matrices: None,
        relations: 0,
        stack_vars: vec![],
        layouts: vec![],
    }
}

/// A small verifier on the recorder's symbol: two roots and a scalar read, a challenge `c` (so all three are hashed),
/// then `rest` (more reads and challenges), whose outputs are opening `C1`'s point after `c`. No zero check, so the
/// circuit holds on any stream.
fn small(rest: impl FnOnce(&mut Recorder) -> Vec<Sym>) -> Recorded {
    let ((stream_len, roots_at, reduced), graph) = record(|| {
        let mut r = Recorder::new();
        let root0 = r.next_root().unwrap();
        let root1 = r.next_root().unwrap();
        let a = r.next_scalar().unwrap();
        let c = r.sample();
        let mut outputs = vec![c];
        outputs.extend(rest(&mut r));
        let reduced = reduced(
            [root0, root1],
            vec![
                (Commitment::C1, point(outputs, a)),
                (Commitment::C2, point(vec![c], a * c)),
            ],
        );
        (r.cursor as usize, [r.roots[0] as usize, r.roots[1] as usize], reduced)
    });
    recorded(graph, reduced, stream_len, roots_at)
}

fn stream(recorded: &Recorded) -> Vec<u8> {
    (0..recorded.stream_len).map(|i| (i * 37 + 11) as u8).collect()
}

fn compile(recorded: &Recorded) -> Compiled {
    let stream = stream(recorded);
    pi2(
        recorded,
        Layout::D16v,
        &Inputs {
            program_iv: PROGRAM_IV,
            public: PUBLIC,
            stream: &stream,
        },
    )
}

#[test]
#[should_panic(expected = "a read never hashed is a 24-byte scalar")]
fn rejects_a_root_never_hashed() {
    // A root read after the last challenge: two 16-byte reads, never hashed, its halves a point's coordinates.
    deep(|| {
        compile(&small(|r| r.next_root().unwrap().to_vec()));
    });
}

#[test]
#[should_panic(expected = "a read never hashed is a 24-byte scalar")]
fn rejects_an_integer_never_hashed() {
    // A 4-byte integer read after the last challenge, a point's coordinate.
    deep(|| {
        compile(&small(|r| vec![r.next_integer(4).unwrap()]));
    });
}

#[test]
#[should_panic(expected = "a bit field of an integer of at most 8 bytes")]
fn rejects_a_bit_field_of_a_scalar() {
    // `x`'s low 4 bits, `x` a 24-byte scalar hashed by the challenge after it (live, so `x` is hashed).
    deep(|| {
        compile(&small(|r| {
            let x = r.next_scalar().unwrap();
            let d = r.sample();
            vec![x.bits(0, 4), d]
        }));
    });
}

#[test]
#[should_panic(expected = "a hashed read is not empty")]
fn rejects_an_empty_read() {
    // By hand: two roots' halves at bytes 0..64 with an empty read at byte 32 between them, all hashed by the
    // challenge's hash of bytes 0..64; the empty read and the challenge are the openings' words.
    deep(|| {
        let mut graph = Graph::default();
        graph.nodes.extend([
            Node::Seed,
            Node::Input { offset: 0, len: 16 },
            Node::Input { offset: 16, len: 16 },
            Node::Input { offset: 32, len: 0 },
            Node::Input { offset: 32, len: 16 },
            Node::Input { offset: 48, len: 16 },
            Node::Hash(0, 0, 64),
            Node::Low(6),
        ]);
        let (empty, c) = (Sym(3), Sym(7));
        let reduced = reduced(
            [[Sym(1), Sym(2)], [Sym(4), Sym(5)]],
            vec![
                (Commitment::C1, point(vec![c, empty], c)),
                (Commitment::C2, point(vec![c], c)),
            ],
        );
        compile(&recorded(graph, reduced, 64, [0, 32]));
    });
}

#[test]
fn compiles_the_boundary_cases() {
    // Each check's boundary, accepted: hashed integers of 1 and 8 bytes, bit fields of the 8-byte one (a single bit,
    // the top bits of its low limb), a root's hashed halves, and a 24-byte scalar never hashed.
    deep(|| {
        let recorded = small(|r| {
            let one = r.next_integer(1).unwrap();
            let eight = r.next_integer(8).unwrap();
            let root = r.next_root().unwrap();
            let d = r.sample();
            let late = r.next_scalar().unwrap();
            vec![one, eight.bits(0, 1), eight.bits(60, 4), root[0], root[1], d, late]
        });
        let c = compile(&recorded);
        assert_eq!(c.finished.circuit.check(&c.finished.witness, &c.public), Ok(()));
        // Every live node's limbs are the evaluator's value.
        let stream = stream(&recorded);
        let seed = keccak_seed(&NAME, &c.pi1_iv, &PUBLIC);
        let values = evaluate(&c.expanded, seed, &PUBLIC, &stream);
        for (&id, limbs) in &c.limbs {
            let x = values[id as usize].e();
            assert_eq!(
                limbs.map(|l| c.finished.words[l as usize]),
                [K(x.c0), K(x.c1), K(x.c2)],
                "the limbs of node {id} ({:?})",
                c.expanded.nodes[id as usize]
            );
        }
        let read = |len: u8| {
            c.limbs
                .keys()
                .any(|&id| matches!(c.expanded.nodes[id as usize], Node::Input { len: l, .. } if l == len))
        };
        assert!([1, 8, 16, 24].into_iter().all(read), "every read's length compiled");
    });
}
