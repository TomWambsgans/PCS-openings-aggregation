// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The vectors of `formal/RecCircuit`'s differential runner (`RecCircuitTest/Main.lean`): a recorded graph as text, and
//! the circuit the Rust compiler makes of it (`circuit::compile::pi2`, D16v), summarised: the shape, the regions and
//! their formula tables, the blocks, the ports, the calls, `κ`, and a hash of `σ`. The Lean compiler reads the graph,
//! compiles it, and prints the same summary; the runner compares them.
//!
//! The graphs: three small ones, recorded here on the recorder's symbol (reads, roots, challenges, a narrow challenge,
//! sums, products, squares, constants, bit fields, a ring-switch weight, zero checks, a paired challenge, a read never
//! hashed, multi-block hashes), and π1-rec3's (`record_verifier` at the reference shape, `FLOCK_REC3`).
//!
//! `LEAN_CIRCUIT_OUT=dir cargo test --release -p leanvm_rec --test lean_circuit -- --include-ignored --nocapture --test-threads 1`

use std::fmt::Write;

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::evm::codegen::Word;
use leanvm_flock_gas::evm::record::{Node, Recorder, Sym, record};
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::scalar::Scalar;
use leanvm_flock_gas::shapes::PROGRAM_IV;
use leanvm_flock_gas::transcript::{Channel, cantor_beta1};
use leanvm_rec::REFERENCE;
use leanvm_rec::circuit::compile::{Inputs, Layout, pi2};
use leanvm_rec::circuit::spec::{CallWord, Circuit, Formula, Source};
use leanvm_univariate::claims::Commitment;
use leanvm_univariate::contract::{Recorded, SetupRoots, calls, record_verifier};
use leanvm_univariate::{Blake2s, Claims, FLOCK_REC3, Opening, Reduced};

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn word_hex(bytes: &[u8; 32]) -> String {
    let h = hex(bytes);
    let t = h.trim_start_matches('0');
    if t.is_empty() { "0".into() } else { t.into() }
}

fn node_line(node: &Node) -> String {
    match *node {
        Node::Const([a, b, c]) => format!("C {a} {b} {c}"),
        Node::Statement(k) => format!("S {k}"),
        Node::Input { offset, len } => format!("I {offset} {len}"),
        Node::Add(a, b) => format!("A {a} {b}"),
        Node::Mul(a, b) => format!("M {a} {b}"),
        Node::Seed => "D".into(),
        Node::Hash(s, f, t) => format!("H {s} {f} {t}"),
        Node::Low(h) => format!("L {h}"),
        Node::Narrow(h) => format!("N {h}"),
        Node::Bits(v, s, w) => format!("B {v} {s} {w}"),
        Node::RingWeight(k, n) => format!("W {k} {n}"),
    }
}

/// The graph as the Lean runner reads it.
fn graph_text(recorded: &Recorded) -> String {
    let g = &recorded.graph;
    let mut out = String::new();
    let o = &mut out;
    writeln!(o, "graph").unwrap();
    writeln!(o, "iv {}", hex(&recorded.iv(&PROGRAM_IV))).unwrap();
    writeln!(o, "stream_len {}", recorded.stream_len).unwrap();
    writeln!(o, "roots_at {} {}", recorded.roots_at[0], recorded.roots_at[1]).unwrap();
    writeln!(o, "nodes {}", g.nodes.len()).unwrap();
    for n in &g.nodes {
        writeln!(o, "{}", node_line(n)).unwrap();
    }
    let ids = |l: &[(u32, VerifierError)]| l.iter().map(|(i, _)| format!(" {i}")).collect::<String>();
    writeln!(o, "zero {}{}", g.zero.len(), ids(&g.zero)).unwrap();
    writeln!(o, "nonzero {}{}", g.nonzero.len(), ids(&g.nonzero)).unwrap();
    writeln!(o, "kernels {}", g.kernels.len()).unwrap();
    for k in &g.kernels {
        writeln!(o, "kernel {}{}", k.len(), k.iter().map(|i| format!(" {i}")).collect::<String>()).unwrap();
    }
    let cs = calls(recorded);
    writeln!(o, "calls {}", cs.len()).unwrap();
    for c in &cs {
        let words: String = c
            .iter()
            .map(|w| match w {
                Word::Node(id) => format!(" n{id}"),
                Word::Const(bytes) => format!(" c{}", word_hex(bytes)),
                Word::Stream(at) => format!(" t{at}"),
                Word::Stored(_) => panic!("no stored words"),
            })
            .collect();
        writeln!(o, "call {}{words}", c.len()).unwrap();
    }
    writeln!(o, "end").unwrap();
    out
}

fn formula_text(f: &Formula) -> String {
    match f {
        Formula::Forward => "F".into(),
        Formula::Expr(p) => {
            let mut s = format!("E {}", p.linear.len());
            for &(c, k) in &p.linear {
                write!(s, " {c}:{:x}", k.0).unwrap();
            }
            write!(s, " {}", p.quadratic.len()).unwrap();
            for &(a, b, k) in &p.quadratic {
                write!(s, " {a}:{b}:{:x}", k.0).unwrap();
            }
            s
        }
        Formula::Port(limbs) => {
            format!("P {}{}", limbs.len(), limbs.iter().map(|l| format!(" {l}")).collect::<String>())
        }
    }
}

fn source_text(s: Source) -> String {
    match s {
        Source::Statement => "S".into(),
        Source::Root(i) => format!("R {i}"),
        Source::Element(i) => format!("E {i}"),
        Source::Zero => "Z".into(),
        Source::Pad => "P".into(),
    }
}

/// The circuit's summary, as the Lean runner prints its own.
fn circuit_text(c: &Circuit) -> String {
    let mut out = String::new();
    let o = &mut out;
    writeln!(o, "circuit").unwrap();
    writeln!(o, "log_n {} log_width {}", c.log_n, c.log_width).unwrap();
    writeln!(o, "regions {}", c.regions.len()).unwrap();
    for r in &c.regions {
        writeln!(o, "region {}", r.name).unwrap();
        for f in &r.roles {
            writeln!(o, " {}", formula_text(f)).unwrap();
        }
    }
    writeln!(o, "blocks {}", c.blocks.len()).unwrap();
    for b in &c.blocks {
        writeln!(o, "block {} {} {}", b.row, b.log_rows, b.region).unwrap();
    }
    writeln!(o, "ports {}", c.ports.len()).unwrap();
    for p in &c.ports {
        writeln!(o, "port {} {}", p.position, source_text(p.source)).unwrap();
    }
    writeln!(o, "calls {}", c.calls.len()).unwrap();
    for call in &c.calls {
        let words: String = call
            .iter()
            .map(|w| match *w {
                CallWord::Const(bytes) => format!(" C{}", word_hex(&bytes)),
                CallWord::Root(i) => format!(" R{i}"),
                CallWord::Element(i) => format!(" E{i}"),
                CallWord::Pair { element, coordinate } => format!(" Q{element}:{coordinate}"),
            })
            .collect();
        writeln!(o, "call {}{words}", call.len()).unwrap();
    }
    writeln!(o, "kappa {}", c.kappa.len()).unwrap();
    for &(i, k) in &c.kappa {
        writeln!(o, "k {i} {:x}", k.0).unwrap();
    }
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &s in &c.sigma {
        h = (h ^ s as u64).wrapping_mul(0x0000_0100_0000_01b3);
    }
    writeln!(o, "sigma {} {h:x}", c.sigma.len()).unwrap();
    writeln!(o, "end").unwrap();
    out
}

fn emit(name: &str, recorded: &Recorded) {
    let stream: Vec<u8> = (0..recorded.stream_len).map(|i| (i * 37 + 11) as u8).collect();
    let c = pi2(
        recorded,
        Layout::D16v,
        &Inputs {
            program_iv: PROGRAM_IV,
            public: [3; 32],
            stream: &stream,
        },
    );
    let graph = graph_text(recorded);
    let circuit = circuit_text(&c.finished.circuit);
    println!(
        "{name}: {} nodes ({} expanded), N = 2^{}, {} regions, {} blocks, {} ports, {} κ",
        recorded.graph.nodes.len(),
        c.expanded.nodes.len(),
        c.finished.circuit.log_n,
        c.finished.circuit.regions.len(),
        c.finished.circuit.blocks.len(),
        c.finished.circuit.ports.len(),
        c.finished.circuit.kappa.len()
    );
    if let Ok(dir) = std::env::var("LEAN_CIRCUIT_OUT") {
        std::fs::create_dir_all(&dir).expect("the output directory");
        std::fs::write(format!("{dir}/{name}.graph"), graph).expect("the graph");
        std::fs::write(format!("{dir}/{name}.circuit"), circuit).expect("the circuit");
    }
}

/// A small verifier on the recorder's symbol: `kind` varies its reads, hashes and checks.
fn small(kind: usize) -> Recorded {
    let ((stream_len, roots_at, reduced), graph) = record(|| {
        let mut r = Recorder::new();
        let st = Recorder::statement();
        let root0 = r.next_root().unwrap();
        let a = r.next_scalar().unwrap();
        // A multi-block hash: many reads before the first challenge.
        let mut acc = a;
        for _ in 0..(3 + 4 * kind) {
            let x = r.next_scalar().unwrap();
            acc = acc * x + x;
        }
        let c = r.sample();
        let n = r.next_integer(4).unwrap();
        let bit = n.bits(3, 1);
        let field = n.bits(5, 9);
        let none = n.bits(40, 3);
        let root1 = r.next_root().unwrap();
        let b = r.next_scalar().unwrap();
        let z = r.sample_narrow();
        let k = Sym::constant(E::new(5, 6 + kind as u64, 7));
        let x = a * c + b * b + st[1] + k * a + acc;
        let y = field * x + bit + none;
        r.require_zero(x + y, VerifierError::StreamExhausted).unwrap();
        r.require_zero(Sym::constant(E::new(0, 0, 0)), VerifierError::StreamExhausted).unwrap();
        r.require_zero(y * y + c, VerifierError::StreamExhausted).unwrap();
        if kind > 0 {
            r.require_zero(x * c + st[3], VerifierError::StreamExhausted).unwrap();
        }
        let y1 = z.square() + z;
        let y0 = z + Sym::constant(cantor_beta1()) * y1;
        let w = Sym::ring_weight(&[a, b], &[c, x], &[y, x, b, a, c, k]);
        let late = r.next_scalar().unwrap();
        let reduced = Reduced {
            roots: [root0, root1],
            openings: vec![
                (
                    Commitment::C1,
                    Opening::Point {
                        point: vec![y0, y1, x, late],
                        value: w,
                        bit_slice: None,
                    },
                ),
                (
                    Commitment::C2,
                    Opening::Point {
                        point: vec![c, z, k],
                        value: y * late,
                        bit_slice: None,
                    },
                ),
            ],
            matrices: None,
            relations: 0,
            stack_vars: vec![],
            layouts: vec![],
        };
        (r.cursor as usize, [r.roots[0] as usize, r.roots[1] as usize], reduced)
    });
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

#[test]
fn small_graphs() {
    for kind in 0..3 {
        deep(move || emit(&format!("small{kind}"), &small(kind)));
    }
}

#[test]
#[ignore = "π1-rec3's whole graph and circuit (2^24 positions): about a minute"]
fn pi1_rec3() {
    deep(|| {
        let recorded = record_verifier(&REFERENCE, Blake2s::Flock(FLOCK_REC3), Claims::Point);
        emit("pi1_rec3", &recorded)
    });
}
