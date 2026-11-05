// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! π1's verifier recorded (`leanvm_flock_gas::evm::record`, as π2 will compile it, SPEC-REC.md §1): its live nodes
//! by kind and by phase, the Keccak-256 calls and their Keccak-f\[1600\] permutations, and the compiled fragment's
//! `FIELD_MUL`s (`measure_fragment`, revm), with the structured Keccak terminal (M3) and with the walked one (M1's
//! reference), and the totals without the terminal.
//!
//! `cargo test --release -p slh_fast --test ops -- --nocapture` (`--ignored` for the walked terminal: 1.4M nodes).

use std::collections::BTreeMap;

use leanvm_flock_gas::evm::contract::measure_fragment;
use leanvm_flock_gas::evm::record::{Graph, Node, Recorder, Sym, record};
use leanvm_flock_gas::flock_min::WalkedCircuit;
use leanvm_flock_gas::keccak_flock::{Keccak, KeccakWalked};
use leanvm_univariate::verifier::Opening;
use slh_fast::Params;
use slh_fast::verifier::{Reduced, reduce};

const P: Params = Params::SLH_128S;

fn statement() -> [Sym; 8] {
    std::array::from_fn(|k| Sym::new(Node::Statement(k as u8)))
}

/// What π2 must output: the roots and the three claims' points and values.
fn outputs(reduced: &Reduced<Sym>) -> Vec<Sym> {
    let mut out: Vec<Sym> = reduced.roots.iter().flatten().copied().collect();
    for (_, opening) in &reduced.openings {
        let Opening::Point { point, value, .. } = opening else { unreachable!() };
        out.extend(point.iter().copied().chain([*value]));
    }
    out
}

/// The nodes the outputs and the checks read, through their operands.
fn live(graph: &Graph, outputs: &[Sym]) -> Vec<bool> {
    let mut live = vec![false; graph.nodes.len()];
    let mut stack: Vec<u32> = outputs.iter().map(|s| s.0).chain(graph.zero.iter().map(|z| z.0)).chain(graph.nonzero.iter().map(|z| z.0)).collect();
    while let Some(id) = stack.pop() {
        if std::mem::replace(&mut live[id as usize], true) {
            continue;
        }
        match graph.nodes[id as usize] {
            Node::Add(a, b) | Node::Mul(a, b) => stack.extend([a, b]),
            Node::Hash(s, _, _) => stack.push(s),
            Node::Low(h) | Node::Narrow(h) | Node::Bits(h, _, _) => stack.push(h),
            Node::RingWeight(k, _) => stack.extend(graph.kernels[k as usize].iter().copied()),
            _ => {}
        }
    }
    live
}

#[derive(Default, Debug, Clone, Copy)]
struct Ops {
    muls: usize,
    const_muls: usize,
    adds: usize,
    hashes: usize,
    keccak_f: usize,
    reads: usize,
}

fn counts<T: WalkedCircuit>() -> (BTreeMap<&'static str, Ops>, Ops, usize) {
    let ((reduced, stream), graph) = record(|| {
        let mut recorder = Recorder::new();
        let reduced = reduce::<Sym, _, T>(&P, statement(), &mut recorder).expect("a recorder rejects nothing");
        (reduced, recorder.cursor as usize)
    });
    let live = live(&graph, &outputs(&reduced));
    let is_const = |id: u32| matches!(graph.nodes[id as usize], Node::Const(_));
    let mut by_phase: BTreeMap<&'static str, Ops> = BTreeMap::new();
    let mut total = Ops::default();
    for (id, (node, phase)) in graph.nodes.iter().zip(&graph.phases).enumerate() {
        if !live[id] {
            continue;
        }
        let entry = by_phase.entry(phase).or_default();
        for ops in [&mut *entry, &mut total] {
            match *node {
                Node::Mul(a, b) => {
                    ops.muls += 1;
                    ops.const_muls += (is_const(a) || is_const(b)) as usize;
                }
                Node::Add(..) => ops.adds += 1,
                Node::Hash(_, from, to) => {
                    ops.hashes += 1;
                    ops.keccak_f += (32 + (to - from) as usize + 1).div_ceil(136);
                }
                // The seed: 16 + 32 + 64 bytes.
                Node::Seed => {
                    ops.hashes += 1;
                    ops.keccak_f += (112usize + 1).div_ceil(136);
                }
                Node::Input { .. } => ops.reads += 1,
                _ => {}
            }
        }
    }
    (by_phase, total, stream)
}

/// The ring switch's kernel at `q_flock`'s point (one `RingWeight` node of the graph, hand-scheduled code in the
/// contract), expanded: `ring_tower::weight_at` recorded on fresh inputs. (products, by a constant, sums.)
fn kernel_ops() -> (usize, usize, usize) {
    use leanvm_flock_gas::transcript::Channel;
    let vars = P.qflock_vars();
    let (_, graph) = record(|| {
        let mut recorder = Recorder::new();
        let point = recorder.next_scalars(vars).expect("recorded");
        let one_plus_r = recorder.next_scalars(vars).expect("recorded");
        let map = recorder.next_scalars(leanvm_flock_gas::ring_tower::STAGES).expect("recorded");
        leanvm_flock_gas::ring_tower::weight_at(&point, &one_plus_r, &map)
    });
    let is_const = |id: u32| matches!(graph.nodes[id as usize], Node::Const(_));
    let (mut muls, mut consts, mut adds) = (0, 0, 0);
    for node in &graph.nodes {
        match *node {
            Node::Mul(a, b) => {
                muls += 1;
                consts += (is_const(a) || is_const(b)) as usize;
            }
            Node::Add(..) => adds += 1,
            _ => {}
        }
    }
    (muls, consts, adds)
}

fn report<T: WalkedCircuit>(name: &str) {
    let (by_phase, total, stream) = counts::<T>();
    let terminal = by_phase.get(T::TERMINAL_PHASE).copied().unwrap_or_default();
    let fragment = measure_fragment(|recorder| {
        let reduced = reduce::<Sym, _, T>(&P, statement(), recorder).expect("recorded");
        outputs(&reduced)
    });
    println!("π1 verifier, {name} terminal: stream {stream} B ({} scalars)", stream / 24);
    println!(
        "  recorded (live): {} products ({} by a constant), {} sums; {} Keccak-256 calls, {} Keccak-f; {} reads",
        total.muls, total.const_muls, total.adds, total.hashes, total.keccak_f, total.reads
    );
    println!(
        "  without the terminal: {} products ({} by a constant), {} sums",
        total.muls - terminal.muls,
        total.const_muls - terminal.const_muls,
        total.adds - terminal.adds
    );
    let (kernel_muls, kernel_consts, kernel_adds) = kernel_ops();
    println!(
        "  the ring kernel (one node above), expanded: {kernel_muls} products ({kernel_consts} by a constant), {kernel_adds} sums"
    );
    println!(
        "  compiled: KECCAK256 {}, FIELD_MUL {}, XOR {}, execution {} gas",
        fragment.hashes, fragment.field_muls, fragment.xors, fragment.execution
    );
    for (phase, ops) in &by_phase {
        println!(
            "    {phase:<64} {:>7} products ({:>6} const) {:>8} sums {:>3} hashes {:>3} Keccak-f",
            ops.muls, ops.const_muls, ops.adds, ops.hashes, ops.keccak_f
        );
    }
    let mut gas: Vec<_> = fragment.phases.iter().map(|p| (p.phase, p.gas)).collect();
    gas.sort_by_key(|&(_, g)| std::cmp::Reverse(g));
    for (phase, g) in gas {
        println!("    gas {phase:<60} {g:>9}");
    }
}

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new().stack_size(1 << 30).spawn(f).expect("a thread").join().expect("no panic")
}

#[test]
fn verifier_ops_structured() {
    deep(|| {
        report::<Keccak>("structured (M3)");
        let (_, total, _) = counts::<Keccak>();
        assert!(total.keccak_f <= 100, "the recorded graph within 100 Keccak-f (SPEC-FAST M4)");
    });
}

#[test]
#[ignore]
fn verifier_ops_walked() {
    deep(|| report::<KeccakWalked>("walked (M1)"));
}
