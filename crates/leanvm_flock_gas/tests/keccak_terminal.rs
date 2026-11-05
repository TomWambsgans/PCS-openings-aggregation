// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The Keccak-f block's structured lincheck terminal (`keccak_flock::structured_terminal`, crates/slh_dsa/SPEC-FAST.md
//! §4.2, M3) against the walked one (`flock_min::walked_terminal_with::<_, KeccakWalked>`, M1's walk), and its cost:
//!
//! - equal at random points, challenges and slices, at every skip `0..=6` (many trials at 3 and 6), and for each of
//!   the 64 packing positions alone (`s` a unit vector) at skips 3 and 6;
//! - its `E` operations, recorded (the recorder's `Mul` and `Add` nodes), at skips 3 and 6;
//! - (ignored) the Flock-for-Keccak verifier at `log_n = 29`, skip 3, `FsShape::Rec3`, recorded, compiled and run on
//!   revm (`measure_fragment`): scalars, Keccak-256 calls and Keccak-f, `FIELD_MUL`s, the terminal's share.
//!
//! `cargo test --release -p leanvm_flock_gas --test keccak_terminal -- --include-ignored --nocapture`.

use leanvm_flock_gas::evm::contract::measure_fragment;
use leanvm_flock_gas::evm::record::{Node, Recorder, Sym, record};
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::flock_min::{self, End, Slices, Variant, WalkedCircuit, walked_terminal_with};
use leanvm_flock_gas::keccak_flock::{Keccak, KeccakWalked, structured_terminal};
use leanvm_flock_gas::scalar::{Scalar, enter};
use leanvm_flock_gas::transcript::{Channel, FsShape};

const LINCHECK_ROUNDS: usize = 11;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn e(&mut self) -> E {
        E::new(self.next(), self.next(), self.next())
    }
    fn es(&mut self, n: usize) -> Vec<E> {
        (0..n).map(|_| self.e()).collect()
    }
}

/// The terminal's inputs at a skip of `k`.
struct Inputs {
    z_skip: Option<E>,
    row_low: Vec<E>,
    chi_in: Vec<E>,
    chi_in_prime: Vec<E>,
    s: Vec<E>,
    alpha: E,
}

impl Inputs {
    fn random(rng: &mut Rng, k: usize) -> Self {
        Self {
            z_skip: (k > 0).then(|| rng.e()),
            row_low: rng.es(6 - k),
            chi_in: rng.es(LINCHECK_ROUNDS),
            chi_in_prime: rng.es(LINCHECK_ROUNDS),
            s: rng.es(64),
            alpha: rng.e(),
        }
    }

    fn both(&self) -> (E, E) {
        let walked = walked_terminal_with::<E, KeccakWalked>(
            self.z_skip,
            &self.row_low,
            &self.chi_in,
            &self.chi_in_prime,
            &self.s,
            self.alpha,
        );
        let structured =
            structured_terminal(self.z_skip, &self.row_low, &self.chi_in, &self.chi_in_prime, &self.s, self.alpha);
        (walked, structured)
    }
}

#[test]
fn structured_equals_walked_at_random_points() {
    let mut rng = Rng(0x4d33_7e41);
    for k in 0..=6 {
        let trials = if k == 3 || k == 6 { 24 } else { 3 };
        for trial in 0..trials {
            let inputs = Inputs::random(&mut rng, k);
            let (walked, structured) = inputs.both();
            assert_eq!(structured, walked, "skip {k}, trial {trial}");
        }
    }
}

/// Each packing position alone (`s = e_i`), so no position's terms can cancel another's; and the trait's terminal
/// for `Keccak` is the structured one, for `KeccakWalked` the walk.
#[test]
fn structured_equals_walked_at_every_packing_position() {
    let mut rng = Rng(0x0064_b175);
    for k in [3, 6] {
        let mut inputs = Inputs::random(&mut rng, k);
        for i in 0..64 {
            inputs.s = (0..64).map(|j| if i == j { E::new(1, 0, 0) } else { E::new(0, 0, 0) }).collect();
            let (walked, structured) = inputs.both();
            assert_eq!(structured, walked, "skip {k}, position {i}");
            // And a random weight there, other points.
            let mut other = Inputs::random(&mut rng, k);
            let weight = rng.e();
            other.s = (0..64).map(|j| if i == j { weight } else { E::new(0, 0, 0) }).collect();
            let (walked, structured) = other.both();
            assert_eq!(structured, walked, "skip {k}, position {i}, random");
        }
        let i = &inputs;
        assert_eq!(
            Keccak::terminal(i.z_skip, &i.row_low, &i.chi_in, &i.chi_in_prime, &i.s, i.alpha),
            KeccakWalked::terminal(i.z_skip, &i.row_low, &i.chi_in, &i.chi_in_prime, &i.s, i.alpha),
        );
    }
}

/// The recorded `E` operations of the terminal alone: (products, of which by a constant, sums).
fn terminal_ops(k: usize, terminal: impl FnOnce(Option<Sym>, &[Sym], &[Sym], &[Sym], &[Sym], Sym) -> Sym) -> (usize, usize, usize) {
    const PHASE: &str = "keccak terminal under test";
    let (_, graph) = record(|| {
        let mut recorder = Recorder::new();
        let mut next = |n: usize| recorder.next_scalars(n).expect("recorded");
        let z_skip = (k > 0).then(|| next(1)[0]);
        let (row_low, chi_in, chi_in_prime, s, alpha) =
            (next(6 - k), next(LINCHECK_ROUNDS), next(LINCHECK_ROUNDS), next(64), next(1)[0]);
        let _phase = enter(PHASE);
        terminal(z_skip, &row_low, &chi_in, &chi_in_prime, &s, alpha)
    });
    let is_const = |at: u32| matches!(graph.nodes[at as usize], Node::Const(_));
    let (mut muls, mut const_muls, mut adds) = (0, 0, 0);
    for (node, phase) in graph.nodes.iter().zip(&graph.phases) {
        if *phase != PHASE {
            continue;
        }
        match *node {
            Node::Mul(a, b) => {
                muls += 1;
                if is_const(a) || is_const(b) {
                    const_muls += 1;
                }
            }
            Node::Add(..) => adds += 1,
            _ => {}
        }
    }
    (muls, const_muls, adds)
}

#[test]
fn structured_terminal_ops() {
    for k in [3, 6] {
        let (muls, const_muls, adds) = terminal_ops(k, structured_terminal::<Sym>);
        println!(
            "Keccak structured terminal, skip {k}: {} E ops ({muls} products, {const_muls} of them by a constant; {adds} sums)",
            muls + adds
        );
        assert!(muls + adds <= 15_000, "skip {k}: within M3's 15K");
    }
}

fn deep<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("no panic")
}

/// The walk's count, for comparison (about 1.4M sums).
#[test]
#[ignore]
fn walked_terminal_ops() {
    deep(|| {
        for k in [3] {
            let (muls, const_muls, adds) = terminal_ops(k, walked_terminal_with::<Sym, KeccakWalked>);
            println!(
                "Keccak walked terminal, skip {k}: {} E ops ({muls} products, {const_muls} by a constant; {adds} sums)",
                muls + adds
            );
        }
    });
}

/// Flock for 4,096 Keccak-f (`log_n = 29`) with the structured terminal, as π2 would record it: π1-rec3's shape.
#[test]
#[ignore]
fn flock_keccak_verifier_fragment() {
    deep(|| {
        for (skip, fs) in [(3, FsShape::Rec3), (3, FsShape::Rec), (6, FsShape::Rec3)] {
            let log_n = 29;
            let variant = Variant {
                skip,
                slices: Slices::TowerWalk,
                fs,
            };
            let mut keccak_f = 0;
            let mut ops = (0, 0);
            let fragment = measure_fragment(|recorder| {
                let (point, end) = flock_min::verify_walked_with::<Sym, Keccak>(log_n, variant, recorder).expect("recorded");
                let mut outputs = point;
                match end {
                    End::Ring { map, target, .. } => outputs.extend(map.into_iter().chain([target])),
                    End::Combination { weights, value } => outputs.extend(weights.into_iter().chain([value])),
                }
                outputs
            });
            // Keccak-f blocks of each hash, and the arithmetic, from a second recording (measure_fragment keeps its
            // graph).
            let (_, graph) = record(|| {
                let mut recorder = Recorder::new();
                flock_min::verify_walked_with::<Sym, Keccak>(log_n, variant, &mut recorder).expect("recorded")
            });
            for node in &graph.nodes {
                match *node {
                    Node::Hash(_, from, to) => keccak_f += (32 + (to - from) as usize + 1).div_ceil(136),
                    Node::Seed => keccak_f += 1,
                    Node::Mul(..) => ops.0 += 1,
                    Node::Add(..) => ops.1 += 1,
                    _ => {}
                }
            }
            println!(
                "Flock for Keccak-f, log_n {log_n}, skip {skip}, {fs:?}, structured terminal: stream {} B ({} scalars), \
                 KECCAK256 {}, Keccak-f {keccak_f}, FIELD_MUL {}, XOR {}, execution {}; recorded products {}, sums {}",
                fragment.stream_bytes,
                fragment.stream_bytes / 24,
                fragment.hashes,
                fragment.field_muls,
                fragment.xors,
                fragment.execution,
                ops.0,
                ops.1
            );
            for phase in &fragment.phases {
                println!("  {}: {} gas", phase.phase, phase.gas);
            }
        }
    });
}
