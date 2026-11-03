// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The circuit's small units (SPEC-REC.md §2.4.3, §2.4.4, §2.4.6), each a few consecutive roles of a row type, packed
//! as many to a row as fit:
//!
//! - **free bits**: a self-loop pushing `b²` to itself (so `b = b²`), alone, or with a slot copying `b` for a value that
//!   must end at a slot (a permutation's input);
//! - **packings**: `Σ_e b_e x^e`, Horner by windows of 15 bits from the top (`acc·x^15 + Σ_(i<15) b_(15t+i) x^i`);
//! - **`E` units** on `K`-limbs, `E = K[y]/(y³ + y + 1)`: a product, a square, a sum. The *slot operand*'s three limbs
//!   are the slots, read and ended there; the other operand is forwarded. When neither operand can end there (each
//!   value ends at one slot only), the unit has three more slots, its operands both forwarded;
//! - **ports**: the limbs forwarded into a row whose last role pushes their fingerprint outside.

use leanvm_flock_gas::field::K;

use super::keccak::Constants;
use super::layout::{Builder, PolyBuilder, Units, Value, forwards};
use super::spec::{Formula, Source};

/// Free bits.
pub struct Bools {
    /// A self-loop and its copy (a bit that needs no copy leaves it junk: one region, fewer selectors).
    copied: Units,
}

impl Bools {
    pub fn new(b: &mut Builder) -> Self {
        let w = b.width();
        let square = |c: usize| Formula::Expr(PolyBuilder::new().quadratic(c, c, 1).build());
        let copied = b.region(
            "bit+copy",
            (0..w)
                .map(|c| {
                    if c % 2 == 0 {
                        square(c)
                    } else {
                        Formula::Expr(PolyBuilder::new().linear(c - 1, 1).build())
                    }
                })
                .collect(),
        );
        Self {
            copied: Units::new(copied, 2, w / 2),
        }
    }

    /// A free bit: its value (ended at its own self-loop).
    pub fn bit(&mut self, b: &mut Builder, bit: bool) -> Value {
        let (v, _junk) = self.bit_and_copy(b, bit);
        v
    }

    /// A free bit and a copy of it: `(b, b')`; `b'` may end at another slot.
    pub fn bit_and_copy(&mut self, b: &mut Builder, bit: bool) -> (Value, Value) {
        let (row, role) = self.copied.next(b);
        let v = b.produce_given(row, role, K(bit as u64));
        b.place(row, role, v);
        (v, b.produce(row, role + 1))
    }
}

/// Packings of bits into a `K` word.
pub struct Packer {
    /// The top window of at most [`TOP`] bits: `Σ_(i<4) b_i x^i`.
    top: Units,
    next: Units,
    zero: Option<Value>,
}

/// The top window's width (a 64-bit limb's: `64 = 4 + 4·15`). A wider top window is a `pack` unit whose accumulator
/// is a fresh zero.
pub const TOP: usize = 4;

/// Horner's window.
pub const WINDOW: usize = 15;

impl Packer {
    pub fn new(b: &mut Builder) -> Self {
        let w = b.width();
        let mut roles = forwards(w);
        for u in 0..w / 16 {
            let base = 16 * u;
            let mut p = PolyBuilder::new().linear(base + 15, 1 << WINDOW);
            for i in 0..WINDOW {
                p.add_linear(base + i, 1 << i);
            }
            roles[base + 15] = Formula::Expr(p.build());
        }
        let next = b.region("pack", roles);
        let size = TOP + 1;
        let mut roles = forwards(w);
        for u in 0..w / size {
            let base = size * u;
            let mut p = PolyBuilder::new();
            for i in 0..TOP {
                p.add_linear(base + i, 1 << i);
            }
            roles[base + TOP] = Formula::Expr(p.build());
        }
        let top = b.region(&format!("pack-top{TOP}"), roles);
        Self {
            top: Units::new(top, size, w / size),
            next: Units::new(next, 16, w / 16),
            zero: None,
        }
    }

    /// `Σ b x^e` over `(e, b)`, exponents distinct and below 64; absent exponents in a window read a shared zero.
    pub fn pack(&mut self, b: &mut Builder, consts: &mut Constants, bits: &[(usize, Value)]) -> Value {
        assert!(!bits.is_empty());
        let mut at: Vec<Option<Value>> = vec![None; 64];
        for &(e, v) in bits {
            assert!(e < 64 && at[e].is_none(), "distinct exponents below 64");
            at[e] = Some(v);
        }
        let top_e = bits.iter().map(|&(e, _)| e).max().expect("a bit");
        let t_top = top_e / WINDOW;
        let top_k = top_e - WINDOW * t_top + 1;
        // The windows' cells: absent exponents (and a short top window's) read a shared zero, at forwards.
        let k_of = |t: usize| if t == t_top && top_k <= TOP { TOP } else { WINDOW };
        if (0..=t_top).any(|t| (0..k_of(t)).any(|i| at.get(WINDOW * t + i).copied().flatten().is_none()))
            && self.zero.is_none()
        {
            self.zero = Some(consts.fresh(b, K(0)));
        }
        let mut acc: Option<Value> = None;
        for t in (0..=t_top).rev() {
            let lo = WINDOW * t;
            let k = k_of(t);
            let cells: Vec<Value> = (0..k)
                .map(|i| {
                    at.get(lo + i)
                        .copied()
                        .flatten()
                        .or(self.zero)
                        .expect("a zero when a bit is absent")
                })
                .collect();
            let (row, base, acc_role) = match acc {
                None if k == TOP => {
                    let (row, base) = self.top.next(b);
                    (row, base, base + TOP)
                }
                None => {
                    // A wide top window: a `pack` unit from a fresh zero (it ends at the accumulator's slot).
                    let (row, base) = self.next.next(b);
                    let zero = consts.fresh(b, K(0));
                    b.place(row, base + 15, zero);
                    (row, base, base + 15)
                }
                Some(prev) => {
                    let (row, base) = self.next.next(b);
                    b.place(row, base + 15, prev);
                    (row, base, base + 15)
                }
            };
            for (i, &v) in cells.iter().enumerate() {
                b.place(row, base + i, v);
            }
            acc = Some(b.produce(row, acc_role));
        }
        acc.expect("a window")
    }
}

/// An element of `E` as three limb values.
pub type Limbs = [Value; 3];

/// Which `E` operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Mul,
    Add,
    Square,
}

/// The limbs of `a·b`, `a + b`, `a²` as polynomials of the cells `a` at `ra[l]`, `b` at `rb[l]`.
fn op_polys(op: Op, ra: [usize; 3], rb: [usize; 3]) -> [PolyBuilder; 3] {
    let q = |p: &mut PolyBuilder, i: usize, j: usize| p.add_quadratic(ra[i], rb[j], 1);
    let mut c: [PolyBuilder; 3] = Default::default();
    match op {
        Op::Add => {
            for l in 0..3 {
                c[l].add_linear(ra[l], 1);
                c[l].add_linear(rb[l], 1);
            }
        }
        Op::Mul => {
            // y³ = y + 1: c0 = a0b0 + a1b2 + a2b1, c1 = a0b1 + a1b0 + a1b2 + a2b1 + a2b2, c2 = a0b2 + a1b1 + a2b0 + a2b2.
            for (i, j) in [(0, 0), (1, 2), (2, 1)] {
                q(&mut c[0], i, j);
            }
            for (i, j) in [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)] {
                q(&mut c[1], i, j);
            }
            for (i, j) in [(0, 2), (1, 1), (2, 0), (2, 2)] {
                q(&mut c[2], i, j);
            }
        }
        Op::Square => {
            // (a0 + a1 y + a2 y²)² = a0² + a2² y + (a1² + a2²) y².
            c[0].add_quadratic(ra[0], ra[0], 1);
            c[1].add_quadratic(ra[2], ra[2], 1);
            c[2].add_quadratic(ra[1], ra[1], 1);
            c[2].add_quadratic(ra[2], ra[2], 1);
        }
    }
    c
}

/// `E` units: products and sums (a square is the product with itself, so one region fewer).
pub struct Arith {
    /// Slot operand ended at the unit: product, sum.
    ended: [Units; 2],
    /// Both operands forwarded, three more slots.
    forwarded: [Units; 2],
    /// Units by op (mul, add, square), slot operand ended / both forwarded.
    pub counts: [[usize; 2]; 3],
}

fn op_index(op: Op) -> usize {
    match op {
        Op::Mul => 0,
        Op::Add => 1,
        Op::Square => 2,
    }
}

impl Arith {
    pub fn new(b: &mut Builder) -> Self {
        let w = b.width();
        let names = ["mul", "add"];
        let ops = [Op::Mul, Op::Add];
        let ended = std::array::from_fn(|k| {
            let size = 6;
            let mut roles = forwards(w);
            for u in 0..w / size {
                let base = size * u;
                let (ra, rb) = ([base, base + 1, base + 2], [base + 3, base + 4, base + 5]);
                for (l, p) in op_polys(ops[k], ra, rb).into_iter().enumerate() {
                    roles[base + l] = Formula::Expr(p.build());
                }
            }
            Units::new(b.region(&format!("e-{}", names[k]), roles), size, w / size)
        });
        let forwarded = std::array::from_fn(|k| {
            let size = 9;
            let mut roles = forwards(w);
            for u in 0..w / size {
                let base = size * u;
                let (ra, rb) = ([base, base + 1, base + 2], [base + 3, base + 4, base + 5]);
                for (l, p) in op_polys(ops[k], ra, rb).into_iter().enumerate() {
                    roles[base + 6 + l] = Formula::Expr(p.build());
                }
            }
            Units::new(b.region(&format!("e-{}-fwd", names[k]), roles), size, w / size)
        });
        Self {
            ended,
            forwarded,
            counts: [[0; 2]; 3],
        }
    }

    /// `op(a, b)` (`b` ignored for a square, which is `a·a`). With `end_a`, `a`'s limbs end here (they must have no
    /// other slot); otherwise both operands are forwarded.
    pub fn op(&mut self, bld: &mut Builder, op: Op, a: Limbs, b: Limbs, end_a: bool) -> Limbs {
        self.counts[op_index(op)][!end_a as usize] += 1;
        let (k, b) = match op {
            Op::Mul => (0, b),
            Op::Square => (0, a),
            Op::Add => (1, b),
        };
        let (units, slots) = if end_a {
            (&mut self.ended[k], 0)
        } else {
            (&mut self.forwarded[k], 6)
        };
        let (row, base) = units.next(bld);
        for l in 0..3 {
            bld.place(row, base + l, a[l]);
            bld.place(row, base + 3 + l, b[l]);
        }
        std::array::from_fn(|l| bld.produce(row, base + slots + l))
    }
}

/// Ports: a row whose roles `0..L` forward the limbs and whose last role pushes `Σ γ^l limb_l` outside.
pub struct Ports {
    units: [Units; 2],
}

impl Ports {
    pub fn new(b: &mut Builder) -> Self {
        let w = b.width();
        let units = std::array::from_fn(|k| {
            let limbs = 3 + k;
            let mut roles = forwards(w);
            roles[w - 1] = Formula::Port((0..limbs as u8).collect());
            Units::new(b.region(&format!("port{limbs}"), roles), w, 1)
        });
        Self { units }
    }

    pub fn port(&mut self, b: &mut Builder, limbs: &[Value], source: Source) {
        assert_eq!(limbs.len(), source.limbs());
        let w = b.width();
        let (row, _) = self.units[limbs.len() - 3].next(b);
        for (l, &v) in limbs.iter().enumerate() {
            b.place(row, l, v);
        }
        b.port(row, w - 1, source);
    }
}
