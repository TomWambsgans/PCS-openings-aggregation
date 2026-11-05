// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! A combined claim's weight on its stack (the verifier's `weight_at`, term by term), kept as pieces on the stack's
//! blocks instead of written out over the stack, for the batching sumcheck's first rounds (`batch.rs`).
//!
//! A piece is `scale · f` on one aligned block of `2^v` words at `offset`, `f` one of:
//!
//! - [`Shape::Factored`]: `low[i mod 2^a] · eq(high, i >> a)`. A column read at one point `p` is `low = eq(p_(<a))`,
//!   `high = p_(≥a)`; `q_flock`'s slots read at one point are `low` the slots' coefficients, `high` the point.
//! - [`Shape::Dense`]: a table, for a column read at several points (the heap).
//! - [`Shape::Twisted`]: `Σ_k c_k eq(p, ·)^(2^k)`, Frobenius-twisted terms of one point (the ring switch's): on the
//!   cube `eq(φ^k(p), u) = eq(p, u)^(2^k)`, so `f` is one GF(2)-linear map of one eq table ([`Linear`]).
//!
//! The rounds bind the low variables first. After `j` rounds at `r`, a factored piece's `low` is folded `j` times
//! (`high` untouched while `low` lasts), a dense table likewise, and a twisted piece is the same map with
//! `c_k Π_(l<j) (1 + r_l + p_l^(2^k))` on `eq(p_(≥j), ·)`. A piece whose block is folded to one word is a scalar at
//! that word, times `r_l` or `1 + r_l` per later round (its offset's bit `l`). The stack is read as its `K`-words:
//! round `j` reads the folded stack `C_j(m) = Σ_y eq(r_(<j), y) C(2^j m + y)` from them, so nothing of the stack's
//! size but the stack is held. A factored piece's round is two inner products of `K`-words with `E`-tables per
//! `2^(a + j)` words ([`dot_base`]); a dense or twisted piece's is its pair's two weights (the twisted ones two maps
//! of one eq value, eight pairs at once by GFNI) times the pair's words, one mixed product a word, summed by the
//! word's offset in its `2^j`-word group and weighted by `eq(r_(<j), offset)` at the end.

use gf2_linear::Linear;
use leanvm_flock_gas::field::E;
use primitives::field::{F64, F192, F192Unreduced, Weights8, dot_base, mul_unreduced4, mul4};
use primitives::multilinear::eq_table;

use super::poly::from_v;
use crate::claims::{Column, Combined};
use crate::stacks::StackLayout;

/// The variables a factored piece's `low` covers: the rounds read from the stack's words must not outlast it.
pub const LOW_VARS: usize = 8;
/// `q_flock`'s slot bits: its word `j + 256 u` is slot `j` of instance `u`.
const SLOT_BITS: usize = 8;
/// Words per task of a round.
const TASK_WORDS: usize = 1 << 15;

/// An `E`-table to take inner products with `K`-words: packed for [`dot_base`] when its length is a multiple of 8.
enum Table {
    Packed(Vec<Weights8>),
    Plain(Vec<F192>),
}

impl Table {
    fn new(mut g: Vec<F192>) -> Self {
        if g.len() >= 8 && g.len().is_multiple_of(8) {
            Table::Packed(g.as_chunks::<8>().0.iter().map(Weights8::new).collect())
        } else {
            g.shrink_to_fit();
            Table::Plain(g)
        }
    }

    /// `g`, its zero tail cut (to a multiple of 8 when it is that long).
    fn trimmed(mut g: Vec<F192>, others: &[&[F192]]) -> Self {
        let used = std::iter::once(&g[..])
            .chain(others.iter().copied())
            .map(|t| t.iter().rposition(|x| !x.is_zero()).map_or(0, |i| i + 1))
            .max()
            .unwrap_or(0);
        let keep = if g.len() >= 8 { used.div_ceil(8) * 8 } else { g.len() };
        g.truncate(keep.max(if g.len() >= 8 { 8 } else { 0 }));
        Self::new(g)
    }

    fn len(&self) -> usize {
        match self {
            Table::Packed(w) => 8 * w.len(),
            Table::Plain(g) => g.len(),
        }
    }

    /// `Σ_i g_i words_i` over the table's length (`words` at least that long).
    #[inline]
    fn dot(&self, words: &[F64]) -> F192Unreduced {
        match self {
            Table::Packed(w) => dot_base(w, &words[..8 * w.len()]),
            Table::Plain(g) => g
                .iter()
                .zip(words)
                .fold(F192Unreduced::ZERO, |acc, (g, &k)| acc ^ g.mul_base_unreduced(k)),
        }
    }

    /// The same, with the words past the stack's end zero.
    fn dot_clipped(&self, words: &[F64], start: usize) -> F192 {
        let n = self.len();
        if start + n <= words.len() {
            self.dot(&words[start..]).reduce()
        } else if start >= words.len() {
            F192::ZERO
        } else {
            let mut padded = words[start..].to_vec();
            padded.resize(n, F64::ZERO);
            self.dot(&padded).reduce()
        }
    }
}

#[derive(Clone)]
enum Shape {
    /// `low[i mod 2^a] · h[i >> a]`, `h = eq(high, ·)`.
    Factored { low: Vec<F192>, h: Vec<F192> },
    /// A table, and the buffer it folds into.
    Dense { table: Vec<F192>, spare: Vec<F192> },
    /// `Σ_k c_k eq(point_(≥bound), ·)^(2^k)`.
    Twisted {
        c: Vec<F192>,
        point: Vec<F192>,
        bound: usize,
    },
}

impl Shape {
    /// The shape's words left (after the rounds so far).
    fn len(&self) -> usize {
        match self {
            Shape::Factored { low, h } => low.len() * h.len(),
            Shape::Dense { table, .. } => table.len(),
            Shape::Twisted { point, bound, .. } => 1 << (point.len() - bound),
        }
    }

    /// Folded to one word: its value.
    fn scalar(&self) -> F192 {
        assert_eq!(self.len(), 1);
        match self {
            Shape::Factored { low, h } => low[0] * h[0],
            Shape::Dense { table, .. } => table[0],
            Shape::Twisted { c, .. } => c.iter().fold(F192::ZERO, |acc, &x| acc + x),
        }
    }
}

#[derive(Clone)]
struct Piece {
    offset: usize,
    vars: usize,
    scale: F192,
    shape: usize,
}

/// One round's tables of a shape.
enum Prep {
    /// The inner products' tables over `2^(a + j)` words: `ga` takes `low[2l] e(y)` on the pair's low half (0 on
    /// the other), `gb` takes `(low[2l] + low[2l + 1]) e(y)` on both.
    Factored {
        ga: Table,
        gb: Table,
        span: usize,
    },
    Dense,
    /// `eq(point_(>j), i)` as `lo[i mod 2^bits] hi[i >> bits]`; the map's pair `(W(2i), W(2i) + W(2i + 1))` of it.
    Twisted {
        lo: Vec<F192>,
        hi: Vec<F192>,
        bits: usize,
        map: Linear<2>,
    },
    Scalar(F192),
}

/// `eq(point, ·)` as two tables, `lo[i mod 2^bits] hi[i >> bits]`.
fn split_eq(point: &[F192]) -> (Vec<F192>, Vec<F192>, usize) {
    let bits = point.len().min(10);
    (eq_table(&point[..bits]), eq_table(&point[bits..]), bits)
}

/// A twisted shape's weight on its words left, `L(eq(point_(≥bound), ·))`: its map and eq table's two halves.
struct TwistedMap {
    map: Linear<1>,
    lo: Vec<F192>,
    hi: Vec<F192>,
    bits: usize,
}

impl TwistedMap {
    /// The weight at the eight words from `first` (past `end`, zero's image).
    #[inline]
    fn at8(&self, first: usize, end: usize) -> [F192; 8] {
        let [w] = self.map.at8(&eq8(&self.lo, &self.hi, self.bits, first, end));
        w
    }
}

/// `lo[i mod 2^bits] hi[i >> bits]` for the eight indices from `first` (past `end`, zero).
#[inline]
fn eq8(lo: &[F192], hi: &[F192], bits: usize, first: usize, end: usize) -> [F192; 8] {
    let mask = (1 << bits) - 1;
    let at = |k: usize| {
        let i = first + k;
        if i < end {
            (lo[i & mask], hi[i >> bits])
        } else {
            (F192::ZERO, F192::ZERO)
        }
    };
    let pairs: [(F192, F192); 8] = std::array::from_fn(at);
    let low = mul4(std::array::from_fn(|k| pairs[k].0), std::array::from_fn(|k| pairs[k].1));
    let high = mul4(
        std::array::from_fn(|k| pairs[4 + k].0),
        std::array::from_fn(|k| pairs[4 + k].1),
    );
    std::array::from_fn(|k| if k < 4 { low[k] } else { high[k - 4] })
}

/// A round's two sums from their parts by offset (`at[y]` and `at[2^j + y]`): `Σ_y e(y) at[y]`, each half.
fn by_offset(at: &[F192Unreduced], e: &[F192]) -> (F192, F192) {
    let (low, high) = at.split_at(e.len());
    let sum = |part: &[F192Unreduced]| {
        part.iter()
            .zip(e)
            .fold(F192Unreduced::ZERO, |acc, (x, &ey)| acc ^ ey.mul_unreduced(x.reduce()))
            .reduce()
    };
    (sum(low), sum(high))
}

/// `len` zeros, a large table written (and its pages mapped) in parallel.
pub fn zeros(len: usize) -> Vec<F192> {
    if len < 1 << 16 {
        vec![F192::ZERO; len]
    } else {
        parallel::map_collect(len, |_| F192::ZERO)
    }
}

/// Fold a table's pairs at `r`: `t[2i] + r (t[2i] + t[2i + 1])`.
pub fn fold(v: &[F192], r: F192) -> Vec<F192> {
    let half = v.len().div_ceil(2);
    let pair = |i: usize| {
        let (a, b) = (v[2 * i], v.get(2 * i + 1).copied().unwrap_or(F192::ZERO));
        a + r * (a + b)
    };
    if half < 1 << 12 {
        (0..half).map(pair).collect()
    } else {
        parallel::map_collect(half, pair)
    }
}

/// A combined claim's weight on its stack, by pieces, through the rounds that read the stack's words.
#[derive(Clone)]
pub struct Weight {
    pieces: Vec<Piece>,
    shapes: Vec<Shape>,
    round: usize,
}

impl Weight {
    /// The weight of `claim` on the stack `layout` places.
    pub fn new(claim: &Combined<E>, layout: &StackLayout) -> Self {
        let basis = [F192::ONE, F192::new(0, 1, 0), F192::new(0, 0, 1)];
        let points: Vec<Vec<F192>> = claim
            .points
            .iter()
            .map(|p| p.iter().map(|&x| from_v(x)).collect())
            .collect();
        // Per column: its terms by point, untwisted (point, coefficient), twisted (point, [(twist, coefficient)]), and
        // q_flock's slots (point, the slots' coefficients).
        #[derive(Default)]
        struct Terms {
            plain: Vec<(usize, F192)>,
            twisted: Vec<(usize, Vec<(u8, F192)>)>,
            slots: Vec<(usize, Vec<F192>)>,
            /// The coefficient of the column's sum (`verifier::SUM_TWIST`: the weight 1 on every word).
            sum: Option<F192>,
        }
        let mut columns: Vec<(Column, Terms)> = Vec::new();
        for &(column, p, twist, coefficient) in &claim.terms {
            let coefficient = from_v(coefficient);
            let (target, slot) = match column {
                Column::QflockSlot(j) => (Column::Qflock, Some(j)),
                other => (other, None),
            };
            let at = match columns.iter().position(|(c, _)| *c == target) {
                Some(at) => at,
                None => {
                    columns.push((target, Terms::default()));
                    columns.len() - 1
                }
            };
            let terms = &mut columns[at].1;
            if twist == crate::verifier::SUM_TWIST {
                assert!(slot.is_none(), "no slot sums");
                *terms.sum.get_or_insert(F192::ZERO) += coefficient;
                continue;
            }
            match slot {
                Some(j) => {
                    assert_eq!(twist, 0, "no twisted slot terms");
                    let slots = match terms.slots.iter().position(|(q, _)| *q == p) {
                        Some(i) => &mut terms.slots[i].1,
                        None => {
                            terms.slots.push((p, vec![F192::ZERO; 1 << SLOT_BITS]));
                            &mut terms.slots.last_mut().unwrap().1
                        }
                    };
                    slots[j] += coefficient;
                }
                None => match terms.twisted.iter().position(|(q, _)| *q == p) {
                    Some(i) => terms.twisted[i].1.push((twist, coefficient)),
                    None => terms.twisted.push((p, vec![(twist, coefficient)])),
                },
            }
        }
        // A point's terms all untwisted are one plain term.
        for (_, terms) in &mut columns {
            let mut twisted = Vec::new();
            for (p, list) in std::mem::take(&mut terms.twisted) {
                if list.iter().all(|&(k, _)| k == 0) {
                    terms
                        .plain
                        .push((p, list.iter().fold(F192::ZERO, |acc, &(_, c)| acc + c)));
                } else {
                    twisted.push((p, list));
                }
            }
            terms.twisted = twisted;
        }
        let mut weight = Weight {
            pieces: Vec::new(),
            shapes: Vec::new(),
            round: 0,
        };
        // Factored shapes of one point, by (point, variables).
        let mut factored: Vec<((usize, usize), usize)> = Vec::new();
        for (column, terms) in &columns {
            let limbs = layout.limbs(*column);
            let vars = limbs[0].1;
            let add = |weight: &mut Weight, shape: usize, scale: F192| {
                for &(limb, v, offset) in &limbs {
                    assert_eq!(v, vars, "a column's limbs are blocks of one size");
                    weight.pieces.push(Piece {
                        offset: offset as usize,
                        vars,
                        scale: scale * basis[limb],
                        shape,
                    });
                }
            };
            match terms.plain[..] {
                [] => {}
                [(p, coefficient)] => {
                    let shape = match factored.iter().find(|(key, _)| *key == (p, vars)) {
                        Some(&(_, shape)) => shape,
                        None => {
                            let point = &points[p][..vars];
                            let a = vars.min(LOW_VARS);
                            weight.shapes.push(Shape::Factored {
                                low: eq_table(&point[..a]),
                                h: eq_table(&point[a..]),
                            });
                            factored.push(((p, vars), weight.shapes.len() - 1));
                            weight.shapes.len() - 1
                        }
                    };
                    add(&mut weight, shape, coefficient);
                }
                ref several => {
                    weight.shapes.push(Shape::Dense {
                        table: several_points(several, &points, vars),
                        spare: Vec::new(),
                    });
                    let shape = weight.shapes.len() - 1;
                    add(&mut weight, shape, F192::ONE);
                }
            }
            for &(p, ref list) in &terms.twisted {
                let top = list.iter().map(|&(k, _)| k as usize).max().unwrap_or(0);
                let mut c = vec![F192::ZERO; top + 1];
                for &(k, coefficient) in list {
                    c[k as usize] += coefficient;
                }
                weight.shapes.push(Shape::Twisted {
                    c,
                    point: points[p][..vars].to_vec(),
                    bound: 0,
                });
                let shape = weight.shapes.len() - 1;
                add(&mut weight, shape, F192::ONE);
            }
            if let Some(coefficient) = terms.sum {
                // The weight 1 on every word: a factored shape of ones.
                let a = vars.min(LOW_VARS);
                weight.shapes.push(Shape::Factored {
                    low: vec![F192::ONE; 1 << a],
                    h: vec![F192::ONE; 1 << (vars - a)],
                });
                let shape = weight.shapes.len() - 1;
                add(&mut weight, shape, coefficient);
            }
            for (p, slots) in &terms.slots {
                weight.shapes.push(Shape::Factored {
                    low: slots.clone(),
                    h: eq_table(&points[*p][..vars - SLOT_BITS]),
                });
                let shape = weight.shapes.len() - 1;
                add(&mut weight, shape, F192::ONE);
            }
        }
        weight
    }

    /// `Σ_u W(u) C(u)` over the stack's words, before any round.
    pub fn sum(&self, words: &[F64]) -> F192 {
        assert_eq!(self.round, 0);
        let lows: Vec<Option<Table>> = self
            .shapes
            .iter()
            .map(|shape| match shape {
                Shape::Factored { low, .. } => Some(Table::new(low.clone())),
                _ => None,
            })
            .collect();
        let maps = self.twisted_maps();
        let tasks = self.tasks(|piece| match &self.shapes[piece.shape] {
            Shape::Factored { low, h } => (h.len(), (TASK_WORDS / low.len()).max(1)),
            _ => (1 << piece.vars, TASK_WORDS),
        });
        parallel::map_reduce(
            tasks.len(),
            || F192::ZERO,
            |t| {
                let (index, start, end) = tasks[t];
                let piece = &self.pieces[index];
                let mut acc = F192Unreduced::ZERO;
                match (&self.shapes[piece.shape], &lows[piece.shape], &maps[piece.shape]) {
                    (Shape::Factored { low, h }, Some(g), _) => {
                        for u in start..end {
                            let at = piece.offset + u * low.len();
                            acc ^= h[u].mul_unreduced(g.dot(&words[at..]).reduce());
                        }
                    }
                    (Shape::Dense { table, .. }, ..) => {
                        for i in start..end {
                            acc ^= table[i].mul_base_unreduced(words[piece.offset + i]);
                        }
                    }
                    (Shape::Twisted { .. }, _, Some(map)) => {
                        for first in (start..end).step_by(8) {
                            let w = map.at8(first, end);
                            for (k, w) in w.iter().enumerate().take(end - first) {
                                acc ^= w.mul_base_unreduced(words[piece.offset + first + k]);
                            }
                        }
                    }
                    _ => unreachable!(),
                }
                piece.scale * acc.reduce()
            },
            |a, b| a + b,
        )
    }

    /// The twisted shapes' weights on their words left, by shape.
    fn twisted_maps(&self) -> Vec<Option<TwistedMap>> {
        self.shapes
            .iter()
            .map(|shape| match shape {
                Shape::Twisted { c, point, bound } if shape.len() > 1 => {
                    let (lo, hi, bits) = split_eq(&point[*bound..]);
                    Some(TwistedMap {
                        map: Linear::new([&c[..]]),
                        lo,
                        hi,
                        bits,
                    })
                }
                _ => None,
            })
            .collect()
    }

    /// Every piece's units split into tasks: `units(piece)` is (its units, units per task).
    fn tasks(&self, units: impl Fn(&Piece) -> (usize, usize)) -> Vec<(usize, usize, usize)> {
        let mut tasks = Vec::new();
        for (index, piece) in self.pieces.iter().enumerate() {
            let (count, per) = units(piece);
            tasks.extend(
                (0..count)
                    .step_by(per)
                    .map(|start| (index, start, (start + per).min(count))),
            );
        }
        tasks
    }

    /// The next round's sums over the stack's `words`, `(Σ W_0 C_0, Σ (W_0 + W_1)(C_0 + C_1))` over the pairs of
    /// the stack folded so far, `e = eq(r_(<j), ·)` at the rounds' challenges so far.
    pub fn round(&self, words: &[F64], e: &[F192]) -> (F192, F192) {
        let j = self.round;
        assert_eq!(e.len(), 1 << j);
        let folded = Table::new(e.to_vec());
        let preps: Vec<Prep> = self
            .shapes
            .iter()
            .map(|shape| {
                if shape.len() == 1 {
                    return Prep::Scalar(shape.scalar());
                }
                match shape {
                    Shape::Factored { low, .. } => {
                        assert!(low.len() >= 2, "a factored piece's rounds outlast its low table");
                        let span = low.len() << j;
                        let (mut ga, mut gb) = (vec![F192::ZERO; span], vec![F192::ZERO; span]);
                        for l in 0..low.len() / 2 {
                            let (w0, dw) = (low[2 * l], low[2 * l] + low[2 * l + 1]);
                            for (y, &ey) in e.iter().enumerate() {
                                ga[y + ((2 * l) << j)] = w0 * ey;
                                gb[y + ((2 * l) << j)] = dw * ey;
                                gb[y + ((2 * l + 1) << j)] = dw * ey;
                            }
                        }
                        let gb = Table::trimmed(gb, &[&ga]);
                        ga.truncate(gb.len());
                        Prep::Factored {
                            ga: Table::new(ga),
                            gb,
                            span,
                        }
                    }
                    Shape::Dense { .. } => Prep::Dense,
                    Shape::Twisted { c, point, bound } => {
                        let p = point[*bound];
                        // W(2i) = L((1 + p) e'_i), W(2i) + W(2i + 1) = L(e'_i), e' = eq(point_(>j), ·).
                        let mut power = F192::ONE + p;
                        let a: Vec<F192> = c
                            .iter()
                            .map(|&ck| {
                                let x = ck * power;
                                power = power.square();
                                x
                            })
                            .collect();
                        let (lo, hi, bits) = split_eq(&point[bound + 1..]);
                        Prep::Twisted {
                            lo,
                            hi,
                            bits,
                            map: Linear::new([&a, c]),
                        }
                    }
                }
            })
            .collect();
        // A dense shape's pieces (a column's limbs) share its table: one task reads it for all of them.
        let mut of_shape: Vec<Vec<&Piece>> = vec![Vec::new(); self.shapes.len()];
        for piece in &self.pieces {
            of_shape[piece.shape].push(piece);
        }
        let tasks = self.tasks(|piece| match &preps[piece.shape] {
            Prep::Factored { span, .. } => (self.shape_units(piece.shape, *span), (TASK_WORDS / span).max(1)),
            Prep::Dense if !std::ptr::eq(of_shape[piece.shape][0], piece) => (0, 1),
            Prep::Dense | Prep::Twisted { .. } => (1 << (piece.vars - j - 1), (TASK_WORDS >> (j + 1)).max(1)),
            Prep::Scalar(_) => (1, 1),
        });
        // A pair's weights `(W(2i), W(2i) + W(2i + 1))` against the folded stack's pair, by the offset `y` in its
        // `2^j` words: `Σ_i W_0(i) C_j(2i) = Σ_y e(y) Σ_i W_0(i) C(2^(j+1) i + y)`, one mixed product a word.
        let span = 1usize << j;
        let pairs = |at: &mut [F192Unreduced], piece: &Piece, i: usize, w0: F192, dw: F192| {
            let base = piece.offset + ((2 * i) << j);
            let (low, high) = words[base..base + 2 * span].split_at(span);
            for (y, (&c0, &c1)) in low.iter().zip(high).enumerate() {
                at[y] ^= w0.mul_base_unreduced(c0);
                at[span + y] ^= dw.mul_base_unreduced(c0 + c1);
            }
        };
        let (a, b) = parallel::map_reduce(
            tasks.len(),
            || (F192::ZERO, F192::ZERO),
            |t| {
                let (index, start, end) = tasks[t];
                let piece = &self.pieces[index];
                let (a, b) = match (&preps[piece.shape], &self.shapes[piece.shape]) {
                    (Prep::Factored { ga, gb, span }, Shape::Factored { h, .. }) => {
                        let (mut a, mut b) = (F192Unreduced::ZERO, F192Unreduced::ZERO);
                        for u in start..end {
                            let at = &words[piece.offset + u * span..];
                            a ^= h[u].mul_unreduced(ga.dot(at).reduce());
                            b ^= h[u].mul_unreduced(gb.dot(at).reduce());
                        }
                        (a.reduce(), b.reduce())
                    }
                    (Prep::Dense, Shape::Dense { table, .. }) => {
                        let limbs = &of_shape[piece.shape];
                        let mut at = vec![F192Unreduced::ZERO; 2 * span * limbs.len()];
                        for i in start..end {
                            let (w0, dw) = (table[2 * i], table[2 * i] + table[2 * i + 1]);
                            for (at, limb) in at.chunks_mut(2 * span).zip(limbs) {
                                pairs(at, limb, i, w0, dw);
                            }
                        }
                        let (mut a, mut b) = (F192::ZERO, F192::ZERO);
                        for (at, limb) in at.chunks(2 * span).zip(limbs) {
                            let (x, y) = by_offset(at, e);
                            a += limb.scale * x;
                            b += limb.scale * y;
                        }
                        return (a, b);
                    }
                    (Prep::Twisted { lo, hi, bits, map }, _) => {
                        let mut at = vec![F192Unreduced::ZERO; 2 * span];
                        for first in (start..end).step_by(8) {
                            let [w0, dw] = map.at8(&eq8(lo, hi, *bits, first, end));
                            for k in 0..(end - first).min(8) {
                                pairs(&mut at, piece, first + k, w0[k], dw[k]);
                            }
                        }
                        by_offset(&at, e)
                    }
                    (Prep::Scalar(value), _) => {
                        // The block is one word of the folded stack, at its offset's position.
                        let position = piece.offset >> j;
                        let (own, other) = (
                            folded.dot_clipped(words, position << j),
                            folded.dot_clipped(words, (position ^ 1) << j),
                        );
                        let s = piece.scale * *value;
                        let a = if position & 1 == 0 { s * own } else { F192::ZERO };
                        return (a, s * (own + other));
                    }
                    _ => unreachable!(),
                };
                (piece.scale * a, piece.scale * b)
            },
            |x, y| (x.0 + y.0, x.1 + y.1),
        );
        (a, b)
    }

    /// A pair round's sums in one read of the words (π1-rec3's paired batch, `batch::prove_pairs`): at round `j`
    /// (variables `j` and `j + 1`), `[plain, at 0, at 1, at β]`: `plain` is [`Weight::round`]'s, and `at x` is
    /// [`Weight::round`]'s on the weight folded at `x` with `e ⊗ (1 + x, x)`, the next variable's sums with this
    /// one bound to `x`. With the folded weight `W` and stack `C` in groups of four (`W_ab` at `4 g + a + 2 b`), eight
    /// sums are taken: `P_0 = Σ W_00 C_00`, `P_1 = Σ W_01 C_01`, `P_2 = Σ W_10 C_10`, `P_3 = Σ (W_00 + W_10)(C_00 +
    /// C_10)`, `P_4 = Σ (W_01 + W_11)(C_01 + C_11)`, `P_5 = Σ (W_00 + W_01)(C_00 + C_01)`, `P_6 = Σ (W_10 + W_11)(C_10 +
    /// C_11)`, `P_7 = Σ (Σ_ab W_ab)(Σ_ab C_ab)`; the sums at `β` (`X_βb = (1 + β) X_0b + β X_1b`) follow from them:
    /// `Σ W_β0 C_β0 = (1 + β)² P_0 + β (1 + β)(P_0 + P_2 + P_3) + β² P_2`, and likewise `Σ (W_β0 + W_β1)(C_β0 + C_β1)`
    /// from `P_5`, `P_6`, `P_7`. `None` if a block is two words or a factored piece's `low` below four (the caller then
    /// folds clones).
    pub fn round_pair(&self, words: &[F64], e: &[F192], beta: F192) -> Option<[(F192, F192); 4]> {
        let j = self.round;
        assert_eq!(e.len(), 1 << j);
        for shape in &self.shapes {
            let len = shape.len();
            if len == 2 || len == 3 {
                return None;
            }
            if let Shape::Factored { low, .. } = shape {
                if len > 1 && low.len() < 4 {
                    return None;
                }
            }
        }
        const SUMS: usize = 8;
        type Sums = [F192; SUMS];
        let folded = Table::new(e.to_vec());
        let span = 1usize << j;
        // The eight products of a group, from its four weights and four stack values.
        let eight = |w: [F192; 4], c: [F192; 4]| -> Sums {
            let [w00, w10, w01, w11] = w;
            let [c00, c10, c01, c11] = c;
            [
                w00 * c00,
                w01 * c01,
                w10 * c10,
                (w00 + w10) * (c00 + c10),
                (w01 + w11) * (c01 + c11),
                (w00 + w01) * (c00 + c01),
                (w10 + w11) * (c10 + c11),
                (w00 + w10 + w01 + w11) * (c00 + c10 + c01 + c11),
            ]
        };
        // Per shape: a factored piece's coefficient of the word at `(l << j) + y` of a unit in each sum (times
        // `e(y)`), cut after the last nonzero one.
        enum Prep2 {
            Factored { coefficients: Vec<Sums>, span: usize },
            Dense,
            Twisted { lo: Vec<F192>, hi: Vec<F192>, bits: usize, map: Linear<2> },
            Scalar(F192),
        }
        let preps: Vec<Prep2> = self
            .shapes
            .iter()
            .map(|shape| {
                if shape.len() == 1 {
                    return Prep2::Scalar(shape.scalar());
                }
                match shape {
                    Shape::Factored { low, .. } => {
                        let unit = low.len() << j;
                        let mut t: Vec<Sums> = vec![[F192::ZERO; SUMS]; unit];
                        for q in 0..low.len() / 4 {
                            let [l0, l1, l2, l3] = std::array::from_fn(|k| low[4 * q + k]);
                            let all = l0 + l1 + l2 + l3;
                            // (sum, position k in the group, coefficient)
                            let entries: [(usize, usize, F192); 15] = [
                                (0, 0, l0),
                                (1, 2, l2),
                                (2, 1, l1),
                                (3, 0, l0 + l1),
                                (3, 1, l0 + l1),
                                (4, 2, l2 + l3),
                                (4, 3, l2 + l3),
                                (5, 0, l0 + l2),
                                (5, 2, l0 + l2),
                                (6, 1, l1 + l3),
                                (6, 3, l1 + l3),
                                (7, 0, all),
                                (7, 1, all),
                                (7, 2, all),
                                (7, 3, all),
                            ];
                            for &(sum, k, coefficient) in &entries {
                                let base = (4 * q + k) << j;
                                for (y, &ey) in e.iter().enumerate() {
                                    t[base + y][sum] = coefficient * ey;
                                }
                            }
                        }
                        let used = t.iter().rposition(|c| c.iter().any(|x| !x.is_zero())).map_or(0, |i| i + 1);
                        t.truncate(used);
                        Prep2::Factored {
                            coefficients: t,
                            span: unit,
                        }
                    }
                    Shape::Dense { .. } => Prep2::Dense,
                    Shape::Twisted { c, point, bound } => {
                        let p = point[*bound];
                        let mut power = F192::ONE + p;
                        let a: Vec<F192> = c
                            .iter()
                            .map(|&ck| {
                                let x = ck * power;
                                power = power.square();
                                x
                            })
                            .collect();
                        let (lo, hi, bits) = split_eq(&point[bound + 1..]);
                        Prep2::Twisted {
                            lo,
                            hi,
                            bits,
                            map: Linear::new([&a, c]),
                        }
                    }
                }
            })
            .collect();
        let mut of_shape: Vec<Vec<&Piece>> = vec![Vec::new(); self.shapes.len()];
        for piece in &self.pieces {
            of_shape[piece.shape].push(piece);
        }
        let tasks = self.tasks(|piece| match &preps[piece.shape] {
            Prep2::Factored { span, .. } => (self.shape_units(piece.shape, *span), (4 * TASK_WORDS / span).max(1)),
            Prep2::Dense if !std::ptr::eq(of_shape[piece.shape][0], piece) => (0, 1),
            Prep2::Dense => (1 << (piece.vars - j - 2), (TASK_WORDS >> (j + 2)).max(1)),
            Prep2::Twisted { .. } => (1 << (piece.vars - j - 1), (TASK_WORDS >> (j + 1)).max(8)),
            Prep2::Scalar(_) => (1, 1),
        });
        // A group's four weights against the stack's words, by the offset `y` in their `2^j`-word runs: the eight
        // sums' accumulators `at[y]`, one mixed product a sum a word.
        let group = |at: &mut [[F192Unreduced; SUMS]], piece: &Piece, g: usize, w: [F192; 4]| {
            let [w00, w10, w01, w11] = w;
            let (d0, d1, e0, e1) = (w00 + w10, w01 + w11, w00 + w01, w10 + w11);
            let all = d0 + d1;
            let base = piece.offset + ((4 * g) << j);
            let run = &words[base..base + 4 * span];
            let (r0, rest) = run.split_at(span);
            let (r1, rest) = rest.split_at(span);
            let (r2, r3) = rest.split_at(span);
            for (y, a) in at.iter_mut().enumerate().take(span) {
                let (c00, c10, c01, c11) = (r0[y], r1[y], r2[y], r3[y]);
                let (s0, s1, t0, t1) = (c00 + c10, c01 + c11, c00 + c01, c10 + c11);
                a[0] ^= w00.mul_base_unreduced(c00);
                a[1] ^= w01.mul_base_unreduced(c01);
                a[2] ^= w10.mul_base_unreduced(c10);
                a[3] ^= d0.mul_base_unreduced(s0);
                a[4] ^= d1.mul_base_unreduced(s1);
                a[5] ^= e0.mul_base_unreduced(t0);
                a[6] ^= e1.mul_base_unreduced(t1);
                a[7] ^= all.mul_base_unreduced(s0 + s1);
            }
        };
        let weigh = |at: &[[F192Unreduced; SUMS]]| -> Sums {
            let mut out = [F192Unreduced::ZERO; SUMS];
            for (a, &ey) in at.iter().zip(e) {
                for s in 0..SUMS {
                    out[s] ^= ey.mul_unreduced(a[s].reduce());
                }
            }
            out.map(|x| x.reduce())
        };
        let add = |x: Sums, y: Sums| -> Sums { std::array::from_fn(|s| x[s] + y[s]) };
        let body = |t: usize| -> Sums {
            let (index, start, end) = tasks[t];
            let piece = &self.pieces[index];
            match (&preps[piece.shape], &self.shapes[piece.shape]) {
                (Prep2::Factored { coefficients, span }, Shape::Factored { h, .. }) => {
                    // `Σ_u h[u] word(u span + i)` first (one mixed product a word), then the sums of it.
                    let keep = coefficients.len();
                    let mut folded_h = vec![F192Unreduced::ZERO; keep];
                    for u in start..end {
                        let at = piece.offset + u * span;
                        if at >= words.len() {
                            break;
                        }
                        let (hu, avail) = (h[u], (words.len() - at).min(keep));
                        for (acc, &k) in folded_h[..avail].iter_mut().zip(&words[at..at + avail]) {
                            *acc ^= hu.mul_base_unreduced(k);
                        }
                    }
                    let mut acc = [F192Unreduced::ZERO; SUMS];
                    for (c, x) in coefficients.iter().zip(&folded_h) {
                        let x = x.reduce();
                        for s in 0..SUMS {
                            if !c[s].is_zero() {
                                acc[s] ^= c[s].mul_unreduced(x);
                            }
                        }
                    }
                    acc.map(|x| piece.scale * x.reduce())
                }
                (Prep2::Dense, Shape::Dense { table, .. }) => {
                    let limbs = &of_shape[piece.shape];
                    let mut out = [F192::ZERO; SUMS];
                    let mut at = vec![[F192Unreduced::ZERO; SUMS]; span];
                    for limb in limbs {
                        at.fill([F192Unreduced::ZERO; SUMS]);
                        for g in start..end {
                            let w: [F192; 4] = std::array::from_fn(|k| table[4 * g + k]);
                            group(&mut at, limb, g, w);
                        }
                        out = add(out, weigh(&at).map(|x| limb.scale * x));
                    }
                    out
                }
                (Prep2::Twisted { lo, hi, bits, map }, _) => {
                    let mut at = vec![[F192Unreduced::ZERO; SUMS]; span];
                    for first in (start..end).step_by(8) {
                        let [w0, dw] = map.at8(&eq8(lo, hi, *bits, first, end));
                        for k in (0..(end - first).min(8)).step_by(2) {
                            let w = [w0[k], w0[k] + dw[k], w0[k + 1], w0[k + 1] + dw[k + 1]];
                            group(&mut at, piece, (first + k) / 2, w);
                        }
                    }
                    weigh(&at).map(|x| piece.scale * x)
                }
                (Prep2::Scalar(value), _) => {
                    // The block is one word of the folded stack, at its offset's position in its group.
                    let position = piece.offset >> j;
                    let g = position >> 2;
                    let c: [F192; 4] = std::array::from_fn(|k| folded.dot_clipped(words, ((4 * g) + k) << j));
                    let s = piece.scale * *value;
                    let w: [F192; 4] = std::array::from_fn(|k| if k == position & 3 { s } else { F192::ZERO });
                    eight(w, c)
                }
                _ => unreachable!(),
            }
        };
        let p = parallel::map_reduce(tasks.len(), || [F192::ZERO; SUMS], body, add);
        if std::env::var("PI1_PROFILE").is_ok() {
            let kind = |t: usize| match preps[self.pieces[tasks[t].0].shape] {
                Prep2::Factored { .. } => 0,
                Prep2::Dense => 1,
                Prep2::Twisted { .. } => 2,
                Prep2::Scalar(_) => 3,
            };
            for k in 0..4 {
                let mine: Vec<usize> = (0..tasks.len()).filter(|&t| kind(t) == k).collect();
                let units: usize = mine.iter().map(|&t| tasks[t].2 - tasks[t].1).sum();
                let clock = std::time::Instant::now();
                parallel::map_reduce(mine.len(), || [F192::ZERO; SUMS], |i| body(mine[i]), add);
                eprintln!(
                    "      round_pair j{j} kind {k}: {} tasks, {units} units, {:.4} s",
                    mine.len(),
                    clock.elapsed().as_secs_f64()
                );
            }
        }
        // `Σ X_β0 Y_β0` from `Σ X_0 Y_0`, `Σ X_1 Y_1` and `Σ (X_0 + X_1)(Y_0 + Y_1)`, `X_βb = (1 + β) X_0 + β X_1`.
        let one_beta = F192::ONE + beta;
        let (aa, ab, bb) = (one_beta * one_beta, beta * one_beta, beta * beta);
        let at_beta = |p00: F192, p11: F192, both: F192| aa * p00 + ab * (both + p00 + p11) + bb * p11;
        Some([
            (p[0] + p[1], p[3] + p[4]),
            (p[0], p[5]),
            (p[2], p[6]),
            (at_beta(p[0], p[2], p[3]), at_beta(p[5], p[6], p[7])),
        ])
    }

    /// A factored shape's units (entries of `h`) in a round of `span` words per unit.
    fn shape_units(&self, shape: usize, span: usize) -> usize {
        match &self.shapes[shape] {
            Shape::Factored { h, low } => {
                debug_assert_eq!(span % low.len(), 0);
                h.len()
            }
            _ => unreachable!(),
        }
    }

    /// Bind the round's variable to `r`.
    pub fn fold(&mut self, r: F192) {
        let j = self.round;
        for piece in &mut self.pieces {
            if piece.vars <= j {
                piece.scale *= if piece.offset >> j & 1 == 1 { r } else { F192::ONE + r };
            }
        }
        for shape in &mut self.shapes {
            if shape.len() == 1 {
                continue;
            }
            match shape {
                Shape::Factored { low, .. } => *low = fold(low, r),
                Shape::Dense { table, spare } => {
                    // Into the spare buffer, which the table's old words become.
                    let half = table.len() / 2;
                    if spare.len() < half {
                        *spare = zeros(half);
                    }
                    spare.truncate(half);
                    let t = &table[..];
                    parallel::chunks_mut(spare, 1 << 12, |k, out| {
                        for (i, o) in out.iter_mut().enumerate() {
                            let g = 2 * ((k << 12) + i);
                            *o = t[g] + r * (t[g] + t[g + 1]);
                        }
                    });
                    std::mem::swap(table, spare);
                }
                Shape::Twisted { c, point, bound } => {
                    let mut power = point[*bound];
                    for ck in c.iter_mut() {
                        *ck *= F192::ONE + r + power;
                        power = power.square();
                    }
                    *bound += 1;
                }
            }
        }
        self.round += 1;
    }

    /// The weight folded so far, written out over the folded stack's `len` words.
    pub fn dense(&self, len: usize) -> Vec<F192> {
        const CHUNK: usize = 1 << 12;
        let j = self.round;
        let mut out = zeros(len);
        // The blocks not yet folded to one word, in order, each with its pieces: written chunk by chunk, one pass.
        let mut blocks: Vec<(usize, usize, Vec<&Piece>)> = Vec::new();
        for piece in &self.pieces {
            let size = self.shapes[piece.shape].len();
            if size > 1 {
                let start = piece.offset >> j;
                match blocks.iter_mut().find(|(s, ..)| *s == start) {
                    Some((_, _, pieces)) => pieces.push(piece),
                    None => blocks.push((start, size, vec![piece])),
                }
            }
        }
        blocks.sort_by_key(|&(start, ..)| start);
        let maps = self.twisted_maps();
        let mut tasks: Vec<(&mut [F192], usize, usize)> = Vec::new();
        let (mut rest, mut cursor) = (&mut out[..], 0);
        for (b, &(start, size, _)) in blocks.iter().enumerate() {
            assert!(start >= cursor, "the blocks are disjoint");
            let (block, tail) = std::mem::take(&mut rest)[start - cursor..].split_at_mut(size);
            (rest, cursor) = (tail, start + size);
            tasks.extend(
                block
                    .chunks_mut(CHUNK)
                    .enumerate()
                    .map(|(k, chunk)| (chunk, b, k * CHUNK)),
            );
        }
        parallel::for_each_mut(&mut tasks, |_, (chunk, b, first)| {
            let first = *first;
            for piece in &blocks[*b].2 {
                let s = piece.scale;
                match &self.shapes[piece.shape] {
                    Shape::Factored { low, h } => {
                        let (mask, bits) = (low.len() - 1, low.len().trailing_zeros());
                        let scaled: Vec<F192> = low.iter().map(|&x| s * x).collect();
                        for (i, o) in chunk.iter_mut().enumerate() {
                            let m = first + i;
                            *o += scaled[m & mask] * h[m >> bits];
                        }
                    }
                    Shape::Dense { table, .. } => {
                        for (o, &t) in chunk.iter_mut().zip(&table[first..]) {
                            *o += s * t;
                        }
                    }
                    Shape::Twisted { .. } => {
                        let map = maps[piece.shape].as_ref().expect("a twisted piece's map");
                        let end = first + chunk.len();
                        for (o, m) in chunk.chunks_mut(8).zip((first..end).step_by(8)) {
                            let w = map.at8(m, end);
                            for (o, &w) in o.iter_mut().zip(&w) {
                                *o += s * w;
                            }
                        }
                    }
                }
            }
        });
        // A block folded to one word is a scalar there.
        for piece in &self.pieces {
            let shape = &self.shapes[piece.shape];
            if shape.len() == 1 {
                out[piece.offset >> j] += piece.scale * shape.scalar();
            }
        }
        out
    }
}

/// `Σ_p c_p eq(point_p, ·)` over `2^vars` words, each point's eq as two tables.
fn several_points(terms: &[(usize, F192)], points: &[Vec<F192>], vars: usize) -> Vec<F192> {
    let bits = vars.min(10);
    let tables: Vec<(Vec<F192>, Vec<F192>)> = terms
        .iter()
        .map(|&(p, c)| {
            let point = &points[p][..vars];
            let hi: Vec<F192> = eq_table(&point[bits..]).into_iter().map(|x| c * x).collect();
            (eq_table(&point[..bits]), hi)
        })
        .collect();
    let mut out = zeros(1 << vars);
    parallel::chunks_mut(&mut out, 1 << bits, |row, chunk| {
        let mut acc = vec![F192Unreduced::ZERO; chunk.len()];
        for (lo, hi) in &tables {
            let h = [hi[row]; 4];
            let (four, rest) = lo.as_chunks::<4>();
            for (a, l) in acc.chunks_mut(4).zip(four) {
                for (a, p) in a.iter_mut().zip(mul_unreduced4(h, *l)) {
                    *a ^= p;
                }
            }
            for (a, &l) in acc[4 * four.len()..].iter_mut().zip(rest) {
                *a ^= h[0].mul_unreduced(l);
            }
        }
        for (o, a) in chunk.iter_mut().zip(&acc) {
            *o = a.reduce();
        }
    });
    out
}

/// The stack folded at the rounds so far, `e = eq(r_(<j), ·)`: `Σ_y e(y) C(2^j m + y)` for `m < len`.
pub fn fold_stack(words: &[F64], e: &[F192], len: usize) -> Vec<F192> {
    let j = e.len().trailing_zeros() as usize;
    let table = Table::new(e.to_vec());
    parallel::map_collect(len, |m| table.dot_clipped(words, m << j))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::claims::Column;

    struct Rng(u64);

    impl Rng {
        fn u64(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn e(&mut self) -> F192 {
            F192::new(self.u64(), self.u64(), self.u64())
        }
    }

    /// The weight written out term by term, one eq table per term (the twisted terms' `eq^(2^k)` by squaring).
    fn reference(claim: &Combined<E>, layout: &StackLayout, len: usize) -> Vec<F192> {
        let basis = [F192::ONE, F192::new(0, 1, 0), F192::new(0, 0, 1)];
        let mut weight = vec![F192::ZERO; len];
        for &(column, p, twist, coefficient) in &claim.terms {
            let coefficient = from_v(coefficient);
            let (target, slot) = match column {
                Column::QflockSlot(j) => (Column::Qflock, Some(j)),
                other => (other, None),
            };
            for (limb, vars, offset) in layout.limbs(target) {
                let n = if slot.is_some() { vars - SLOT_BITS } else { vars };
                let point: Vec<F192> = claim.points[p][..n].iter().map(|&x| from_v(x)).collect();
                for (u, mut e) in eq_table(&point).into_iter().enumerate() {
                    for _ in 0..twist {
                        e = e.square();
                    }
                    let at = offset as usize + slot.map_or(u, |j| j + (u << SLOT_BITS));
                    weight[at] += coefficient * basis[limb] * e;
                }
            }
        }
        weight
    }

    fn sums(w: &[F192], c: &[F192]) -> (F192, F192) {
        let at = |v: &[F192], i: usize| v.get(i).copied().unwrap_or(F192::ZERO);
        (0..w.len().div_ceil(2)).fold((F192::ZERO, F192::ZERO), |(a, b), i| {
            let (w0, w1, c0, c1) = (at(w, 2 * i), at(w, 2 * i + 1), at(c, 2 * i), at(c, 2 * i + 1));
            (a + w0 * c0, b + (w0 + w1) * (c0 + c1))
        })
    }

    /// `round_pair` (when it applies) is the plain round and the rounds of clones folded at 0, 1 and a random `β`.
    /// Returns whether it applied.
    fn check_round_pair(weight: &Weight, words: &[F64], e: &[F192], rng: &mut Rng) -> bool {
        let beta = rng.e();
        let Some(p) = weight.round_pair(words, e, beta) else {
            return false;
        };
        assert_eq!(p[0], weight.round(words, e), "the plain round");
        for (k, x) in [F192::ZERO, F192::ONE, beta].into_iter().enumerate() {
            let mut w = weight.clone();
            w.fold(x);
            let e2: Vec<F192> = e.iter().map(|&y| y * (F192::ONE + x)).chain(e.iter().map(|&y| y * x)).collect();
            assert_eq!(p[1 + k], w.round(words, &e2), "the clone at {k}");
        }
        true
    }

    /// `round_pair` on blocks that stay at least four words through the rounds that read the words: every shape.
    #[test]
    fn pair_rounds_are_the_clones_rounds() {
        parallel::init();
        let mut rng = Rng(0xFA12);
        let columns = vec![
            (Column::Qflock, 13, false),
            (Column::Table { table: 0, column: 0 }, 10, false),
            (Column::Heap, 9, true),
            (Column::LeafQuotient { block: 0, chunk: 0 }, 8, true),
            (Column::Memory(0), 7, false),
            (Column::TreeQuotient(1), 0, true),
        ];
        let layout = StackLayout::new(&columns);
        let lane = 1usize << (layout.vars - super::super::opening::LANE_FOLD);
        let len = (layout.words() as usize).div_ceil(lane) * lane;
        let points: Vec<Vec<E>> = (0..5)
            .map(|_| (0..13).map(|_| super::super::poly::to_v(rng.e())).collect())
            .collect();
        let mut terms = Vec::new();
        let mut term =
            |column: Column, p: usize, twist: u8| terms.push((column, p, twist, super::super::poly::to_v(rng.e())));
        term(Column::Table { table: 0, column: 0 }, 0, 0);
        for p in 0..3 {
            term(Column::Heap, p, 0);
        }
        term(Column::LeafQuotient { block: 0, chunk: 0 }, 0, 0);
        term(Column::Memory(0), 1, 0);
        term(Column::TreeQuotient(1), 0, 0);
        for j in [0, 3, 17, 255] {
            term(Column::QflockSlot(j), 3, 0);
        }
        for k in 0..6 {
            term(Column::Qflock, 4, k);
        }
        let claim = Combined {
            points,
            terms,
            value: E::default(),
            relations: 1,
        };
        let words: Vec<F64> = (0..len).map(|_| F64(rng.u64())).collect();
        let words = &words[..];
        let mut weight = Weight::new(&claim, &layout);
        let mut e = vec![F192::ONE];
        for j in 0..6 {
            assert!(check_round_pair(&weight, words, &e, &mut rng), "round {j} pairs");
            let r = rng.e();
            weight.fold(r);
            e = e
                .iter()
                .map(|&x| x * (F192::ONE + r))
                .chain(e.iter().map(|&x| x * r))
                .collect();
        }
    }

    #[test]
    fn pieces_are_the_written_out_weight() {
        parallel::init();
        let mut rng = Rng(0x5EED);
        let columns = vec![
            (Column::Qflock, 12, false),
            (Column::Table { table: 0, column: 0 }, 10, false),
            (Column::Heap, 9, true),
            (Column::LeafQuotient { block: 0, chunk: 0 }, 3, true),
            (Column::Memory(0), 2, false),
            (Column::TreeQuotient(1), 0, true),
        ];
        let layout = StackLayout::new(&columns);
        let lane = 1usize << (layout.vars - super::super::opening::LANE_FOLD);
        let len = (layout.words() as usize).div_ceil(lane) * lane;
        let points: Vec<Vec<E>> = (0..5)
            .map(|_| (0..12).map(|_| super::super::poly::to_v(rng.e())).collect())
            .collect();
        let mut terms = Vec::new();
        let mut term =
            |column: Column, p: usize, twist: u8| terms.push((column, p, twist, super::super::poly::to_v(rng.e())));
        term(Column::Table { table: 0, column: 0 }, 0, 0);
        for p in 0..3 {
            term(Column::Heap, p, 0);
        }
        term(Column::LeafQuotient { block: 0, chunk: 0 }, 0, 0);
        term(Column::Memory(0), 1, 0);
        term(Column::TreeQuotient(1), 0, 0);
        for j in [0, 3, 17, 255] {
            term(Column::QflockSlot(j), 3, 0);
        }
        for k in 0..6 {
            term(Column::Qflock, 4, k);
        }
        let claim = Combined {
            points,
            terms,
            value: E::default(),
            relations: 1,
        };
        // Words past the blocks are not zero: nothing may rely on them.
        let words: Vec<F64> = (0..len).map(|_| F64(rng.u64())).collect();
        let mut dense = reference(&claim, &layout, len);
        let mut weight = Weight::new(&claim, &layout);
        let direct = dense
            .iter()
            .zip(&words)
            .fold(F192::ZERO, |acc, (w, &k)| acc + w.mul_base(k));
        assert_eq!(weight.sum(&words), direct);
        let mut stack: Vec<F192> = words.iter().map(|&k| F192::from(k)).collect();
        let mut e = vec![F192::ONE];
        for j in 0..LOW_VARS {
            assert_eq!(weight.round(&words, &e), sums(&dense, &stack), "round {j}");
            check_round_pair(&weight, &words, &e, &mut rng);
            let full = 1usize << (layout.vars - j);
            let mut written = weight.dense(full);
            assert!(written[dense.len()..].iter().all(|x| x.is_zero()));
            written.truncate(dense.len());
            assert_eq!(written, dense, "the weight written out after {j} rounds");
            let mut c = fold_stack(&words, &e, full);
            assert!(c[stack.len()..].iter().all(|x| x.is_zero()));
            c.truncate(stack.len());
            assert_eq!(c, stack, "the stack folded {j} rounds");
            let r = rng.e();
            weight.fold(r);
            dense = fold(&dense, r);
            stack = fold(&stack, r);
            e = e
                .iter()
                .map(|&x| x * (F192::ONE + r))
                .chain(e.iter().map(|&x| x * r))
                .collect();
        }
    }
}
