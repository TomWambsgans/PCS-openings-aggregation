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
//! `2^(a + j)` words ([`dot_base`]), the twisted piece's one map lookup per pair of words.

use leanvm_flock_gas::field::E;
use primitives::field::{F64, F192, F192Unreduced, Weights8, dot_base};
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

/// `x ↦ Σ_k c_k x^(2^k)` for `N` coefficient lists at once, GF(2)-linear on `E`, as 24 byte tables:
/// `L(x) = Σ_j T_j[byte_j(x)]`.
pub struct Linear<const N: usize> {
    tables: Vec<[[F192; N]; 256]>,
}

impl<const N: usize> Linear<N> {
    /// `coefficients[n][k]` is map `n`'s coefficient of `x^(2^k)`.
    pub fn new(coefficients: [&[F192]; N]) -> Self {
        let top = coefficients.iter().map(|c| c.len()).max().unwrap_or(0);
        let image = |x: F192| {
            let mut power = x;
            let mut sum = [F192::ZERO; N];
            for k in 0..top {
                for (s, c) in sum.iter_mut().zip(&coefficients) {
                    if let Some(&c) = c.get(k) {
                        *s += c * power;
                    }
                }
                power = power.square();
            }
            sum
        };
        let mut tables = vec![[[F192::ZERO; N]; 256]; 24];
        for (j, table) in tables.iter_mut().enumerate() {
            let (limb, byte) = (j / 8, j % 8);
            let bits: Vec<[F192; N]> = (0..8)
                .map(|i| {
                    let mut c = [0u64; 3];
                    c[limb] = 1u64 << (8 * byte + i);
                    image(F192::new(c[0], c[1], c[2]))
                })
                .collect();
            for v in 1..256usize {
                let low = v.trailing_zeros() as usize;
                table[v] = std::array::from_fn(|n| table[v & (v - 1)][n] + bits[low][n]);
            }
        }
        Self { tables }
    }

    #[inline]
    pub fn at(&self, x: F192) -> [F192; N] {
        let mut acc = [F192::ZERO; N];
        for (limb, word) in [x.c0, x.c1, x.c2].into_iter().enumerate() {
            for byte in 0..8 {
                let entry = &self.tables[8 * limb + byte][(word >> (8 * byte)) as usize & 0xff];
                for (a, &e) in acc.iter_mut().zip(entry) {
                    *a += e;
                }
            }
        }
        acc
    }
}

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

enum Shape {
    /// `low[i mod 2^a] · h[i >> a]`, `h = eq(high, ·)`.
    Factored { low: Vec<F192>, h: Vec<F192> },
    Dense(Vec<F192>),
    /// `Σ_k c_k eq(point_(≥bound), ·)^(2^k)`.
    Twisted { c: Vec<F192>, point: Vec<F192>, bound: usize },
}

impl Shape {
    /// The shape's words left (after the rounds so far).
    fn len(&self) -> usize {
        match self {
            Shape::Factored { low, h } => low.len() * h.len(),
            Shape::Dense(t) => t.len(),
            Shape::Twisted { point, bound, .. } => 1 << (point.len() - bound),
        }
    }

    /// Folded to one word: its value.
    fn scalar(&self) -> F192 {
        assert_eq!(self.len(), 1);
        match self {
            Shape::Factored { low, h } => low[0] * h[0],
            Shape::Dense(t) => t[0],
            Shape::Twisted { c, .. } => c.iter().fold(F192::ZERO, |acc, &x| acc + x),
        }
    }
}

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
    Factored { ga: Table, gb: Table, span: usize },
    Dense,
    /// `eq(point_(>j), i)` as `lo[i mod 2^bits] hi[i >> bits]`; the map's pair `(W(2i), W(2i) + W(2i + 1))` of it.
    Twisted { lo: Vec<F192>, hi: Vec<F192>, bits: usize, map: Linear<2> },
    Scalar(F192),
}

/// `eq(point, ·)` as two tables, `lo[i mod 2^bits] hi[i >> bits]`.
fn split_eq(point: &[F192]) -> (Vec<F192>, Vec<F192>, usize) {
    let bits = point.len().min(10);
    (eq_table(&point[..bits]), eq_table(&point[bits..]), bits)
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
pub struct Weight {
    pieces: Vec<Piece>,
    shapes: Vec<Shape>,
    round: usize,
}

impl Weight {
    /// The weight of `claim` on the stack `layout` places.
    pub fn new(claim: &Combined<E>, layout: &StackLayout) -> Self {
        let basis = [F192::ONE, F192::new(0, 1, 0), F192::new(0, 0, 1)];
        let points: Vec<Vec<F192>> = claim.points.iter().map(|p| p.iter().map(|&x| from_v(x)).collect()).collect();
        // Per column: its terms by point, untwisted (point, coefficient), twisted (point, [(twist, coefficient)]), and
        // q_flock's slots (point, the slots' coefficients).
        #[derive(Default)]
        struct Terms {
            plain: Vec<(usize, F192)>,
            twisted: Vec<(usize, Vec<(u8, F192)>)>,
            slots: Vec<(usize, Vec<F192>)>,
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
                    terms.plain.push((p, list.iter().fold(F192::ZERO, |acc, &(_, c)| acc + c)));
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
                    weight.shapes.push(Shape::Dense(several_points(several, &points, vars)));
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
        let preps: Vec<Option<(Table, Option<Linear<1>>, Vec<F192>, Vec<F192>, usize)>> = self
            .shapes
            .iter()
            .map(|shape| match shape {
                Shape::Factored { low, .. } => Some((Table::new(low.clone()), None, Vec::new(), Vec::new(), 0)),
                Shape::Dense(_) => None,
                Shape::Twisted { c, point, .. } => {
                    let (lo, hi, bits) = split_eq(point);
                    Some((Table::Plain(Vec::new()), Some(Linear::new([c])), lo, hi, bits))
                }
            })
            .collect();
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
                match (&self.shapes[piece.shape], &preps[piece.shape]) {
                    (Shape::Factored { low, h }, Some((g, ..))) => {
                        for u in start..end {
                            let at = piece.offset + u * low.len();
                            acc ^= h[u].mul_unreduced(g.dot(&words[at..]).reduce());
                        }
                    }
                    (Shape::Dense(table), _) => {
                        for i in start..end {
                            acc ^= table[i].mul_base_unreduced(words[piece.offset + i]);
                        }
                    }
                    (Shape::Twisted { .. }, Some((_, Some(map), lo, hi, bits))) => {
                        let mask = (1 << bits) - 1;
                        for i in start..end {
                            let [w] = map.at(lo[i & mask] * hi[i >> bits]);
                            acc ^= w.mul_base_unreduced(words[piece.offset + i]);
                        }
                    }
                    _ => unreachable!(),
                }
                piece.scale * acc.reduce()
            },
            |a, b| a + b,
        )
    }

    /// Every piece's units split into tasks: `units(piece)` is (its units, units per task).
    fn tasks(&self, units: impl Fn(&Piece) -> (usize, usize)) -> Vec<(usize, usize, usize)> {
        let mut tasks = Vec::new();
        for (index, piece) in self.pieces.iter().enumerate() {
            let (count, per) = units(piece);
            tasks.extend((0..count).step_by(per).map(|start| (index, start, (start + per).min(count))));
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
                                ga[y + (2 * l << j)] = w0 * ey;
                                gb[y + (2 * l << j)] = dw * ey;
                                gb[y + ((2 * l + 1) << j)] = dw * ey;
                            }
                        }
                        let gb = Table::trimmed(gb, &[&ga]);
                        let mut ga = ga;
                        ga.truncate(gb.len());
                        Prep::Factored {
                            ga: Table::new(ga),
                            gb,
                            span,
                        }
                    }
                    Shape::Dense(_) => Prep::Dense,
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
        let tasks = self.tasks(|piece| match &preps[piece.shape] {
            Prep::Factored { span, .. } => (self.shape_units(piece.shape, *span), (TASK_WORDS / span).max(1)),
            Prep::Dense | Prep::Twisted { .. } => (1 << (piece.vars - j - 1), (TASK_WORDS >> (j + 1)).max(1)),
            Prep::Scalar(_) => (1, 1),
        });
        let pair_c = |at: usize| -> (F192, F192) {
            (folded.dot_clipped(words, at), folded.dot_clipped(words, at + (1 << j)))
        };
        let (a, b) = parallel::map_reduce(
            tasks.len(),
            || (F192::ZERO, F192::ZERO),
            |t| {
                let (index, start, end) = tasks[t];
                let piece = &self.pieces[index];
                let (mut a, mut b) = (F192Unreduced::ZERO, F192Unreduced::ZERO);
                match (&preps[piece.shape], &self.shapes[piece.shape]) {
                    (Prep::Factored { ga, gb, span }, Shape::Factored { h, .. }) => {
                        for u in start..end {
                            let at = &words[piece.offset + u * span..];
                            a ^= h[u].mul_unreduced(ga.dot(at).reduce());
                            b ^= h[u].mul_unreduced(gb.dot(at).reduce());
                        }
                    }
                    (Prep::Dense, Shape::Dense(table)) => {
                        for i in start..end {
                            let (w0, dw) = (table[2 * i], table[2 * i] + table[2 * i + 1]);
                            let at = piece.offset + (2 * i << j);
                            if j == 0 {
                                let (c0, c1) = (words[at], words[at + 1]);
                                a ^= w0.mul_base_unreduced(c0);
                                b ^= dw.mul_base_unreduced(c0 + c1);
                            } else {
                                let (c0, c1) = pair_c(at);
                                a ^= w0.mul_unreduced(c0);
                                b ^= dw.mul_unreduced(c0 + c1);
                            }
                        }
                    }
                    (Prep::Twisted { lo, hi, bits, map }, _) => {
                        let mask = (1 << bits) - 1;
                        for i in start..end {
                            let [w0, dw] = map.at(lo[i & mask] * hi[i >> bits]);
                            let at = piece.offset + (2 * i << j);
                            if j == 0 {
                                let (c0, c1) = (words[at], words[at + 1]);
                                a ^= w0.mul_base_unreduced(c0);
                                b ^= dw.mul_base_unreduced(c0 + c1);
                            } else {
                                let (c0, c1) = pair_c(at);
                                a ^= w0.mul_unreduced(c0);
                                b ^= dw.mul_unreduced(c0 + c1);
                            }
                        }
                    }
                    (Prep::Scalar(value), _) => {
                        // The block is one word of the folded stack, at its offset's position.
                        let position = piece.offset >> j;
                        let (own, other) = (folded.dot_clipped(words, position << j), folded.dot_clipped(words, (position ^ 1) << j));
                        let s = piece.scale * *value;
                        let a = if position & 1 == 0 { s * own } else { F192::ZERO };
                        return (a, s * (own + other));
                    }
                    _ => unreachable!(),
                }
                (piece.scale * a.reduce(), piece.scale * b.reduce())
            },
            |x, y| (x.0 + y.0, x.1 + y.1),
        );
        (a, b)
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
                Shape::Dense(table) => *table = fold(table, r),
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
        let j = self.round;
        let mut out = vec![F192::ZERO; len];
        for piece in &self.pieces {
            let shape = &self.shapes[piece.shape];
            let at = piece.offset >> j;
            if shape.len() == 1 {
                out[at] += piece.scale * shape.scalar();
                continue;
            }
            let block = &mut out[at..at + shape.len()];
            let s = piece.scale;
            match shape {
                Shape::Factored { low, h } => {
                    let a = low.len();
                    parallel::chunks_mut(block, a.max(1 << 12), |c, chunk| {
                        let first = c * a.max(1 << 12);
                        for (m, o) in chunk.iter_mut().enumerate() {
                            let m = first + m;
                            *o += s * low[m % a] * h[m / a];
                        }
                    });
                }
                Shape::Dense(table) => {
                    parallel::chunks_mut_zip(block, table, 1 << 12, |_, chunk, table| {
                        for (o, &t) in chunk.iter_mut().zip(table) {
                            *o += s * t;
                        }
                    });
                }
                Shape::Twisted { c, point, bound } => {
                    let map = Linear::new([&c[..]]);
                    let (lo, hi, bits) = split_eq(&point[*bound..]);
                    let mask = (1 << bits) - 1;
                    parallel::chunks_mut(block, 1 << 12, |c, chunk| {
                        for (m, o) in chunk.iter_mut().enumerate() {
                            let m = (c << 12) + m;
                            let [w] = map.at(lo[m & mask] * hi[m >> bits]);
                            *o += s * w;
                        }
                    });
                }
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
    let mut out = vec![F192::ZERO; 1 << vars];
    parallel::chunks_mut(&mut out, 1 << bits, |row, chunk| {
        for (lo, hi) in &tables {
            let h = hi[row];
            for (o, &l) in chunk.iter_mut().zip(lo) {
                *o += h * l;
            }
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
        let mut term = |column: Column, p: usize, twist: u8| terms.push((column, p, twist, super::super::poly::to_v(rng.e())));
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
        let direct = dense.iter().zip(&words).fold(F192::ZERO, |acc, (w, &k)| acc + w.mul_base(k));
        assert_eq!(weight.sum(&words), direct);
        let mut stack: Vec<F192> = words.iter().map(|&k| F192::from(k)).collect();
        let mut e = vec![F192::ONE];
        for j in 0..LOW_VARS {
            assert_eq!(weight.round(&words, &e), sums(&dense, &stack), "round {j}");
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
            e = e.iter().map(|&x| x * (F192::ONE + r)).chain(e.iter().map(|&x| x * r)).collect();
        }
    }
}
