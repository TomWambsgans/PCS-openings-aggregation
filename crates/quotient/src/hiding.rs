// Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The two attack tests at the end are an independent
// review's (`review_zk_calldata_only`, `review_zk_distinguish_and_unmask`), turned around to assert that the
// attacks no longer distinguish.
//! The exact checks behind `HIDING.md`, in the real fields (`K = GF(2^64)`, `E = GF(2^192)`, WHIR's novel
//! basis on its own domain).
//!
//! An opening of a hidden table shows, up to and including WHIR's first fold, three families of `K`-linear forms
//! in the stack's entries (everything later is a function of the folded table): the twelve values of the six
//! lane rounds, the folded table `f¹ = Σ_l eq(φ, l)·lane_l`, and every lane at the opened positions `Q`. For
//! fixed challenges the view is `M_R·r + M_D·d` (`r` the random unknowns, `d` the table's entries), so it is
//! distributed independently of `d` given the claims `C·d` if and only if `M_D(ker C) ⊆ im M_R`, that is
//! `rank [[M_R, M_D], [0, C]] = rank M_R + rank C`. [`view_ranks`] computes both sides exactly on scaled-down
//! layouts built by the same code as the real ones. [`round_freedom`] computes, on the full-size layouts, the
//! condition of `HIDING.md`'s argument on the lane rounds (condition (R)), which the gadget makes hold for every
//! challenge outside a set of probability below `2^-188`: [`rounds_are_free_for_every_challenge`] checks the
//! argument's parts, the E-linear core exactly, at challenges chosen against it.

use primitives::field::{F64, F192, powers};
use primitives::test_rng::Rng;

use pcs::whir::LaneTensor;

use crate::opening::{self, Claim, GADGET, LANE_FOLD, LOG_INV_RATE, Lane, Layout, gadget_beta, gadget_lanes};
use crate::protocol::{Channel, Q_SPILL, extension, quotient_chunks, reduce, sum_point};
use crate::transcript::TranscriptError;

/// The `K` coordinates of an `E` value.
pub(crate) fn coords(x: F192) -> [F64; 3] {
    [F64(x.c0), F64(x.c1), F64(x.c2)]
}

/// A `K`-subspace, as rows in echelon form: each with its pivot (normalized to one), and its nonzero columns
/// when they are few.
struct Span {
    rows: Vec<(usize, Vec<F64>, Option<Vec<usize>>)>,
}

impl Span {
    fn new() -> Self {
        Self { rows: vec![] }
    }

    fn rank(&self) -> usize {
        self.rows.len()
    }

    /// Add `v` to the span; whether it was outside it.
    fn insert(&mut self, mut v: Vec<F64>) -> bool {
        // Each row is zero at the pivots of the rows before it, so one pass in order reduces `v`.
        for (pivot, row, support) in &self.rows {
            let f = v[*pivot];
            if f.is_zero() {
                continue;
            }
            match support {
                Some(columns) => columns.iter().for_each(|&i| v[i] += f * row[i]),
                None => v.iter_mut().zip(row).for_each(|(a, &b)| *a += f * b),
            }
        }
        let Some(pivot) = v.iter().position(|x| !x.is_zero()) else {
            return false;
        };
        let inverse = v[pivot].inv();
        v.iter_mut().for_each(|x| *x *= inverse);
        let nonzero: Vec<usize> = (0..v.len()).filter(|&i| !v[i].is_zero()).collect();
        let support = (nonzero.len() * 8 < v.len()).then_some(nonzero);
        self.rows.push((pivot, v, support));
        true
    }
}

/// The rank of a set of `K`-rows.
pub(crate) fn rank(rows: impl IntoIterator<Item = Vec<F64>>) -> usize {
    let mut span = Span::new();
    rows.into_iter().for_each(|row| {
        span.insert(row);
    });
    span.rank()
}

/// A basis of the kernel of the `K`-matrix `m` (`n` columns).
pub(crate) fn kernel(m: &[Vec<F64>], n: usize) -> Vec<Vec<F64>> {
    let mut rows: Vec<Vec<F64>> = m.to_vec();
    let mut pivots = vec![];
    let mut r = 0;
    for c in 0..n {
        let Some(p) = (r..rows.len()).find(|&i| !rows[i][c].is_zero()) else {
            continue;
        };
        rows.swap(r, p);
        let inverse = rows[r][c].inv();
        rows[r].iter_mut().for_each(|x| *x *= inverse);
        for i in 0..rows.len() {
            let f = rows[i][c];
            if i != r && !f.is_zero() {
                let pivot_row = rows[r].clone();
                rows[i].iter_mut().zip(&pivot_row).for_each(|(a, &b)| *a += f * b);
            }
        }
        pivots.push(c);
        r += 1;
    }
    (0..n)
        .filter(|c| !pivots.contains(c))
        .map(|free| {
            let mut v = vec![F64::ZERO; n];
            v[free] = F64::ONE;
            for (i, &c) in pivots.iter().enumerate() {
                v[c] = rows[i][free];
            }
            v
        })
        .collect()
}

/// A lane's codeword at domain position `position`, as a form in its `2^log_lane` entries: entry `y` weighs
/// `Π_{k ∈ y} Ŵ_k(x)`, the novel basis at `x`, with the subspace polynomials the verifier uses.
pub(crate) fn column(log_lane: usize, position: usize) -> Vec<F64> {
    let mut roots = vec![F64::ONE];
    let mut layer: Vec<F64> = (1..=log_lane).map(|i| F64(1 << i)).collect();
    for _ in 0..log_lane {
        let root = roots[roots.len() - 1];
        layer.iter_mut().for_each(|v| *v = v.square() + root * *v);
        roots.push(layer.remove(0));
    }
    let mut w = F64(position as u64);
    let mut out = vec![F64::ONE];
    for &root in &roots[..log_lane] {
        let hat = w * root.inv();
        let len = out.len();
        for i in 0..len {
            let v = out[i] * hat;
            out.push(v);
        }
        w = w.square() + root * w;
    }
    out
}

/// `eq(φ_{<j}, bits of l below j)`.
fn eq_prefix(phi: &[F192], j: usize, l: usize) -> F192 {
    (0..j).fold(F192::ONE, |w, k| {
        w * if (l >> k) & 1 == 1 { phi[k] } else { F192::ONE + phi[k] }
    })
}

/// `eq(φ, bits of l)`: lane `l`'s weight in the first fold.
pub(crate) fn fold_weight(phi: &[F192], l: usize) -> F192 {
    eq_prefix(phi, phi.len(), l)
}

/// What a unit of lane `r` weighs in the twelve lane-round values through a unit of lane `l`'s weight at the
/// same entry: round `j` pairs lanes that agree above bit `j`, with `eq(φ_{<j}, ·)` on each, in `h_j`'s
/// quadratic coefficient, and, when both have bit `j` zero, in `h_j(0)`.
fn pairing(phi: &[F192], l: usize, r: usize) -> [F192; 12] {
    let mut out = [F192::ZERO; 12];
    for j in 0..LANE_FOLD {
        if l >> (j + 1) == r >> (j + 1) {
            let c = eq_prefix(phi, j, l) * eq_prefix(phi, j, r);
            out[2 * j + 1] = c;
            if (l >> j) & 1 == 0 && (r >> j) & 1 == 0 {
                out[2 * j] = c;
            }
        }
    }
    out
}

/// The dense weight of lane tensors on the stack.
fn dense(layout: &Layout, tensors: &[LaneTensor]) -> Vec<F192> {
    let lane = 1usize << layout.log_lane();
    let mut weight = vec![F192::ZERO; layout.placed()];
    for tensor in tensors {
        for (l, &scale) in tensor.scales.iter().enumerate() {
            if !scale.is_zero() {
                let out = &mut weight[l * lane..(l + 1) * lane];
                out.iter_mut().zip(&tensor.low).for_each(|(o, &e)| *o += scale * e);
            }
        }
    }
    weight
}

/// The opening's weight, written out, with only the gadget's patterns `patterns` (all three in the real one,
/// [`Layout::weight`]): the claims at `points` scaled by `lambdas`, and those patterns.
fn opening_weight(layout: &Layout, points: &[Vec<F192>], lambdas: &[F192], patterns: &[usize]) -> Vec<F192> {
    let tensors: Vec<LaneTensor> = points
        .iter()
        .zip(lambdas)
        .flat_map(|(p, &lambda)| layout.tensors(p, lambda))
        .collect();
    let mut weight = dense(layout, &tensors);
    let log_lane = layout.log_lane();
    for &g in patterns {
        for i in 0..3 {
            for &l in gadget_lanes(g) {
                weight[(l << log_lane) + layout.gadget_entry(g, i)] += gadget_beta(i);
            }
        }
    }
    weight
}

/// The weight of the gadget's patterns `patterns` on entry `y` of lane `l`.
fn pattern_weight(layout: &Layout, patterns: &[usize], l: usize, y: usize) -> F192 {
    let on = |g: usize| (0..3).any(|i| layout.gadget_entry(g, i) == y) && gadget_lanes(g).contains(&l);
    if patterns.iter().any(|&g| on(g)) {
        layout.gadget_at(l, y)
    } else {
        F192::ZERO
    }
}

/// The six lane rounds of the sumcheck of `Σ weight · stack`, as forms in the stack's entries: per round, the
/// coefficient of each entry in `h_j(0)` and in `h_j`'s quadratic coefficient (what the prover sends).
fn lane_rounds(layout: &Layout, weight: &[F192], phi: &[F192]) -> Vec<Vec<F192>> {
    let (lanes, lane) = (layout.lanes(), 1usize << layout.log_lane());
    let mut forms = vec![vec![F192::ZERO; lanes * lane]; 2 * LANE_FOLD];
    for r in 0..lanes {
        for l in 0..lanes {
            let pair = pairing(phi, l, r);
            for (t, form) in forms.iter_mut().enumerate() {
                if pair[t].is_zero() {
                    continue;
                }
                for y in 0..lane {
                    form[r * lane + y] += pair[t] * weight[l * lane + y];
                }
            }
        }
    }
    forms
}

/// The twelve lane-round values of a weight `w` against a table `t` at one entry (the lanes padded to 64),
/// folded as the prover folds them.
pub(crate) fn rounds_at(w: &[F192], t: &[F192], phi: &[F192]) -> [F192; 12] {
    let mut w = w.to_vec();
    let mut t = t.to_vec();
    w.resize(1 << LANE_FOLD, F192::ZERO);
    t.resize(1 << LANE_FOLD, F192::ZERO);
    let mut out = [F192::ZERO; 12];
    for j in 0..LANE_FOLD {
        let half = w.len() / 2;
        for i in 0..half {
            out[2 * j] += w[2 * i] * t[2 * i];
            out[2 * j + 1] += (w[2 * i] + w[2 * i + 1]) * (t[2 * i] + t[2 * i + 1]);
        }
        for i in 0..half {
            w[i] = w[2 * i] + phi[j] * (w[2 * i] + w[2 * i + 1]);
            t[i] = t[2 * i] + phi[j] * (t[2 * i] + t[2 * i + 1]);
        }
        w.truncate(half);
        t.truncate(half);
    }
    out
}

/// The last round's value at its challenge of round values `values` (twelve) that start from a zero claim:
/// `lastMap` of `formal/QuotientSecurity/Hiding/Rounds.lean`.
pub(crate) fn last_claim(values: &[F192], phi: &[F192]) -> F192 {
    let mut claim = F192::ZERO;
    for j in 0..LANE_FOLD {
        let (at_zero, quadratic) = (values[2 * j], values[2 * j + 1]);
        claim = at_zero + (claim + quadratic) * phi[j] + quadratic * phi[j] * phi[j];
    }
    claim
}

/// Whether the round values `values` (twelve) leave the last round's value at its challenge unchanged: what
/// every change that keeps the claims and `f¹` must do (`h_5(φ_5) = Σ W̃(·, φ)·f¹`).
pub(crate) fn keeps_last_claim(values: &[F192], phi: &[F192]) -> bool {
    last_claim(values, phi).is_zero()
}

/// What a stack entry of a hidden layout is, to the view.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Unknown {
    /// The table's entry.
    Data,
    /// Uniform, on its own.
    Random,
    /// The same uniform value as stack entry `i` (a gadget pair's second lane).
    Copy(usize),
    /// Zero (the overflow lane at the gadget's third pattern).
    Zero,
}

/// What stack entry `index` of a hidden layout is.
pub(crate) fn unknown(layout: &Layout, index: usize) -> Unknown {
    let s = layout.log_piece().expect("a hidden layout");
    let log_lane = layout.log_lane();
    let (l, y) = (index >> log_lane, index & ((1 << log_lane) - 1));
    if y < 1 << s {
        return match y.checked_sub((1 << s) - GADGET) {
            Some(k) => match *gadget_lanes(k / 3) {
                [a, b] if l == b => Unknown::Copy((a << log_lane) | y),
                [a] if l == a => Unknown::Zero,
                _ => Unknown::Random,
            },
            None => Unknown::Random,
        };
    }
    match layout.lane(l) {
        Lane::Random => Unknown::Random,
        Lane::Overflow if y >> s > layout.pieces().len() => Unknown::Random,
        _ => Unknown::Data,
    }
}

fn push_e(rows: &mut Vec<Vec<F64>>, form: &[F192]) {
    for c in 0..3 {
        rows.push(form.iter().map(|&x| coords(x)[c]).collect());
    }
}

/// Distinct random positions of the first level's domain, `2^(log_lane + 1)` of them.
fn positions(log_lane: usize, count: usize, rng: &mut Rng) -> Vec<usize> {
    let mut out: Vec<usize> = vec![];
    while out.len() < count {
        let x = (rng.next_u64() as usize) & ((2 << log_lane) - 1);
        if !out.contains(&x) {
            out.push(x);
        }
    }
    out
}

/// What an opening's view up to its first fold shows of a hidden table, for claims at `points`, `queries` opened
/// positions and the gadget's patterns `patterns`, at random challenges: `(rank M_R, rank C, rank [[M_R, M_D],
/// [0, C]])`, and the K-dimension of one more, unopened, row's randomness beyond the view (the entropy the Merkle
/// siblings rest on).
fn view_ranks(layout: &Layout, points: &[Vec<F192>], queries: usize, patterns: &[usize], rng: &mut Rng) -> [usize; 4] {
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let lane = 1usize << log_lane;
    let placed = layout.placed();
    let weight = opening_weight(layout, points, &powers(rng.ext(), points.len()), patterns);
    let phi = rng.ext_vec(LANE_FOLD);

    // The view, as K-rows over the stack's entries: the rounds, `f¹`, the lanes at the opened positions.
    let mut view: Vec<Vec<F64>> = vec![];
    for form in lane_rounds(layout, &weight, &phi) {
        push_e(&mut view, &form);
    }
    for y in 0..lane {
        let mut form = vec![F192::ZERO; placed];
        for l in 0..lanes {
            form[l * lane + y] = fold_weight(&phi, l);
        }
        push_e(&mut view, &form);
    }
    let at = positions(log_lane, queries + 1, rng);
    let row = |x: usize| -> Vec<Vec<F64>> {
        let col = column(log_lane, x);
        (0..lanes)
            .map(|l| {
                let mut row = vec![F64::ZERO; placed];
                row[l * lane..(l + 1) * lane].copy_from_slice(&col);
                row
            })
            .collect()
    };
    for &x in &at[..queries] {
        view.extend(row(x));
    }
    let unopened = row(at[queries]);
    // The claims, on the stack's entries, and the gadget alone.
    let mut claim_rows = vec![];
    for p in points {
        push_e(&mut claim_rows, &dense(layout, &layout.tensors(p, F192::ONE)));
    }
    let mut gadget_rows = vec![];
    push_e(&mut gadget_rows, &opening_weight(layout, &[], &[], patterns));

    // The unknowns: an entry of the table, or a random one. A gadget pair's second lane is its first lane's
    // unknown; the overflow lane's zeros there are no unknown.
    let kinds: Vec<Unknown> = (0..placed).map(|i| unknown(layout, i)).collect();
    let random: Vec<usize> = (0..placed).filter(|&i| kinds[i] == Unknown::Random).collect();
    let data: Vec<usize> = (0..placed).filter(|&i| kinds[i] == Unknown::Data).collect();
    let mut copies = vec![vec![]; placed];
    for (j, kind) in kinds.iter().enumerate() {
        if let Unknown::Copy(i) = *kind {
            copies[i].push(j);
        }
    }
    let on_random = |row: &[F64]| -> Vec<F64> {
        random
            .iter()
            .map(|&i| copies[i].iter().fold(row[i], |acc, &j| acc + row[j]))
            .collect()
    };
    let on_data = |row: &[F64]| -> Vec<F64> { data.iter().map(|&i| row[i]).collect() };
    for row in claim_rows.iter().chain(&gadget_rows) {
        assert!(
            on_random(row).iter().all(|x| x.is_zero()),
            "the claims and the gadget weigh no randomness"
        );
    }
    let view_random = rank(view.iter().map(|row| on_random(row)));
    let claims = rank(claim_rows.iter().map(|row| on_data(row)));
    let whole = rank(
        view.iter().map(|row| [on_random(row), on_data(row)].concat()).chain(
            claim_rows
                .iter()
                .map(|row| [vec![F64::ZERO; random.len()], on_data(row)].concat()),
        ),
    );
    let with_unopened = rank(view.iter().chain(&unopened).map(|row| on_random(row)));
    [view_random, claims, whole, with_unopened - view_random]
}

/// The K-dimension of what the opening's view reveals of the table beyond the claims (zero: it hides it).
fn leak(layout: &Layout, points: &[Vec<F192>], queries: usize, patterns: &[usize], rng: &mut Rng) -> usize {
    let [view_random, claims, whole, _] = view_ranks(layout, points, queries, patterns, rng);
    whole - view_random - claims
}

/// The random unknowns at in-lane entry `y`, each as the lanes whose entry `y` it is (a gadget pair's two lanes
/// at its entries).
pub(crate) fn random_at(layout: &Layout, y: usize) -> Vec<Vec<usize>> {
    let log_lane = layout.log_lane();
    let kinds: Vec<Unknown> = (0..layout.lanes())
        .map(|l| unknown(layout, (l << log_lane) | y))
        .collect();
    (0..layout.lanes())
        .filter(|&l| kinds[l] == Unknown::Random)
        .map(|l| {
            let at = (l << log_lane) | y;
            let mut u = vec![l];
            u.extend((0..layout.lanes()).filter(|&m| kinds[m] == Unknown::Copy(at)));
            u
        })
        .collect()
}

/// The gadget's entries, in every lane's first piece.
pub(crate) fn gadget_entries(layout: &Layout) -> Vec<usize> {
    (0..3)
        .flat_map(|g| (0..3).map(move |i| layout.gadget_entry(g, i)))
        .collect()
}

/// `count` entries past the first piece, half where the overflow lane holds the table and half where it does
/// not (all of them if fewer).
pub(crate) fn data_entries(layout: &Layout, count: usize, rng: &mut Rng) -> Vec<usize> {
    let s = layout.log_piece().expect("a hidden layout");
    let held = layout.pieces().len();
    let mut chosen = vec![];
    for holds in [true, false] {
        let entries: Vec<usize> = (1 << s..1 << layout.log_lane())
            .filter(|&y| ((y >> s) <= held) == holds)
            .collect();
        if entries.len() <= count / 2 {
            chosen.extend(entries);
        } else {
            chosen.extend((0..count / 2).map(|_| entries[(rng.next_u64() as usize) % entries.len()]));
        }
    }
    chosen
}

/// Condition (R) of `HIDING.md`: the K-span the randomness gives the twelve lane-round values once `f¹` is
/// pinned, through the entries `entries`, for claims at `points` batched by `lambdas` and the gadget's patterns
/// `patterns`. At entry `y` the random unknowns there ([`random_at`]) leave `f¹(y)` alone along the kernel of
/// their fold weights, `ker_y = {k : Σ_u k_u·Σ_{r ∈ u} eq(φ, r) = 0}`, and move the rounds by
/// `Σ_l W_l(y)·Σ_u k_u·Σ_{r ∈ u} pairing(l, r)`, `W_l(y)` the opening's weight at entry `y` of lane `l`. The span
/// lies in the 33 dimensions that keep the last claim (asserted); it is 33 when (R) holds.
pub(crate) fn round_freedom(
    layout: &Layout,
    points: &[Vec<F192>],
    lambdas: &[F192],
    patterns: &[usize],
    phi: &[F192],
    entries: &[usize],
) -> usize {
    let lanes = layout.lanes();
    let scales: Vec<_> = points.iter().map(|p| layout.scales(p)).collect();
    let mut freedom = Span::new();
    for &y in entries {
        let unknowns = random_at(layout, y);
        let folds: Vec<F192> = unknowns
            .iter()
            .map(|u| u.iter().fold(F192::ZERO, |acc, &r| acc + fold_weight(phi, r)))
            .collect();
        let m: Vec<Vec<F64>> = (0..3).map(|c| folds.iter().map(|&f| coords(f)[c]).collect()).collect();
        let weights: Vec<F192> = (0..lanes)
            .map(|l| {
                let claims = points
                    .iter()
                    .zip(&scales)
                    .zip(lambdas)
                    .fold(F192::ZERO, |acc, ((p, sc), &lambda)| {
                        acc + lambda * layout.weight_at(p, sc, l, y)
                    });
                claims + pattern_weight(layout, patterns, l, y)
            })
            .collect();
        // What one unit of each unknown moves the rounds by.
        let moves: Vec<[F192; 12]> = unknowns
            .iter()
            .map(|u| {
                let mut t = vec![F192::ZERO; lanes];
                u.iter().for_each(|&r| t[r] = F192::ONE);
                rounds_at(&weights, &t, phi)
            })
            .collect();
        for k in kernel(&m, unknowns.len()) {
            let mut total = [F192::ZERO; 12];
            for (mv, &ku) in moves.iter().zip(&k) {
                total.iter_mut().zip(mv).for_each(|(o, &x)| *o += x.mul_base(ku));
            }
            assert!(keeps_last_claim(&total, phi));
            freedom.insert(total.iter().flat_map(|&x| coords(x)).collect());
        }
    }
    freedom.rank()
}

/// Condition (S) of `HIDING.md`: the K-dimension of the random lanes' fold weights (3 when they span `E`).
pub(crate) fn fold_span(layout: &Layout, phi: &[F192]) -> usize {
    rank(
        (0..layout.lanes())
            .filter(|&l| layout.lane(l) == Lane::Random)
            .map(|r| coords(fold_weight(phi, r)).to_vec()),
    )
}

/// (R) through the gadget's entries alone, with all three patterns: it does not depend on the claims.
pub(crate) fn gadget_freedom(layout: &Layout, phi: &[F192]) -> usize {
    round_freedom(layout, &[], &[], &[0, 1, 2], phi, &gadget_entries(layout))
}

/// A verifier's channel that reads nothing but random scalars: the reduction's claims at random challenges.
struct RandomChannel(Rng);

impl Channel<F192> for RandomChannel {
    fn statement(&mut self) -> [F192; 4] {
        std::array::from_fn(|_| self.0.ext())
    }
    fn next_root(&mut self) -> Result<[F192; 2], TranscriptError> {
        Ok([self.0.ext(), self.0.ext()])
    }
    fn next(&mut self) -> Result<F192, TranscriptError> {
        Ok(self.0.ext())
    }
    fn sample(&mut self) -> F192 {
        self.0.ext()
    }
    fn finish(&mut self) -> Result<(), TranscriptError> {
        Ok(())
    }
}

/// The reduction's claim points at random challenges: the witness table's, and the quotient table's two.
pub(crate) fn reduced_points(log_rows: usize, seed: u64) -> (Vec<F192>, Vec<Vec<F192>>) {
    let reduced = reduce(&mut RandomChannel(Rng::new(seed)), log_rows).expect("a nondegenerate challenge");
    (reduced.witness.0, vec![reduced.quotient.0, sum_point(log_rows)])
}

/// The quotient table's two claims in a layout of `2^m` cells: one at a random point but for its two limb
/// coordinates, and one at the fixed point of the sum (the top coefficient of `h`).
fn quotient_points(m: usize, rng: &mut Rng) -> Vec<Vec<F192>> {
    let ([y0, y1], _) = extension();
    let mut generic = rng.ext_vec(m + 4);
    generic.extend([y0, y1]);
    let fixed = [&vec![F192::ONE; m][..], &[F192::ZERO; 4], &[y0, y1]].concat();
    vec![generic, fixed]
}

/// A scaled-down layout with the quotient table's claim shapes (`2^10` cells): lanes of `2^8` entries in pieces
/// of `2^4`, built by the same `Layout::hidden_with` as the real ones: eleven blocks of four of the quotient's
/// chunks, a spill of two pieces and a tail of one, the overflow lane and the seven random lanes, 40 lanes.
fn small_quotient() -> Layout {
    let (m, n) = (10, 1 << 10);
    let chunks = [(0, n), (4, n), (7, 17), (9, 3 * n / 4 + 1)];
    Layout::hidden_with(m + 6, m, m + 4, &chunks, crate::protocol::QUOTIENT_RANDOM_LANES, 4)
}

/// A scaled-down layout with the witness table's claim shape: lanes of `2^8` in pieces of `2^4`, eight blocks
/// and the masks' piece, the overflow lane and the seven random lanes, 40 lanes.
fn small_witness() -> Layout {
    Layout::hidden_with(
        12,
        11,
        14,
        &[(0, 1 << 11), (1, 16)],
        crate::protocol::WITNESS_RANDOM_LANES,
        4,
    )
}

/// The model of the view is the prover's: the lane rounds [`lane_rounds`] gives are the ones a real opening
/// sends, the weight [`Layout::weight_at`] and [`Layout::gadget_at`] read is the prover's, and [`column`] reads
/// the committed codeword.
#[test]
fn model_matches_the_prover() {
    use verifier::{Digest, E, Transcript};
    let mut rng = Rng::new(0x3D);
    let (vars, log_chunk, log_n) = (20, 15, 20);
    let layout = Layout::hidden(vars, log_chunk, log_n, &[(3, 1 << 15), (0, 3000), (9, 1 << 15)], 7);
    let table = opening::Table::hidden(layout.clone(), &[7; 32], |start, out| {
        out.iter_mut()
            .enumerate()
            .for_each(|(k, o)| *o = F64(((start + k) as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x55));
    });
    let committed = opening::commit(&table);
    let claims: Vec<Claim> = (0..2)
        .map(|_| {
            let point = rng.ext_vec(vars);
            Claim {
                value: table.eval(&point),
                point,
            }
        })
        .collect();
    let proof = opening::wire_proof(&opening::open(&table, &committed, &claims));
    assert_eq!(opening::verify(&layout, &committed.root, &claims, &proof), Ok(()));

    // Replay the transcript's lane rounds.
    let iv = opening::iv(&layout, &claims);
    let mut transcript = Transcript::new(&proof, Digest(iv), Digest(opening::PUBLIC_DIGEST), true);
    transcript.next_scalars(2).unwrap();
    let to = |x: E| F192::new(x.c0, x.c1, x.c2);
    let from = |x: F192| E::new(x.c0, x.c1, x.c2);
    let lambdas = powers(to(transcript.sample()), 2);
    let mut claim = from(claims[0].value + lambdas[1] * claims[1].value);
    let mut sent = vec![];
    let mut phi = vec![];
    for _ in 0..LANE_FOLD {
        let poly = transcript.sumcheck_round_poly(3, claim, None).unwrap();
        sent.extend([to(poly[0]), to(poly[2])]);
        let r = transcript.sample();
        phi.push(to(r));
        claim = poly[0] + r * (poly[1] + r * poly[2]);
    }
    let points: Vec<Vec<F192>> = claims.iter().map(|c| c.point.clone()).collect();
    let weight = opening_weight(&layout, &points, &lambdas, &[0, 1, 2]);
    let parts = points.iter().zip(&lambdas).map(|(p, &l)| (&p[..], l));
    assert_eq!(weight, dense(&layout, &layout.weight(parts)), "the prover's tensors");
    let model: Vec<F192> = lane_rounds(&layout, &weight, &phi)
        .iter()
        .map(|form| {
            form.iter()
                .zip(&table.stack)
                .fold(F192::ZERO, |acc, (&c, &t)| acc + c.mul_base(t))
        })
        .collect();
    assert_eq!(model, sent);

    // The pointwise weight is the tensors', and the gadget weighs nothing of the stack.
    let scales = layout.scales(&claims[0].point);
    let dense_one = dense(&layout, &layout.tensors(&claims[0].point, F192::ONE));
    for _ in 0..400 {
        let i = (rng.next_u64() as usize) % layout.placed();
        let (l, y) = (i >> layout.log_lane(), i & ((1 << layout.log_lane()) - 1));
        assert_eq!(layout.weight_at(&claims[0].point, &scales, l, y), dense_one[i]);
    }
    let gadget = opening_weight(&layout, &[], &[], &[0, 1, 2]);
    for (i, &w) in gadget.iter().enumerate() {
        let (l, y) = (i >> layout.log_lane(), i & ((1 << layout.log_lane()) - 1));
        assert_eq!(layout.gadget_at(l, y), w);
    }
    let on_stack = gadget
        .iter()
        .zip(&table.stack)
        .fold(F192::ZERO, |acc, (&w, &t)| acc + w.mul_base(t));
    assert!(on_stack.is_zero(), "the gadget's values cancel it");

    // The codeword: lane `t` of a row is the stack's lane `lanes - 1 - t`.
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let (_, data) = pcs::whir::commit(&table.stack, log_n, LANE_FOLD, LOG_INV_RATE);
    for position in [0, 1, 777, (2 << log_lane) - 1] {
        let col = column(log_lane, position);
        for t in 0..lanes {
            let l = lanes - 1 - t;
            let lane = &table.stack[l << log_lane..(l + 1) << log_lane];
            let value = lane.iter().zip(&col).fold(F64::ZERO, |acc, (&a, &b)| acc + a * b);
            assert_eq!(data.codeword[position * lanes + t], value);
        }
    }
}

/// The exact test, on scaled-down layouts with both tables' claim shapes: the opening's view up to its first fold
/// is distributed independently of the table given the claims, and an unopened row keeps every random entry but
/// the three the fold pins, also with as many opened positions as the first piece has entries below the gadget
/// (the bound of condition (Q)). Without the gadget the rounds show the table.
#[test]
fn openings_hide_the_tables() {
    let mut rng = Rng::new(0x41D);
    let free = (1 << 4) - GADGET;
    let quotient = (small_quotient(), quotient_points(10, &mut rng));
    let witness = (small_witness(), vec![rng.ext_vec(12)]);
    for (layout, points) in [quotient, witness] {
        for queries in [3, free] {
            let [view, claims, whole, unopened] = view_ranks(&layout, &points, queries, &[0, 1, 2], &mut rng);
            assert_eq!(
                (whole - view - claims, unopened),
                (0, layout.lanes() - 3),
                "{queries} queries"
            );
        }
        assert!(leak(&layout, &points, 3, &[], &mut rng) > 0, "without the gadget");
    }
}

/// Condition (R) predicts the exact test: on the scaled-down layouts, with the gadget or parts of it, the view
/// reveals nothing when the randomness reaches the rounds' 33 dimensions, and otherwise something, at most the
/// dimensions it does not reach. Through the gadget's entries alone, all three patterns reach the 33 (the
/// argument of HIDING.md, for every challenge outside a tiny set), two reach 30; at random challenges the data
/// entries' twisted moves make up the rest with one lower pattern.
#[test]
fn round_freedom_predicts_the_exact_test() {
    let mut rng = Rng::new(0x41F);
    let quotient = (small_quotient(), quotient_points(10, &mut rng));
    let witness = (small_witness(), vec![rng.ext_vec(12)]);
    for (layout, points) in [quotient, witness] {
        let entries: Vec<usize> = (0..1 << layout.log_lane()).collect();
        for patterns in [&[0, 1, 2][..], &[0, 2], &[0, 1], &[1, 2], &[0], &[2], &[]] {
            let phi = rng.ext_vec(LANE_FOLD);
            let lambdas = powers(rng.ext(), points.len());
            let freedom = round_freedom(&layout, &points, &lambdas, patterns, &phi, &entries);
            let gadget = round_freedom(&layout, &[], &[], patterns, &phi, &gadget_entries(&layout));
            let leak = leak(&layout, &points, 3, patterns, &mut rng);
            assert_eq!(
                leak == 0,
                freedom == 33,
                "patterns {patterns:?}: leak {leak}, freedom {freedom}"
            );
            assert!(
                leak <= 33 - freedom,
                "patterns {patterns:?}: leak {leak}, freedom {freedom}"
            );
            // Through the gadget alone: 33 with the three patterns, 30 with two, 27 with a lower one, 9 with the
            // upper one.
            let expected = match patterns {
                [_, _, _] => 33,
                [_, _] => 30,
                [2] => 9,
                [_] => 27,
                _ => 0,
            };
            assert_eq!(gadget, expected, "patterns {patterns:?}");
        }
    }
}

/// Condition (R) and (S) on the real layouts, at the toy's size and the benchmark's: through the gadget's entries
/// alone (which do not depend on the claims) the randomness reaches all 33 dimensions of the lane rounds, and with
/// the reduction's own claims through data entries too; the random lanes' fold weights span `E`. Without the
/// gadget the data entries' randomness does not reach round 0's value at 0.
#[test]
fn rounds_are_free_at_full_size() {
    use crate::circuit::LOG_ROWS;
    use crate::protocol::{quotient_layout, witness_layout};
    let mut rng = Rng::new(0xF3EE);
    for log_rows in [17, LOG_ROWS] {
        for seed in 0..3 {
            let (witness, quotient) = reduced_points(log_rows, seed);
            let phi = rng.ext_vec(LANE_FOLD);
            let lambdas = powers(rng.ext(), 2);
            for (layout, points) in [
                (witness_layout(log_rows), vec![witness.clone()]),
                (quotient_layout(log_rows), quotient.clone()),
            ] {
                let lambdas = &lambdas[..points.len()];
                assert_eq!((gadget_freedom(&layout, &phi), fold_span(&layout, &phi)), (33, 3));
                let data = data_entries(&layout, 200, &mut rng);
                let all: Vec<usize> = gadget_entries(&layout)
                    .into_iter()
                    .chain(data.iter().copied())
                    .collect();
                assert_eq!(round_freedom(&layout, &points, lambdas, &[0, 1, 2], &phi, &all), 33);
                assert!(round_freedom(&layout, &points, lambdas, &[], &phi, &data) <= 30);
            }
        }
    }
}

/// Gaussian elimination over `E`: the rank of `rows`.
fn e_rank(mut rows: Vec<Vec<F192>>) -> usize {
    let cols = rows.first().map_or(0, |r| r.len());
    let mut r = 0;
    for c in 0..cols {
        let Some(p) = (r..rows.len()).find(|&i| !rows[i][c].is_zero()) else {
            continue;
        };
        rows.swap(r, p);
        let inverse = rows[r][c].inv();
        let pivot: Vec<F192> = rows[r].iter().map(|&x| x * inverse).collect();
        for row in rows.iter_mut().skip(r + 1) {
            let f = row[c];
            if !f.is_zero() {
                row.iter_mut().zip(&pivot).for_each(|(a, &b)| *a += f * b);
            }
        }
        r += 1;
    }
    r
}

/// The running claim after the first `rounds` lane rounds of values `values`, from a zero claim.
fn running_claim(values: &[F192], phi: &[F192], rounds: usize) -> F192 {
    (0..rounds).fold(F192::ZERO, |claim, j| {
        let (at_zero, quadratic) = (values[2 * j], values[2 * j + 1]);
        at_zero + (claim + quadratic) * phi[j] + quadratic * phi[j] * phi[j]
    })
}

/// The gadget's pattern `g` as a weight on the 64 lane indices, and the moves of its half that keep the claims
/// (a unit table on each lane of the half but the pattern's, and the pattern's pair as one, or none for the
/// overflow lane, which holds zero), over the lanes `0..lanes`.
fn pattern_moves(g: usize, lanes: usize) -> (Vec<F192>, Vec<Vec<F192>>) {
    let pattern = gadget_lanes(g);
    let mut w = vec![F192::ZERO; 1 << LANE_FOLD];
    pattern.iter().for_each(|&l| w[l] = F192::ONE);
    let upper = pattern[0] >= 32;
    let mut moves: Vec<Vec<F192>> = (0..lanes)
        .filter(|&r| (r >= 32) == upper && !pattern.contains(&r))
        .map(|r| {
            let mut t = vec![F192::ZERO; 1 << LANE_FOLD];
            t[r] = F192::ONE;
            t
        })
        .collect();
    if pattern.len() == 2 {
        let mut t = vec![F192::ZERO; 1 << LANE_FOLD];
        pattern.iter().for_each(|&l| t[l] = F192::ONE);
        moves.push(t);
    }
    (w, moves)
}

/// `φ` in families outside the bad set `B` of HIDING.md (no coordinate in `{0, 1}`, at most one of `φ_0, φ_1, φ_2`
/// in `K`), chosen against the argument: coordinates in `K`, equal, complementary, and the last fold at the
/// root of a pair's line (where a single lower pattern would fail).
fn adversarial_challenges(rng: &mut Rng) -> Vec<Vec<F192>> {
    let k = |rng: &mut Rng| F192::from(F64(rng.next_u64() | 2));
    let mut out = vec![];
    for _ in 0..4 {
        out.push(rng.ext_vec(LANE_FOLD));
        // All but φ_0 and φ_1 in K; all but φ_1 and φ_2; all but φ_0 and φ_2.
        for free in [[0, 1], [1, 2], [0, 2]] {
            out.push(
                (0..LANE_FOLD)
                    .map(|i| if free.contains(&i) { rng.ext() } else { k(rng) })
                    .collect(),
            );
        }
        let x = rng.ext();
        out.push(vec![x; LANE_FOLD]);
        out.push(
            (0..LANE_FOLD)
                .map(|i| if i % 2 == 0 { x } else { F192::ONE + x })
                .collect(),
        );
        let mut phi = rng.ext_vec(LANE_FOLD);
        let p = (0..4).fold(F192::ONE, |acc, i| acc * (F192::ONE + phi[i]));
        let q = (0..4).fold(F192::ONE, |acc, i| acc * phi[i]);
        phi[4] = p * (p + q).inv();
        out.push(phi);
    }
    out
}

/// HIDING.md's argument that (R) holds for every challenge outside `B = {some φ_i ∈ {0, 1}} ∪ {two of φ_0, φ_1,
/// φ_2 in K}` (probability below `2^-188`), checked part by part on both real layouts:
/// 1. at every lane pair, whatever `φ`: a lane of one half meets one of the other half in `h_5`'s quadratic
///    coefficient only (the solvers' moves are along it);
/// 2. the E-linear core, exactly, at adversarial `φ`: each lower pair's moves reach the rounds 0 to 4 in 9
///    dimensions with `h_5(0)` the running claim, the upper lane's in a direction where `h_5(0) = 0` and the
///    running claim is not, and all of them 11 dimensions once `h_5`'s quadratic coefficient is forgotten;
/// 3. the whole condition, the exact K-span through the gadget's entries with the twisted solvers: 33, and (S);
/// 4. at `φ ∈ B` the argument's hypotheses fail: with two of `φ_0, φ_1, φ_2` in `K`, (S).
#[test]
fn rounds_are_free_for_every_challenge() {
    use crate::protocol::{quotient_layout, witness_layout};
    let mut rng = Rng::new(0xA11);
    // 1. Pairing across the halves: `pairing(l, r)` is nonzero only where `l` and `r` agree above bit `j`.
    for l in 0..64usize {
        for r in 0..64usize {
            if (l < 32) != (r < 32) {
                assert!((0..LANE_FOLD - 1).all(|j| l >> (j + 1) != r >> (j + 1)));
            }
        }
    }
    for layout in [
        witness_layout(17),
        quotient_layout(17),
        quotient_layout(crate::circuit::LOG_ROWS),
    ] {
        let lanes = layout.lanes();
        for phi in adversarial_challenges(&mut rng) {
            assert!(phi.iter().all(|&x| x != F192::ZERO && x != F192::ONE));
            // 1, at this φ: the other half's lanes move h_5's quadratic coefficient alone.
            for g in 0..3 {
                let (w, _) = pattern_moves(g, lanes);
                for r in (0..lanes).filter(|&r| (r >= 32) != (gadget_lanes(g)[0] >= 32)) {
                    let mut t = vec![F192::ZERO; 1 << LANE_FOLD];
                    t[r] = F192::ONE;
                    assert!(rounds_at(&w, &t, &phi)[..11].iter().all(|x| x.is_zero()));
                }
            }
            // 2. The E-linear core.
            let mut all = vec![];
            for g in 0..3 {
                let (w, moves) = pattern_moves(g, lanes);
                let values: Vec<[F192; 12]> = moves.iter().map(|t| rounds_at(&w, t, &phi)).collect();
                for v in &values {
                    let h5 = if g < 2 { running_claim(v, &phi, 5) } else { F192::ZERO };
                    assert_eq!(v[10], h5, "h_5(0) of pattern {g}");
                }
                if g < 2 {
                    assert_eq!(e_rank(values.iter().map(|v| v[..10].to_vec()).collect()), 9);
                } else {
                    assert!(values.iter().any(|v| !running_claim(v, &phi, 5).is_zero()));
                }
                all.extend(values.iter().map(|v| v[..11].to_vec()));
            }
            assert_eq!(e_rank(all), 11);
            // 3. The condition itself.
            assert_eq!((gadget_freedom(&layout, &phi), fold_span(&layout, &phi)), (33, 3));
        }
        // 4. Two of φ_0, φ_1, φ_2 in K: the random lanes' fold weights no longer span E.
        let mut phi = rng.ext_vec(LANE_FOLD);
        phi[0] = F192::from(F64(rng.next_u64() | 2));
        phi[2] = F192::from(F64(rng.next_u64() | 2));
        assert!(fold_span(&layout, &phi) < 3);
    }
}

/// A toy circuit with one input bit the statement does not depend on: two witnesses of one statement.
pub(crate) fn two_witnesses() -> (
    crate::circuit::Circuit,
    impl Fn(bool) -> Vec<bool>,
    crate::statement::Statement,
) {
    use crate::circuit::{Builder, Src, public_words};
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let _dummy = b.input();
    let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
    let circuit = b.finish(17, &public_words(&x, &digest));
    let mut rng = Rng::new(0x2C);
    let xb: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let statement = crate::statement::Statement {
        y: xb,
        root: crate::statement::pair(&xb, &xb),
    };
    let inputs = move |dummy: bool| -> Vec<bool> {
        let mut v: Vec<bool> = (0..256).map(|i| (xb[i / 8] >> (i % 8)) & 1 == 1).collect();
        v.push(dummy);
        v
    };
    (circuit, inputs, statement)
}

/// The witness table a verifier who guesses the cells, the masks and the padding's seed would commit.
pub(crate) fn guessed_witness(
    circuit: &crate::circuit::Circuit,
    cells: &[F64],
    mask: &[F64; 16],
    seed: &[u8; 32],
) -> opening::Table {
    let n = cells.len();
    let mut w_hat = cells.to_vec();
    crate::domain::coefficients(&mut w_hat, F64::ZERO);
    let layout = crate::protocol::witness_layout(circuit.log_rows);
    opening::Table::hidden(layout, seed, |start, out| {
        for (i, o) in (start..).zip(out.iter_mut()) {
            *o = if i < n {
                w_hat[i]
            } else {
                mask.get(i - n).copied().unwrap_or(F64::ZERO)
            };
        }
    })
}

/// The review's calldata-only distinguisher, turned around: for a candidate witness the four `a_j` still pin
/// the twelve mask coefficients, but the witness table's root also commits to its padding, so recomputing it
/// confirms neither candidate; and the same cells and masks under another seed commit to another root.
///
/// **What this does not show.** The verifier's guess at the padding is one seed, `[0; 32]`, so the test passes for
/// any design whose padding is secret: it shows that the root commits to the padding, not that the root hides the
/// witness. It also checks that with the prover's own padding the root confirms the true candidate and only it:
/// the verdict rests on the padding's secrecy alone. The evidence that the roots and openings are independent of
/// the witness is HIDING.md's argument, run on the real prover by `review_hiding.rs`'s translation tests
/// (`translation_holds_on_real_openings`, `translation_holds_at_the_benchmark_size`), and [`openings_hide_the_tables`].
#[test]
fn calldata_alone_does_not_confirm_a_witness() {
    use crate::protocol::{Index, Randomness, label, prove_with_randomness, table_seed};
    use crate::transcript::{ProverChain, scalars_root};
    let (circuit, inputs, statement) = two_witnesses();
    let index = Index::new(&circuit);
    let index_committed = opening::commit(&index.table);
    let mut rng = Rng::new(0x5D);
    for trial in 0..2 {
        let secret = trial % 2 == 1;
        let masks: [[F64; 3]; 4] = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
        let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        let cells = circuit.cells(&inputs(secret));
        let prove = |padding: [u8; 32]| {
            let randomness = Randomness { masks, padding };
            prove_with_randomness(&circuit, &index, &index_committed.root, &statement, &cells, &randomness).proof
        };
        let proof = prove(seed);
        // Only the proof's nine scalars from here on.
        let s = &proof.stream;
        let root1 = scalars_root(&[s[0], s[1]]).unwrap();
        let mut chain = ProverChain::new(&label(&index_committed.root, &statement));
        chain.send(s[0]);
        chain.send(s[1]);
        let _ = [(); 3].map(|_| chain.sample());
        chain.send(s[2]);
        chain.send(s[3]);
        let t = chain.sample();
        let m = circuit.log_rows + 2;
        let digits: Vec<F192> = std::iter::successors(Some(t), |&w| Some(w * w + w))
            .take(m + 1)
            .collect();
        let (w2, w3, wm) = (digits[2], digits[3], digits[m]);
        let (mut verdict, mut knowing_the_padding) = (vec![], vec![]);
        for hypothesis in [false, true] {
            let candidate = circuit.cells(&inputs(hypothesis));
            let mut w_hat = candidate.clone();
            crate::domain::coefficients(&mut w_hat, F64::ZERO);
            let mut mask = [F64::ZERO; 16];
            for j in 0..4 {
                let v = (s[4 + j] + crate::domain::evaluate(&w_hat, j, 4, &digits[2..m])) * wm.inv();
                // m0 + m1 w2 + m2 w3 = v over GF(2^64): three K-equations in three unknowns.
                let rows: Vec<Vec<F64>> = (0..3)
                    .map(|c| [F192::ONE, w2, w3, v].iter().map(|&e| coords(e)[c]).collect())
                    .collect();
                let solution = kernel(&rows, 4);
                assert_eq!(solution.len(), 1, "the a_j pin the masks");
                let scale = solution[0][3].inv();
                for i in 0..3 {
                    mask[4 * i + j] = solution[0][i] * scale;
                }
            }
            if hypothesis == secret {
                let truth: Vec<F64> = (0..12).map(|k| masks[k % 4][k / 4]).collect();
                assert_eq!(mask[..12].to_vec(), truth, "the true candidate's masks are pinned");
            }
            // The verifier's best guess at the padding: any seed. The root commits to the real one.
            let table = guessed_witness(&circuit, &candidate, &mask, &[0; 32]);
            verdict.push(opening::commit(&table).root == root1);
            let known = guessed_witness(&circuit, &candidate, &mask, &table_seed(&seed, b"witness"));
            knowing_the_padding.push(opening::commit(&known).root == root1);
        }
        assert_eq!(verdict, [false, false], "trial {trial}");
        assert_eq!(
            knowing_the_padding,
            [!secret, secret],
            "trial {trial}: the padding alone hides"
        );

        let again: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        let other = prove(again);
        assert_ne!(other.stream[..2], proof.stream[..2], "the root commits to the padding");
    }
}

/// The review's opening distinguisher, turned around: the witness table's opened rows match no row a candidate
/// witness commits to, whichever candidate; and they say nothing of the masks, for at the opened positions the
/// overflow lane's random first piece alone reaches every value, so the masks' contributions lie in its span.
///
/// **What this does not show.** The candidates are committed with one guessed padding seed, `[0; 32]`, so the
/// first half passes for any design whose padding is secret; with the prover's own padding, every opened row is a
/// row of the true candidate's commitment and not every one is of the other's (checked): the verdict rests on the
/// padding's secrecy alone. The second half (the masks in the first piece's span) is a property of the layout. The evidence
/// that the openings are independent of the witness is `review_hiding.rs`'s translation tests
/// (`translation_holds_on_real_openings`, `translation_holds_at_the_benchmark_size`) and [`openings_hide_the_tables`].
#[test]
fn opened_rows_do_not_identify_the_witness() {
    use crate::protocol::{Index, Randomness, open, prove_with_randomness, table_seed, witness_layout};
    use std::collections::HashSet;
    let (circuit, inputs, statement) = two_witnesses();
    let index = Index::new(&circuit);
    let index_committed = opening::commit(&index.table);
    let mut rng = Rng::new(0x2D);
    let secret = rng.next_u64() & 1 == 1;
    let masks: [[F64; 3]; 4] = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let cells = circuit.cells(&inputs(secret));
    let randomness = Randomness { masks, padding: seed };
    let proved = prove_with_randomness(&circuit, &index, &index_committed.root, &statement, &cells, &randomness);
    let layout = witness_layout(circuit.log_rows);
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let honest = pcs::whir::commit(&proved.tables.witness.stack, layout.log_n, LANE_FOLD, LOG_INV_RATE).1;
    let openings = open(proved.tables, &proved.claims, &index, &index_committed);
    let rows: Vec<Vec<u64>> = openings.witness.merkle[0]
        .leaf_data
        .iter()
        .map(|row| row.iter().map(|w| w.0).collect())
        .collect();
    assert_eq!(rows[0].len(), lanes);

    // The review's distinguisher: commit each candidate, with the masks and any padding, and look the opened rows
    // up among its rows.
    let mut mask = [F64::ZERO; 16];
    for (j, coeffs) in masks.iter().enumerate() {
        for (i, &c) in coeffs.iter().enumerate() {
            mask[4 * i + j] = c;
        }
    }
    let found = |hypothesis: bool, padding: &[u8; 32]| {
        let table = guessed_witness(&circuit, &circuit.cells(&inputs(hypothesis)), &mask, padding);
        let (_, data) = pcs::whir::commit(&table.stack, layout.log_n, LANE_FOLD, LOG_INV_RATE);
        let candidate: HashSet<Vec<u64>> = data
            .codeword
            .chunks_exact(lanes)
            .map(|r| r.iter().map(|w| w.0).collect())
            .collect();
        rows.iter().filter(|r| candidate.contains(*r)).count()
    };
    for hypothesis in [false, true] {
        assert_eq!(found(hypothesis, &[0; 32]), 0, "dummy = {hypothesis}");
        // With the prover's padding: every opened row for the true candidate, not all of them for the other (the
        // two witnesses differ in a few cells, so some rows agree).
        let known = found(hypothesis, &table_seed(&seed, b"witness"));
        assert_eq!(
            known == rows.len(),
            hypothesis == secret,
            "dummy = {hypothesis}, the prover's padding: {known} of {} rows",
            rows.len()
        );
    }

    // Where the rows were opened (the prover's knowledge), and the overflow lane's codeword there as forms in its
    // entries: its first piece (random) alone has full rank, so the masks' piece adds none.
    let opened: Vec<usize> = rows
        .iter()
        .map(|r| {
            honest
                .codeword
                .chunks_exact(lanes)
                .position(|row| row.iter().map(|w| w.0).eq(r.iter().copied()))
                .expect("an honest row")
        })
        .collect();
    let s = layout.log_piece().unwrap();
    let mask_piece = layout
        .pieces()
        .iter()
        .position(|&p| p == (1 << (circuit.log_rows + 2)) >> s)
        .unwrap()
        + 1;
    // The overflow lane's first piece is random below the gadget (at the gadget's last pattern it is zero).
    let free = (1 << s) - opening::GADGET;
    let first: Vec<Vec<F64>> = opened.iter().map(|&x| column(log_lane, x)[..free].to_vec()).collect();
    let with_masks: Vec<Vec<F64>> = opened
        .iter()
        .map(|&x| {
            let col = column(log_lane, x);
            [&col[..free], &col[mask_piece << s..(mask_piece << s) + 16]].concat()
        })
        .collect();
    assert_eq!(rank(first), opened.len());
    assert_eq!(rank(with_masks), opened.len());
    println!(
        "{} distinct positions opened: the first piece's columns have rank {0}",
        opened.len()
    );
}
