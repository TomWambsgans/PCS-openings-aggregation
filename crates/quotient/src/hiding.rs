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
//! one condition of `HIDING.md`'s argument that depends on the challenges and the claims (condition (R)).

use primitives::field::{F64, F192, powers};
use primitives::test_rng::Rng;

use crate::opening::{self, Claim, LANE_FOLD, LOG_INV_RATE, Lane, Layout};
use crate::protocol::{Channel, Q_SPILL, extension, quotient_chunks, reduce, sum_point};
use crate::transcript::TranscriptError;

/// The `K` coordinates of an `E` value.
fn coords(x: F192) -> [F64; 3] {
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
fn rank(rows: impl IntoIterator<Item = Vec<F64>>) -> usize {
    let mut span = Span::new();
    rows.into_iter().for_each(|row| {
        span.insert(row);
    });
    span.rank()
}

/// A basis of the kernel of the `K`-matrix `m` (`n` columns).
fn kernel(m: &[Vec<F64>], n: usize) -> Vec<Vec<F64>> {
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
fn column(log_lane: usize, position: usize) -> Vec<F64> {
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
fn fold_weight(phi: &[F192], l: usize) -> F192 {
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

/// The combined weight of claims at `points` on the stack, written out: what the prover's lane tensors stand
/// for.
fn dense_weight(layout: &Layout, points: &[Vec<F192>], lambdas: &[F192]) -> Vec<F192> {
    let lane = 1usize << layout.log_lane();
    let mut weight = vec![F192::ZERO; layout.placed()];
    for (p, &lambda) in points.iter().zip(lambdas) {
        for tensor in layout.tensors(p, lambda) {
            for (l, &scale) in tensor.scales.iter().enumerate() {
                if !scale.is_zero() {
                    let out = &mut weight[l * lane..(l + 1) * lane];
                    out.iter_mut().zip(&tensor.low).for_each(|(o, &e)| *o += scale * e);
                }
            }
        }
    }
    weight
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

/// Whether the round values `values` (twelve) leave the last round's value at its challenge unchanged: what
/// every change that keeps the claims and `f¹` must do (`h_5(φ_5) = Σ W̃(·, φ)·f¹`).
fn keeps_last_claim(values: &[F192], phi: &[F192]) -> bool {
    let mut claim = F192::ZERO;
    for j in 0..LANE_FOLD {
        let (at_zero, quadratic) = (values[2 * j], values[2 * j + 1]);
        claim = at_zero + (claim + quadratic) * phi[j] + quadratic * phi[j] * phi[j];
    }
    claim.is_zero()
}

/// Whether stack entry `index` is a random unknown (the share lane's held pieces are: the overflow lane's
/// entries there are the table's plus them).
fn is_random(layout: &Layout, index: usize) -> bool {
    let s = layout.log_piece().expect("a hidden layout");
    let (l, y) = (index >> layout.log_lane(), index & ((1 << layout.log_lane()) - 1));
    y < 1 << s
        || match layout.lane(l) {
            Lane::Random => true,
            Lane::Overflow => y >> s > layout.pieces().len(),
            Lane::Block(_) => false,
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

/// What an opening's view up to its first fold shows of a hidden table, for claims at `points` and `queries`
/// opened positions, at random challenges: `(rank M_R, rank C, rank [[M_R, M_D], [0, C]])`, and the K-dimension
/// of one more, unopened, row's randomness beyond the view (the entropy the Merkle siblings rest on).
fn view_ranks(layout: &Layout, points: &[Vec<F192>], queries: usize, rng: &mut Rng) -> [usize; 4] {
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let lane = 1usize << log_lane;
    let placed = layout.placed();
    let weight = dense_weight(layout, points, &powers(rng.ext(), points.len()));
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
    // The claims, on the stack's entries.
    let mut claim_rows = vec![];
    for p in points {
        push_e(
            &mut claim_rows,
            &dense_weight(layout, std::slice::from_ref(p), &[F192::ONE]),
        );
    }

    // The unknowns: an entry of the table, or a random one. Every stack entry is one of them, but the overflow
    // lane's held pieces, which are the table's entries plus the share lane's (random) ones at the same place.
    let random: Vec<usize> = (0..placed).filter(|&i| is_random(layout, i)).collect();
    let data: Vec<usize> = (0..placed).filter(|&i| !is_random(layout, i)).collect();
    let overflow = layout.overflow().expect("an overflow lane");
    let share = layout.share().expect("a share lane");
    let s = layout.log_piece().expect("a hidden layout");
    let held = layout.pieces().len();
    let coupled = |i: usize| -> Option<usize> {
        let (l, y) = (i >> log_lane, i & (lane - 1));
        (l == share && (1..=held).contains(&(y >> s))).then_some(overflow * lane + y)
    };
    let on_random = |row: &[F64]| -> Vec<F64> {
        random
            .iter()
            .map(|&i| row[i] + coupled(i).map_or(F64::ZERO, |j| row[j]))
            .collect()
    };
    let on_data = |row: &[F64]| -> Vec<F64> { data.iter().map(|&i| row[i]).collect() };
    for row in &claim_rows {
        assert!(
            on_random(row).iter().all(|x| x.is_zero()),
            "the claims weigh no randomness"
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
fn leak(layout: &Layout, points: &[Vec<F192>], queries: usize, rng: &mut Rng) -> usize {
    let [view_random, claims, whole, _] = view_ranks(layout, points, queries, rng);
    whole - view_random - claims
}

/// The random unknowns at in-lane entry `y` past the first piece, each as the lanes whose entry `y` it is part
/// of: every random lane's own entry (the share lane's at a held piece being part of the overflow lane's too),
/// and the overflow lane's where it holds none of the table.
fn random_at(layout: &Layout, y: usize) -> Vec<Vec<usize>> {
    let s = layout.log_piece().expect("a hidden layout");
    let overflow = layout.overflow().expect("an overflow lane");
    let held = (1..=layout.pieces().len()).contains(&(y >> s));
    let mut out = vec![];
    for l in 0..layout.lanes() {
        match layout.lane(l) {
            Lane::Random if layout.share() == Some(l) && held => out.push(vec![l, overflow]),
            Lane::Random => out.push(vec![l]),
            Lane::Overflow if !held => out.push(vec![l]),
            _ => {}
        }
    }
    out
}

/// Condition (R) of `HIDING.md`: the span the randomness gives the twelve lane-round values once `f¹` is pinned.
/// At an entry `y` past the first piece, the random unknowns there ([`random_at`]) leave `f¹(y)` alone along
/// the kernel of their fold weights, `ker_y = {k : Σ_u k_u·Σ_{r ∈ u} eq(φ, r) = 0}`, and move the rounds by
/// `Σ_l W_l(y)·Σ_u k_u·Σ_{r ∈ u} pairing(l, r)`, with `W_l(y)` the combined weight at entry `y` of lane `l`.
/// The span over all such `y` and `k` lies in the 33 dimensions that keep the last claim (asserted); this returns
/// its K-dimension over `samples` entries where the overflow lane holds the table and as many where it does
/// not (all of them if fewer), exact once it reaches 33, and condition (S): the K-dimension of the fold weights
/// of the random lanes but the share, which are random at every entry (3 when they span `E`).
fn round_freedom(
    layout: &Layout,
    points: &[Vec<F192>],
    lambdas: &[F192],
    phi: &[F192],
    samples: usize,
    rng: &mut Rng,
) -> (usize, usize) {
    let lanes = layout.lanes();
    let (log_lane, s) = (layout.log_lane(), layout.log_piece().expect("a hidden layout"));
    let span_random = rank(
        (0..lanes)
            .filter(|&l| layout.lane(l) == Lane::Random && layout.share() != Some(l))
            .map(|r| coords(fold_weight(phi, r)).to_vec()),
    );
    let scales: Vec<_> = points.iter().map(|p| layout.scales(p)).collect();
    let held = layout.pieces().len();
    let mut chosen = vec![];
    for holds in [true, false] {
        let entries: Vec<usize> = (1 << s..1 << log_lane)
            .filter(|&y| ((y >> s) <= held) == holds)
            .collect();
        if entries.len() <= samples {
            chosen.extend(entries);
        } else {
            chosen.extend((0..samples).map(|_| entries[(rng.next_u64() as usize) % entries.len()]));
        }
    }
    let mut freedom = Span::new();
    for y in chosen {
        let unknowns = random_at(layout, y);
        let folds: Vec<F192> = unknowns
            .iter()
            .map(|u| u.iter().fold(F192::ZERO, |acc, &r| acc + fold_weight(phi, r)))
            .collect();
        let m: Vec<Vec<F64>> = (0..3).map(|c| folds.iter().map(|&f| coords(f)[c]).collect()).collect();
        let weights: Vec<F192> = (0..lanes)
            .map(|l| {
                points
                    .iter()
                    .zip(&scales)
                    .zip(lambdas)
                    .fold(F192::ZERO, |acc, ((p, sc), &lambda)| {
                        acc + lambda * layout.weight_at(p, sc, l, y)
                    })
            })
            .collect();
        // What one unit of each unknown moves the rounds by.
        let moves: Vec<[F192; 12]> = unknowns
            .iter()
            .map(|u| {
                let mut total = [F192::ZERO; 12];
                for (l, &w) in weights.iter().enumerate() {
                    if w.is_zero() {
                        continue;
                    }
                    for &r in u {
                        total.iter_mut().zip(pairing(phi, l, r)).for_each(|(o, x)| *o += w * x);
                    }
                }
                total
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
    (freedom.rank(), span_random)
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
fn reduced_points(log_rows: usize, seed: u64) -> (Vec<F192>, Vec<Vec<F192>>) {
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

/// A scaled-down quotient layout (`2^m` cells, pieces of `2^log_piece`): the same `55` blocks, overflow lane,
/// share and spread random lanes as the real one, from the same code, with spills of two pieces and one.
fn small_quotient(m: usize, log_piece: usize, random: usize) -> Layout {
    let spill = (1 << log_piece) + 1;
    Layout::hidden_with(m + 6, m, m + 4, &quotient_chunks(m, spill, 1), random, log_piece)
}

/// A scaled-down witness layout: `32` blocks, the masks' piece, the overflow lane, the share and the random lanes.
fn small_witness(m: usize, log_piece: usize, random: usize) -> Layout {
    Layout::hidden_with(m + 1, m, m + 1, &[(0, 1 << m), (1, 1 << log_piece)], random, log_piece)
}

/// The full-size hidden layouts with `witness` and `quotient` random lanes.
fn full_layouts(log_rows: usize, witness: usize, quotient: usize) -> (Layout, Layout) {
    let m = log_rows + 2;
    (
        Layout::hidden(m + 1, m, m + 1, &[(0, 1 << m), (1, 16)], witness),
        Layout::hidden(m + 6, m, m + 4, &quotient_chunks(m, Q_SPILL, 64), quotient),
    )
}

/// The model of the view is the prover's: the lane rounds [`lane_rounds`] gives are the ones a real opening
/// sends, the weight [`Layout::weight_at`] reads is the prover's, and [`column`] reads the committed codeword.
#[test]
fn model_matches_the_prover() {
    use verifier::{Digest, E, Transcript};
    let mut rng = Rng::new(0x3D);
    let (vars, log_chunk, log_n) = (20, 15, 20);
    let layout = Layout::hidden(vars, log_chunk, log_n, &[(3, 1 << 15), (0, 3000), (9, 1 << 15)], 5);
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
    let (iv, statement) = opening::seed(&committed.root, &claims);
    let mut transcript = Transcript::new(&proof, Digest(iv), Digest(statement), true);
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
    let weight = dense_weight(&layout, &points, &lambdas);
    let model: Vec<F192> = lane_rounds(&layout, &weight, &phi)
        .iter()
        .map(|form| {
            form.iter()
                .zip(&table.stack)
                .fold(F192::ZERO, |acc, (&c, &t)| acc + c.mul_base(t))
        })
        .collect();
    assert_eq!(model, sent);

    // The pointwise weight is the tensors'.
    let scales = layout.scales(&claims[0].point);
    let dense = dense_weight(&layout, &points[..1], &[F192::ONE]);
    for _ in 0..400 {
        let i = (rng.next_u64() as usize) % layout.placed();
        let (l, y) = (i >> layout.log_lane(), i & ((1 << layout.log_lane()) - 1));
        assert_eq!(layout.weight_at(&claims[0].point, &scales, l, y), dense[i]);
    }

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

/// The exact test, on scaled-down copies of both hidden layouts with the production number of random lanes:
/// the opening's view up to its first fold is distributed independently of the table given the claims, with
/// as many opened positions as a first piece has entries but one, and an unopened row keeps every random entry
/// but the three the fold pins. With one random lane fewer the rounds show the table.
#[test]
fn openings_hide_the_tables() {
    use crate::protocol::{QUOTIENT_RANDOM_LANES, WITNESS_RANDOM_LANES};
    let mut rng = Rng::new(0x41D);
    // The quotient table: two claims, 55 blocks, lanes of 2^9 entries in pieces of 4, three positions opened.
    let layout = small_quotient(11, 2, QUOTIENT_RANDOM_LANES);
    let points = quotient_points(11, &mut rng);
    let [view, claims, whole, unopened] = view_ranks(&layout, &points, 3, &mut rng);
    assert_eq!((whole - view - claims, unopened), (0, layout.lanes() - 3));
    assert!(leak(&small_quotient(11, 2, QUOTIENT_RANDOM_LANES - 1), &points, 3, &mut rng) > 0);

    // The witness table: one claim, 32 blocks, lanes of 2^8 entries in pieces of 4, three positions opened.
    let layout = small_witness(13, 2, WITNESS_RANDOM_LANES);
    let point = vec![rng.ext_vec(14)];
    let [view, claims, whole, unopened] = view_ranks(&layout, &point, 3, &mut rng);
    assert_eq!((whole - view - claims, unopened), (0, layout.lanes() - 3));
    assert!(leak(&small_witness(13, 2, WITNESS_RANDOM_LANES - 1), &point, 3, &mut rng) > 0);
    // As many opened positions as a first piece has entries: the view still hides the table, but an unopened
    // row has nothing left past what the fold and its own codeword pin.
    let [view, claims, whole, unopened] = view_ranks(&layout, &point, 4, &mut rng);
    assert_eq!(whole - view - claims, 0);
    assert!(unopened < layout.lanes() - 3, "{unopened}");
}

/// Condition (R) predicts the exact test: on scaled-down layouts, what the view reveals is the 33 dimensions of
/// the rounds the randomness cannot reach.
#[test]
fn round_freedom_predicts_the_exact_test() {
    let mut rng = Rng::new(0x41F);
    for random in [4, 6, 7] {
        let points = quotient_points(11, &mut rng);
        let point = vec![rng.ext_vec(14)];
        let phi = rng.ext_vec(LANE_FOLD);
        let lambdas = powers(rng.ext(), 2);
        let layout = small_quotient(11, 2, random);
        let (freedom, _) = round_freedom(&layout, &points, &lambdas, &phi, 1 << 12, &mut rng);
        assert_eq!(
            leak(&layout, &points, 3, &mut rng),
            33 - freedom,
            "quotient, {random} random lanes"
        );
        let layout = small_witness(13, 2, random);
        let (freedom, _) = round_freedom(&layout, &point, &lambdas[..1], &phi, 1 << 12, &mut rng);
        assert_eq!(
            leak(&layout, &point, 3, &mut rng),
            33 - freedom,
            "witness, {random} random lanes"
        );
    }
}

/// Condition (R) on the real layouts, at the toy's size and the benchmark's, at the reduction's own claim
/// points: the randomness reaches all 33 dimensions of the lane rounds and the random lanes' fold weights span
/// `E`; with one random lane fewer it does not.
#[test]
fn rounds_are_free_at_full_size() {
    use crate::circuit::LOG_ROWS;
    use crate::protocol::{QUOTIENT_RANDOM_LANES, WITNESS_RANDOM_LANES, quotient_layout, witness_layout};
    let mut rng = Rng::new(0xF3EE);
    for log_rows in [17, LOG_ROWS] {
        for seed in 0..3 {
            let (witness, quotient) = reduced_points(log_rows, seed);
            let phi = rng.ext_vec(LANE_FOLD);
            let lambdas = powers(rng.ext(), 2);
            let w = std::slice::from_ref(&witness);
            let layout = witness_layout(log_rows);
            assert_eq!(round_freedom(&layout, w, &lambdas[..1], &phi, 300, &mut rng), (33, 3));
            let layout = quotient_layout(log_rows);
            assert_eq!(
                round_freedom(&layout, &quotient, &lambdas, &phi, 300, &mut rng),
                (33, 3)
            );

            let (fewer_w, fewer_q) = full_layouts(log_rows, WITNESS_RANDOM_LANES - 1, QUOTIENT_RANDOM_LANES - 1);
            assert!(round_freedom(&fewer_w, w, &lambdas[..1], &phi, 300, &mut rng).0 < 33);
            assert!(round_freedom(&fewer_q, &quotient, &lambdas, &phi, 300, &mut rng).0 < 33);
        }
    }
}

/// A toy circuit with one input bit the statement does not depend on: two witnesses of one statement.
fn two_witnesses() -> (
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
fn guessed_witness(
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
#[test]
fn calldata_alone_does_not_confirm_a_witness() {
    use crate::protocol::{Index, label, prove};
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
        let proof = prove(
            &circuit,
            &index,
            &index_committed.root,
            &statement,
            &cells,
            &masks,
            &seed,
        )
        .proof;
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
        let mut verdict = vec![];
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
        }
        assert_eq!(verdict, [false, false], "trial {trial}");

        let again: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        let other = prove(
            &circuit,
            &index,
            &index_committed.root,
            &statement,
            &cells,
            &masks,
            &again,
        )
        .proof;
        assert_ne!(other.stream[..2], proof.stream[..2], "the root commits to the padding");
    }
}

/// The review's opening distinguisher, turned around: the witness table's opened rows match no row a candidate
/// witness commits to, whichever candidate; and they say nothing of the masks, for at the opened positions the
/// overflow lane's random first piece alone reaches every value, so the masks' contributions lie in its span.
#[test]
fn opened_rows_do_not_identify_the_witness() {
    use crate::protocol::{Index, open, prove, witness_layout};
    use std::collections::HashSet;
    let (circuit, inputs, statement) = two_witnesses();
    let index = Index::new(&circuit);
    let index_committed = opening::commit(&index.table);
    let mut rng = Rng::new(0x2D);
    let secret = rng.next_u64() & 1 == 1;
    let masks: [[F64; 3]; 4] = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let cells = circuit.cells(&inputs(secret));
    let proved = prove(
        &circuit,
        &index,
        &index_committed.root,
        &statement,
        &cells,
        &masks,
        &seed,
    );
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
    for hypothesis in [false, true] {
        let table = guessed_witness(&circuit, &circuit.cells(&inputs(hypothesis)), &mask, &[0; 32]);
        let (_, data) = pcs::whir::commit(&table.stack, layout.log_n, LANE_FOLD, LOG_INV_RATE);
        let candidate: HashSet<Vec<u64>> = data
            .codeword
            .chunks_exact(lanes)
            .map(|r| r.iter().map(|w| w.0).collect())
            .collect();
        assert_eq!(
            rows.iter().filter(|r| candidate.contains(*r)).count(),
            0,
            "dummy = {hypothesis}"
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
    let first: Vec<Vec<F64>> = opened.iter().map(|&x| column(log_lane, x)[..1 << s].to_vec()).collect();
    let with_masks: Vec<Vec<F64>> = opened
        .iter()
        .map(|&x| {
            let col = column(log_lane, x);
            [&col[..1 << s], &col[mask_piece << s..(mask_piece << s) + 16]].concat()
        })
        .collect();
    assert_eq!(rank(first), opened.len());
    assert_eq!(rank(with_masks), opened.len());
    println!(
        "{} distinct positions opened: the first piece's columns have rank {0}",
        opened.len()
    );
}
