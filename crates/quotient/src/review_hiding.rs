// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! An adversarial review of `HIDING.md` (commit 201a5d1), in the real fields, on the real layouts and with the
//! real WHIR prover.
//!
//! - [`translation_holds_on_real_openings`]: HIDING.md's argument, run constructively at full size (`2^17` rows,
//!   both tables, their real claims, the real 223 first-level queries): for two tables with the same claims (the
//!   witness table of two witnesses of one statement, with the masks the `a_j` pin; and the quotient table plus a
//!   random change that keeps both its claims), a change of the padding alone (steps 1 and 2 of "Why it hides",
//!   with condition (R) solved for) makes the real prover's opening of the second table byte for byte that of
//!   the first, every sumcheck message, out-of-domain value, nonce, deeper row, sibling and the final polynomial,
//!   but for the first commitment's root and sibling hashes. This checks the model of the view (V1)–(V3) is
//!   complete against the actual proof bytes, at the real sizes.
//! - [`reused_seed_confirms_the_witness`], [`reused_masks_confirm_the_witness`]: what `prove`'s randomness must
//!   be. HIDING.md and `prove` ask for the masks and the seed to be "uniform and secret", which a fixed secret
//!   meets; two proofs that share either one let an observer confirm a guessed witness.
//! - [`rounds_are_free_at_every_size`]: condition (R) and (S) at every supported size, more draws.

use fiat_shamir::digest_words;
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::{Proof, ProverState};
use pcs::whir::{LaneTensor, commit_tree, config_for_rate, encoded_rows, recursive_prover_with_lane_tensors};
use primitives::field::{F64, F192, powers};
use primitives::multilinear::eq_table;
use primitives::test_rng::Rng;

use crate::hiding::{column, coords, guessed_witness, keeps_last_claim, kernel, random_at, two_witnesses};
use crate::opening::{self, Claim, LANE_FOLD, LOG_INV_RATE, Lane, Layout, Table};

/// Gauss–Jordan elimination of `m` over its first `cols` columns (the rest ride along): the pivot columns, row
/// `i` holding pivot `i`.
fn rref(m: &mut [Vec<F64>], cols: usize) -> Vec<usize> {
    let mut pivots = vec![];
    let mut r = 0;
    for c in 0..cols {
        let Some(p) = (r..m.len()).find(|&i| !m[i][c].is_zero()) else {
            continue;
        };
        m.swap(r, p);
        let inverse = m[r][c].inv();
        m[r].iter_mut().for_each(|x| *x *= inverse);
        let pivot_row = m[r].clone();
        for (i, row) in m.iter_mut().enumerate() {
            let f = row[c];
            if i != r && !f.is_zero() {
                row.iter_mut().zip(&pivot_row).for_each(|(a, &b)| *a += f * b);
            }
        }
        pivots.push(c);
        r += 1;
        if r == m.len() {
            break;
        }
    }
    pivots
}

/// The combined weight of the opening at every lane of entry `y`.
fn weight_at(tensors: &[LaneTensor], lanes: usize, y: usize) -> Vec<F192> {
    (0..lanes)
        .map(|l| tensors.iter().fold(F192::ZERO, |acc, t| acc + t.scales[l] * t.low[y]))
        .collect()
}

/// The six lane rounds' sent values `(u_0, u_2)` of `Σ_l w_l·s_l` at one in-lane entry, the lanes padded to 64,
/// folded as the prover folds them (`x_0 + r·(x_0 + x_1)`).
fn messages_at(w: &[F192], s: &[F192], phi: &[F192]) -> [F192; 12] {
    let mut w = w.to_vec();
    let mut s = s.to_vec();
    w.resize(1 << LANE_FOLD, F192::ZERO);
    s.resize(1 << LANE_FOLD, F192::ZERO);
    let mut out = [F192::ZERO; 12];
    for j in 0..LANE_FOLD {
        let half = w.len() / 2;
        for i in 0..half {
            out[2 * j] += w[2 * i] * s[2 * i];
            out[2 * j + 1] += (w[2 * i] + w[2 * i + 1]) * (s[2 * i] + s[2 * i + 1]);
        }
        for i in 0..half {
            w[i] = w[2 * i] + phi[j] * (w[2 * i] + w[2 * i + 1]);
            s[i] = s[2 * i] + phi[j] * (s[2 * i] + s[2 * i + 1]);
        }
        w.truncate(half);
        s.truncate(half);
    }
    out
}

/// The lane rounds' twelve sent values on a whole stack (they are linear in it).
fn messages(layout: &Layout, tensors: &[LaneTensor], phi: &[F192], stack: &[F64]) -> [F192; 12] {
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let lane = 1usize << log_lane;
    let chunk = 1usize << 10;
    parallel::map_reduce(
        lane / chunk,
        || [F192::ZERO; 12],
        |c| {
            let mut acc = [F192::ZERO; 12];
            for y in c * chunk..(c + 1) * chunk {
                let s: Vec<F192> = (0..lanes).map(|l| F192::from(stack[l * lane + y])).collect();
                if s.iter().all(|x| x.is_zero()) {
                    continue;
                }
                let m = messages_at(&weight_at(tensors, lanes, y), &s, phi);
                acc.iter_mut().zip(m).for_each(|(a, b)| *a += b);
            }
            acc
        },
        |mut a, b| {
            a.iter_mut().zip(b).for_each(|(x, y)| *x += y);
            a
        },
    )
}

/// The folded table `f¹(y) = Σ_l eq(φ, l)·stack_l(y)`.
fn folded(layout: &Layout, phi: &[F192], stack: &[F64]) -> Vec<F192> {
    let (lanes, lane) = (layout.lanes(), 1usize << layout.log_lane());
    let e = eq_table(phi);
    (0..lane)
        .map(|y| (0..lanes).fold(F192::ZERO, |acc, l| acc + e[l].mul_base(stack[l * lane + y])))
        .collect()
}

/// An opening of `claims` on `stack`, by the real prover (what [`opening::open`] runs), from a transcript seeded
/// with `fs` rather than with the stack's own root: two stacks opened from one seed draw the same challenges as
/// long as their transcripts agree.
fn open_from(layout: &Layout, stack: &[F64], claims: &[Claim], fs: &([u8; 32], [u8; 32])) -> (Hash, Proof) {
    let config = config_for_rate(layout.log_n, LOG_INV_RATE).expect("a supported shape");
    let (commitment, tree) = commit_tree(stack, layout.log_n, LANE_FOLD, LOG_INV_RATE);
    let mut ps = ProverState::new(digest_words(&fs.0), digest_words(&fs.1));
    let lambdas = powers(ps.sample(), claims.len());
    let target = claims
        .iter()
        .zip(&lambdas)
        .fold(F192::ZERO, |acc, (c, &l)| acc + l * c.value);
    let weight: Vec<LaneTensor> = claims
        .iter()
        .zip(&lambdas)
        .flat_map(|(c, &l)| layout.tensors(&c.point, l))
        .collect();
    recursive_prover_with_lane_tensors(&config, layout.log_n, stack, &weight, target, None, &tree[..], &mut ps);
    (commitment.root, ps.into_proof())
}

/// What anyone reads off an opening, up to its first level's rows: the batching powers, the lane rounds'
/// challenges and sent values, the first level's query positions (in order, repeats kept) and rows (in stack
/// lane order).
struct FirstLevel {
    lambdas: Vec<F192>,
    phi: Vec<F192>,
    sent: Vec<F192>,
    queries: Vec<usize>,
    rows: Vec<Vec<F64>>,
}

/// The verifier's query sampling (`verifier::whir::sample_queries`).
fn sample_queries(tr: &mut verifier::Transcript, block: u64, count: usize) -> Vec<usize> {
    let depth = block.trailing_zeros() as usize;
    let per = 192 / depth;
    let mut out = vec![];
    while out.len() < count {
        let s = tr.sample();
        let bits = [s.c0, s.c1, s.c2, 0];
        for chunk in 0..per.min(count - out.len()) {
            let (limb, shift) = (chunk * depth / 64, chunk * depth % 64);
            let window = (bits[limb] as u128 | (bits[limb + 1] as u128) << 64) >> shift;
            out.push((window as u64 & (block - 1)) as usize);
        }
    }
    out
}

/// Replay an opening as its verifier does, from public data alone, through the first level's Merkle opening
/// (checked against `root`).
fn replay(layout: &Layout, root: &Hash, claims: &[Claim], fs: &([u8; 32], [u8; 32]), proof: &Proof) -> FirstLevel {
    use verifier::{Digest, E, Transcript};
    let wire = opening::wire_proof(proof);
    let mut tr = Transcript::new(&wire, Digest(fs.0), Digest(fs.1), true);
    let to = |x: E| F192::new(x.c0, x.c1, x.c2);
    let from = |x: F192| E::new(x.c0, x.c1, x.c2);
    let lambdas = powers(to(tr.sample()), claims.len());
    let mut claim = from(
        claims
            .iter()
            .zip(&lambdas)
            .fold(F192::ZERO, |acc, (c, &l)| acc + l * c.value),
    );
    let (mut phi, mut sent) = (vec![], vec![]);
    for _ in 0..LANE_FOLD {
        let poly = tr.sumcheck_round_poly(3, claim, None).unwrap();
        sent.extend([to(poly[0]), to(poly[2])]);
        let r = tr.sample();
        phi.push(to(r));
        claim = poly[0] + r * (poly[1] + r * poly[2]);
    }
    let log_lane = layout.log_lane();
    tr.sumcheck_round_poly(3, claim, None).unwrap();
    tr.next_scalars(2).unwrap();
    tr.samples(log_lane);
    let ood = tr.next_scalar().unwrap();
    tr.sumcheck_round_poly(3, ood, None).unwrap();
    tr.grind_check(pcs::whir::QUERY_GRINDING_BITS as u32).unwrap();
    let block = 1u64 << (log_lane + LOG_INV_RATE);
    let count = config_for_rate(layout.log_n, LOG_INV_RATE).unwrap().queries[0];
    let queries = sample_queries(&mut tr, block, count);
    tr.sample();
    let q64: Vec<u64> = queries.iter().map(|&q| q as u64).collect();
    let lanes = layout.lanes();
    let words = tr.merkle(Digest(*root), block, &q64, lanes, 1 << LANE_FOLD).unwrap();
    let rows = words
        .iter()
        .map(|image| (0..lanes).map(|l| F64(image[(1 << LANE_FOLD) - 1 - l].0)).collect())
        .collect();
    FirstLevel {
        lambdas,
        phi,
        sent,
        queries,
        rows,
    }
}

/// The rows of `stack`'s first-level codeword at `positions`, in stack lane order.
fn rows_at(layout: &Layout, stack: &[F64], positions: &[usize]) -> Vec<Vec<F64>> {
    let lanes = layout.lanes();
    encoded_rows(stack, layout.log_n, LANE_FOLD, LOG_INV_RATE, positions)
        .into_iter()
        .map(|row| (0..lanes).map(|l| row[lanes - 1 - l]).collect())
        .collect()
}

/// HIDING.md's translation, run: `delta` changes a hidden stack's table entries only (its padding is untouched)
/// and keeps every claim; add to it a change of the padding alone after which the lane rounds, `f¹` and the
/// rows at `positions` do not move. Step 1 (past the first pieces): three random lanes cancel `f¹`'s change at
/// every entry, then changes that keep `f¹` (the kernels of condition (R)) cancel what is left of the rounds'.
/// Step 2: each lane's first piece cancels its rows' change. Panics if a step has no solution.
fn translate(
    layout: &Layout,
    tensors: &[LaneTensor],
    phi: &[F192],
    positions: &[usize],
    delta: &mut [F64],
    rng: &mut Rng,
) {
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let lane = 1usize << log_lane;
    let s = layout.log_piece().expect("a hidden layout");
    let piece = 1usize << s;
    let held = layout.pieces().len();
    let e = eq_table(phi);

    // Step 1: three random lanes (not the share) whose fold weights span E over K: condition (S).
    let random: Vec<usize> = (0..lanes)
        .filter(|&l| layout.lane(l) == Lane::Random && layout.share() != Some(l))
        .collect();
    let mut chosen = None;
    'search: for a in 0..random.len() {
        for b in a + 1..random.len() {
            for c in b + 1..random.len() {
                let lanes3 = [random[a], random[b], random[c]];
                let mut m: Vec<Vec<F64>> = (0..3)
                    .map(|k| {
                        let mut row: Vec<F64> = lanes3.iter().map(|&r| coords(e[r])[k]).collect();
                        row.extend((0..3).map(|j| if j == k { F64::ONE } else { F64::ZERO }));
                        row
                    })
                    .collect();
                if rref(&mut m, 3).len() == 3 {
                    let inverse: Vec<Vec<F64>> = m.iter().map(|row| row[3..].to_vec()).collect();
                    chosen = Some((lanes3, inverse));
                    break 'search;
                }
            }
        }
    }
    let (three, inverse) = chosen.expect("condition (S)");
    for y in piece..lane {
        let d = (0..lanes).fold(F192::ZERO, |acc, l| acc + e[l].mul_base(delta[l * lane + y]));
        let d = coords(d);
        for (i, &r) in three.iter().enumerate() {
            let c = (0..3).fold(F64::ZERO, |acc, k| acc + inverse[i][k] * d[k]);
            delta[r * lane + y] += c;
        }
    }
    let f1 = folded(layout, phi, delta);
    assert!(f1.iter().all(|x| x.is_zero()), "step 1 keeps f¹");

    // What is left of the rounds' change, and the moves that keep `f¹`, at sampled entries of both kinds.
    let left = messages(layout, tensors, phi, delta);
    assert!(
        keeps_last_claim(&left, phi),
        "the rounds' change keeps the claim and the last value"
    );
    let mut ys: Vec<usize> = vec![];
    for holds in [true, false] {
        let pool: Vec<usize> = (piece..lane).filter(|&y| ((y >> s) <= held) == holds).collect();
        for _ in 0..64.min(pool.len()) {
            ys.push(pool[(rng.next_u64() as usize) % pool.len()]);
        }
    }
    // One column per move: (entry, the unknowns there, the kernel vector), its twelve values' K coordinates.
    let mut moves: Vec<(usize, Vec<Vec<usize>>, Vec<F64>)> = vec![];
    let mut columns: Vec<Vec<F64>> = vec![];
    for &y in &ys {
        let unknowns = random_at(layout, y);
        let folds: Vec<F192> = unknowns
            .iter()
            .map(|u| u.iter().fold(F192::ZERO, |acc, &r| acc + e[r]))
            .collect();
        let m: Vec<Vec<F64>> = (0..3).map(|c| folds.iter().map(|&f| coords(f)[c]).collect()).collect();
        let w = weight_at(tensors, lanes, y);
        let unit: Vec<[F192; 12]> = unknowns
            .iter()
            .map(|u| {
                let mut s = vec![F192::ZERO; lanes];
                u.iter().for_each(|&r| s[r] = F192::ONE);
                messages_at(&w, &s, phi)
            })
            .collect();
        for k in kernel(&m, unknowns.len()) {
            let mut total = [F192::ZERO; 12];
            for (mv, &ku) in unit.iter().zip(&k) {
                total.iter_mut().zip(mv).for_each(|(o, &x)| *o += x.mul_base(ku));
            }
            columns.push(total.iter().flat_map(|&x| coords(x)).collect());
            moves.push((y, unknowns.clone(), k));
        }
    }
    // Solve `Σ_j a_j·move_j = left` (36 K-equations).
    let n = columns.len();
    let target: Vec<F64> = left.iter().flat_map(|&x| coords(x)).collect();
    let mut system: Vec<Vec<F64>> = (0..36)
        .map(|i| {
            let mut row: Vec<F64> = columns.iter().map(|col| col[i]).collect();
            row.push(target[i]);
            row
        })
        .collect();
    let pivots = rref(&mut system, n);
    assert_eq!(
        pivots.len(),
        33,
        "condition (R): the moves reach the rounds' 33 dimensions"
    );
    assert!(
        system[pivots.len()..].iter().all(|row| row[n].is_zero()),
        "the rounds' change lies in their reach"
    );
    for (i, &j) in pivots.iter().enumerate() {
        let a = system[i][n];
        if a.is_zero() {
            continue;
        }
        let (y, unknowns, k) = &moves[j];
        for (u, &ku) in unknowns.iter().zip(k) {
            for &r in u {
                delta[r * lane + y] += a * ku;
            }
        }
    }
    assert!(
        messages(layout, tensors, phi, delta).iter().all(|x| x.is_zero()),
        "step 1 keeps the rounds"
    );
    assert!(folded(layout, phi, delta).iter().all(|x| x.is_zero()), "and f¹");

    // Step 2: each lane's first piece cancels its rows' change at the opened positions, by one right inverse
    // of the first piece's evaluation there (the same for every lane, so `f¹`'s first piece stays put).
    let mut distinct = positions.to_vec();
    distinct.sort_unstable();
    distinct.dedup();
    assert!(distinct.len() < piece, "condition (Q)");
    let rows = rows_at(layout, delta, &distinct);
    let mut system: Vec<Vec<F64>> = distinct
        .iter()
        .zip(&rows)
        .map(|(&x, row)| [&column(s, x)[..piece], &row[..]].concat())
        .collect();
    let pivots = rref(&mut system, piece);
    assert_eq!(
        pivots.len(),
        distinct.len(),
        "the first piece reaches every opened position"
    );
    for (i, &y) in pivots.iter().enumerate() {
        for l in 0..lanes {
            delta[l * lane + y] += system[i][piece + l];
        }
    }
    assert!(
        rows_at(layout, delta, &distinct)
            .iter()
            .all(|r| r.iter().all(|x| x.is_zero())),
        "step 2 keeps the rows"
    );
    assert!(folded(layout, phi, delta).iter().all(|x| x.is_zero()), "and f¹");
    assert!(
        messages(layout, tensors, phi, delta).iter().all(|x| x.is_zero()),
        "and the rounds"
    );
}

/// The table's entries a hidden stack holds, read back.
fn entries(layout: &Layout, stack: &[F64]) -> Vec<F64> {
    let table = Table {
        layout: layout.clone(),
        stack: stack.to_vec(),
    };
    let mut out = vec![F64::ZERO; 1 << layout.vars];
    table.read(0, &mut out);
    out
}

/// Whether stack entry `i` is padding: first pieces, random lanes (the share's held pieces included), the
/// overflow lane past its held pieces.
fn is_padding(layout: &Layout, i: usize) -> bool {
    let s = layout.log_piece().expect("a hidden layout");
    let (l, y) = (i >> layout.log_lane(), i & ((1 << layout.log_lane()) - 1));
    y < 1 << s
        || match layout.lane(l) {
            Lane::Random => true,
            Lane::Overflow => y >> s > layout.pieces().len(),
            Lane::Block(_) => false,
        }
}

/// A change of a hidden stack's table entries, uniform among those that keep every claim at `points` (the
/// padding untouched).
fn random_claim_kernel(layout: &Layout, points: &[Vec<F192>], rng: &mut Rng) -> Vec<F64> {
    let placed = layout.placed();
    let lane = 1usize << layout.log_lane();
    let share = layout.share().unwrap();
    let mut delta = vec![F64::ZERO; placed];
    for (i, d) in delta.iter_mut().enumerate() {
        // The table's entries: block lanes past the first piece, the overflow lane's held pieces (the share
        // lane's are its padding).
        if !is_padding(layout, i) {
            *d = F64(rng.next_u64());
        }
    }
    assert!(delta[share * lane..(share + 1) * lane].iter().all(|x| x.is_zero()));
    // The claims of a change, as K-coordinates; fix them with entries every claim weighs.
    let unit: Vec<Vec<LaneTensor>> = points.iter().map(|p| layout.tensors(p, F192::ONE)).collect();
    let claims_of = |delta: &[F64]| -> Vec<F64> {
        unit.iter()
            .flat_map(|tensors| {
                let mut v = F192::ZERO;
                for t in tensors {
                    for (l, &sc) in t.scales.iter().enumerate() {
                        if sc.is_zero() {
                            continue;
                        }
                        let inner = parallel::map_reduce(
                            lane >> 10,
                            || F192::ZERO,
                            |c| {
                                (c << 10..(c + 1) << 10)
                                    .fold(F192::ZERO, |acc, y| acc + t.low[y].mul_base(delta[l * lane + y]))
                            },
                            |a, b| a + b,
                        );
                        v += sc * inner;
                    }
                }
                coords(v)
            })
            .collect()
    };
    let at = |i: usize| -> Vec<F64> {
        unit.iter()
            .flat_map(|tensors| {
                let (l, y) = (i / lane, i % lane);
                coords(tensors.iter().fold(F192::ZERO, |acc, t| acc + t.scales[l] * t.low[y]))
            })
            .collect()
    };
    // Candidates: the data entries a sparse claim (the sum claim) weighs, and random ones.
    let mut candidates: Vec<usize> = vec![];
    for tensors in unit.iter().skip(1) {
        for t in tensors {
            let ys: Vec<usize> = (0..lane).filter(|&y| !t.low[y].is_zero()).take(17).collect();
            if ys.len() > 16 {
                continue;
            }
            for (l, sc) in t.scales.iter().enumerate() {
                for &y in ys.iter().filter(|_| !sc.is_zero()) {
                    if !is_padding(layout, l * lane + y) {
                        candidates.push(l * lane + y);
                    }
                }
            }
        }
    }
    while candidates.len() < 128 {
        let i = (rng.next_u64() as usize) % placed;
        if !is_padding(layout, i) {
            candidates.push(i);
        }
    }
    let cols: Vec<Vec<F64>> = candidates.iter().map(|&i| at(i)).collect();
    let rhs = claims_of(&delta);
    let k = rhs.len();
    let mut system: Vec<Vec<F64>> = (0..k)
        .map(|r| {
            let mut row: Vec<F64> = cols.iter().map(|c| c[r]).collect();
            row.push(rhs[r]);
            row
        })
        .collect();
    let n = candidates.len();
    let pivots = rref(&mut system, n);
    assert_eq!(pivots.len(), k, "the claims are independent on the candidates");
    for (r, &j) in pivots.iter().enumerate() {
        delta[candidates[j]] += system[r][n];
    }
    assert!(
        claims_of(&delta).iter().all(|x| x.is_zero()),
        "the change keeps every claim"
    );
    delta
}

/// A random `K`-linear functional of a stack's table entries (the overflow lane's held entries are the table's
/// plus the share lane's there): equal on two stacks, but with probability `2^-64`, only if they hold the same
/// table entries in the same places.
fn fingerprint(layout: &Layout, stack: &[F64]) -> F64 {
    let chunk = 1usize << 12;
    let lane = 1usize << layout.log_lane();
    let (overflow, share) = (layout.overflow().unwrap(), layout.share().unwrap());
    parallel::map_reduce(
        stack.len() / chunk,
        || F64::ZERO,
        |c| {
            (c * chunk..(c + 1) * chunk)
                .filter(|&i| !is_padding(layout, i))
                .fold(F64::ZERO, |acc, i| {
                    let w = (i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(29) ^ 0xD6E8_FEB8_6659_FD93;
                    let entry = if i / lane == overflow {
                        stack[i] + stack[share * lane + i % lane]
                    } else {
                        stack[i]
                    };
                    acc + F64(w) * entry
                })
        },
        |a, b| a + b,
    )
}

/// Run the translation on `table` and `table + delta` (`delta` a change of the table's entries that keeps the
/// claims), open both with the real prover from one transcript seed, and compare every byte. Holds two stacks
/// at a time.
fn translation_case(name: &str, table: &Table, mut delta: Vec<F64>, claims: &[Claim], rng: &mut Rng) {
    let (layout, stack) = (&table.layout, &table.stack[..]);
    let placed = layout.placed();
    assert_eq!(stack.len(), placed);
    assert!(
        (0..placed).all(|i| !is_padding(layout, i) || delta[i].is_zero()),
        "{name}: a change of the table"
    );
    let add = |delta: &mut [F64]| {
        parallel::chunks_mut(delta, 1 << 16, |c, out| {
            out.iter_mut().zip(&stack[c << 16..]).for_each(|(d, &s)| *d += s)
        })
    };
    let points: Vec<Vec<F192>> = claims.iter().map(|c| c.point.clone()).collect();
    // The first stack's own opening, exactly as `opening::open` makes it.
    let root = commit_tree(stack, layout.log_n, LANE_FOLD, LOG_INV_RATE).0.root;
    let fs = opening::seed(&root, claims);
    let (root_again, proof) = open_from(layout, stack, claims, &fs);
    assert_eq!(root_again, root);
    assert_eq!(
        opening::verify(layout, &root, claims, &opening::wire_proof(&proof)),
        Ok(()),
        "{name}: an honest opening"
    );
    let view = replay(layout, &root, claims, &fs, &proof);
    let tensors: Vec<LaneTensor> = points
        .iter()
        .zip(&view.lambdas)
        .flat_map(|(p, &l)| layout.tensors(p, l))
        .collect();
    // The model of the view is the proof's: the twelve values, and the rows at the replayed positions.
    assert_eq!(
        messages(layout, &tensors, &view.phi, stack).to_vec(),
        view.sent,
        "{name}: rounds"
    );
    assert_eq!(rows_at(layout, stack, &view.queries), view.rows, "{name}: rows");

    // The second table, with the first one's padding: its opening differs from the first's.
    add(&mut delta);
    let (_, naive) = open_from(layout, &delta, claims, &fs);
    assert_ne!(naive.stream, proof.stream, "{name}: the same padding shows the change");
    let second = fingerprint(layout, &delta);
    let second_entries = (placed <= 1 << 24).then(|| entries(layout, &delta));
    add(&mut delta);

    translate(layout, &tensors, &view.phi, &view.queries, &mut delta, rng);
    assert!(
        (0..placed).any(|i| is_padding(layout, i) && !delta[i].is_zero()),
        "{name}: a new padding"
    );
    add(&mut delta);
    let other = Table {
        layout: layout.clone(),
        stack: delta,
    };
    // The translated stack holds the second table, and its claims.
    assert_eq!(fingerprint(layout, &other.stack), second, "{name}: the second table");
    if let Some(second_entries) = second_entries {
        assert_eq!(
            entries(layout, &other.stack),
            second_entries,
            "{name}: the second table, entry by entry"
        );
    }
    for c in claims {
        assert_eq!(
            other.eval(&c.point),
            c.value,
            "{name}: the claims hold on the second table"
        );
    }

    let (other_root, other_proof) = open_from(layout, &other.stack, claims, &fs);
    assert_ne!(
        other_root, root,
        "{name}: the roots differ (they hide behind the oracle)"
    );
    assert_eq!(other_proof.stream, proof.stream, "{name}: every scalar of the opening");
    assert_eq!(other_proof.merkle.len(), proof.merkle.len());
    assert_eq!(
        other_proof.merkle[0].leaf_data, proof.merkle[0].leaf_data,
        "{name}: the first level's rows"
    );
    assert_ne!(other_proof.merkle[0].sibling_hashes, proof.merkle[0].sibling_hashes);
    for (a, b) in other_proof.merkle.iter().zip(&proof.merkle).skip(1) {
        assert_eq!(a.leaf_data, b.leaf_data, "{name}: deeper rows");
        assert_eq!(a.sibling_hashes, b.sibling_hashes, "{name}: deeper siblings");
    }
    // The second opening checks against its own root (the verifier's transcript replayed from the same seed).
    let again = replay(layout, &other_root, claims, &fs, &other_proof);
    assert_eq!(again.rows, view.rows);
    println!(
        "{name}: {} lanes of 2^{}, {} first-level queries ({} distinct), proof of {} scalars and {} Merkle batches: \
         identical but for the first level's root and {} sibling hashes",
        layout.lanes(),
        layout.log_lane(),
        view.queries.len(),
        {
            let mut d = view.queries.clone();
            d.sort_unstable();
            d.dedup();
            d.len()
        },
        proof.stream.len(),
        proof.merkle.len(),
        proof.merkle[0].sibling_hashes.len()
    );
}

/// The witness table's seed, as `prove` derives it.
fn witness_seed(seed: &[u8; 32]) -> [u8; 32] {
    primitives::hash::hash(&[b"pcs-quotient-pad-".as_slice(), b"witness", seed].concat())
}

/// For a candidate witness's coefficients, the twelve mask coefficients the proof's four `a_j` pin, and the
/// point's digits (`w_2, w_3, w_m`): from the proof's scalars alone.
fn pinned_masks(
    circuit: &crate::circuit::Circuit,
    index_root: &Hash,
    statement: &crate::statement::Statement,
    stream: &[F192],
    w_hat: &[F64],
) -> ([F64; 16], Vec<F192>) {
    use crate::protocol::label;
    use crate::transcript::ProverChain;
    let s = stream;
    let mut chain = ProverChain::new(&label(index_root, statement));
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
    let mut mask = [F64::ZERO; 16];
    for j in 0..4 {
        let v = (s[4 + j] + crate::domain::evaluate(w_hat, j, 4, &digits[2..m])) * wm.inv();
        let rows: Vec<Vec<F64>> = (0..3)
            .map(|c| [F192::ONE, w2, w3, v].iter().map(|&e| coords(e)[c]).collect())
            .collect();
        let solution = kernel(&rows, 4);
        assert_eq!(solution.len(), 1);
        let scale = solution[0][3].inv();
        for i in 0..3 {
            mask[4 * i + j] = solution[0][i] * scale;
        }
    }
    (mask, digits)
}

fn coefficients_of(cells: &[F64]) -> Vec<F64> {
    let mut w_hat = cells.to_vec();
    crate::domain::coefficients(&mut w_hat, F64::ZERO);
    w_hat
}

/// HIDING.md's theorem, run constructively on the real layouts at `2^17` rows with the real prover: see the
/// module's documentation.
#[test]
fn translation_holds_on_real_openings() {
    use crate::protocol::{Index, prove, quotient_layout, witness_layout};
    let mut rng = Rng::new(0x7E5);
    let (circuit, inputs, statement) = two_witnesses();
    let index = Index::new(&circuit);
    let index_root = opening::commit(&index.table).root;
    let secret = rng.bit();
    let masks: [[F64; 3]; 4] = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let proved = prove(
        &circuit,
        &index,
        &index_root,
        &statement,
        &circuit.cells(&inputs(secret)),
        &masks,
        &seed,
    );

    // The witness table of the other witness, with the masks the proof's `a_j` pin for it, and this proof's
    // padding: it has the same claim.
    let layout = witness_layout(circuit.log_rows);
    let other_cells = circuit.cells(&inputs(!secret));
    let (mask, _) = pinned_masks(
        &circuit,
        &index_root,
        &statement,
        &proved.proof.stream,
        &coefficients_of(&other_cells),
    );
    let other = guessed_witness(&circuit, &other_cells, &mask, &witness_seed(&seed));
    let stack = &proved.tables.witness.stack;
    assert_ne!(entries(&layout, &other.stack), entries(&layout, stack), "two tables");
    assert_eq!(
        other.eval(&proved.claims.witness.point),
        proved.claims.witness.value,
        "one claim"
    );
    let delta: Vec<F64> = other.stack.iter().zip(stack).map(|(&a, &b)| a + b).collect();
    assert!((0..layout.placed()).all(|i| !is_padding(&layout, i) || delta[i].is_zero()));
    let claims = [proved.claims.witness.clone()];
    let witness = &proved.tables.witness;
    translation_case("witness table, two witnesses", witness, delta, &claims, &mut rng);

    // The witness table again, any change that keeps its claim.
    let points = vec![proved.claims.witness.point.clone()];
    let delta = random_claim_kernel(&layout, &points, &mut rng);
    translation_case("witness table, a random change", witness, delta, &claims, &mut rng);

    // The quotient table, both claims: any change that keeps them.
    let layout = quotient_layout(circuit.log_rows);
    let claims = [proved.claims.quotient.clone(), proved.claims.sum.clone()];
    let points: Vec<Vec<F192>> = claims.iter().map(|c| c.point.clone()).collect();
    let delta = random_claim_kernel(&layout, &points, &mut rng);
    translation_case(
        "quotient table, a random change",
        &proved.tables.quotient,
        delta,
        &claims,
        &mut rng,
    );
}

/// The same at the benchmark's size, `2^22` rows (both tables at their largest: the quotient's stack is `2^28`
/// words, 225 first-level queries), on tables of pseudo-random entries at the reduction's own claim points.
/// Some 8 GB: `cargo test --release -p quotient translation_holds_at_the_benchmark_size -- --ignored`.
#[test]
#[ignore]
fn translation_holds_at_the_benchmark_size() {
    use crate::circuit::LOG_ROWS;
    use crate::hiding::reduced_points;
    use crate::protocol::{quotient_layout, sum_point, witness_layout};
    let mut rng = Rng::new(0xB16);
    let (witness_point, quotient_points) = reduced_points(LOG_ROWS, 0x22);
    assert_eq!(quotient_points[1], sum_point(LOG_ROWS));
    let pseudo = |i: usize| F64((i as u64 + 7).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(23) ^ 0x5555);
    for (name, layout, points) in [
        (
            "witness table, 2^22 rows",
            witness_layout(LOG_ROWS),
            vec![witness_point],
        ),
        ("quotient table, 2^22 rows", quotient_layout(LOG_ROWS), quotient_points),
    ] {
        let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        let table = Table::hidden(layout.clone(), &seed, |start, out| {
            out.iter_mut().enumerate().for_each(|(k, o)| *o = pseudo(start + k));
        });
        let claims: Vec<Claim> = points
            .into_iter()
            .map(|point| Claim {
                value: table.eval(&point),
                point,
            })
            .collect();
        let delta = random_claim_kernel(
            &layout,
            &claims.iter().map(|c| c.point.clone()).collect::<Vec<_>>(),
            &mut rng,
        );
        translation_case(name, &table, delta, &claims, &mut rng);
    }
}

/// Two proofs that share the padding's seed (fresh masks each): the witness table's block lanes hold the same
/// first piece in both, so their opened rows, less a candidate witness's codeword past the first piece, fit one
/// polynomial of degree below `2^8` across both proofs' positions (about 446 > 256) only for the true witness.
/// From public data alone: the proofs, the openings, the circuit. With fresh seeds neither candidate fits.
#[test]
fn reused_seed_confirms_the_witness() {
    use crate::protocol::{Index, open, prove, verify, witness_layout};
    let mut rng = Rng::new(0x5EED);
    let (circuit, inputs, statement) = two_witnesses();
    let index = Index::new(&circuit);
    let index_committed = opening::commit(&index.table);
    let layout = witness_layout(circuit.log_rows);
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let lane = 1usize << log_lane;
    let s = layout.log_piece().unwrap();
    let piece = 1usize << s;
    let n = 1usize << (circuit.log_rows + 2);

    // A candidate's block lanes past their first piece, everything else zero: what an observer can encode.
    let candidate_stack = |w_hat: &[F64]| -> Vec<F64> {
        let mut stack = vec![F64::ZERO; layout.placed()];
        for l in 0..lanes {
            if let Lane::Block(b) = layout.lane(l) {
                for k in 1..lane / piece {
                    let from = (b << log_lane) + (k ^ (l & 1)) * piece;
                    if from < n {
                        stack[l * lane + k * piece..l * lane + (k + 1) * piece]
                            .copy_from_slice(&w_hat[from..from + piece]);
                    }
                }
            }
        }
        stack
    };
    let candidates: Vec<Vec<F64>> = [false, true]
        .iter()
        .map(|&h| candidate_stack(&coefficients_of(&circuit.cells(&inputs(h)))))
        .collect();

    for reuse in [true, false] {
        let secret = rng.bit();
        let cells = circuit.cells(&inputs(secret));
        let first_seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        // Two proofs of the same witness, fresh masks each; the seed reused or not.
        let views: Vec<FirstLevel> = (0..2)
            .map(|k| {
                let masks: [[F64; 3]; 4] = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
                let seed: [u8; 32] = if reuse || k == 0 {
                    first_seed
                } else {
                    std::array::from_fn(|_| rng.next_u8())
                };
                let proved = prove(
                    &circuit,
                    &index,
                    &index_committed.root,
                    &statement,
                    &cells,
                    &masks,
                    &seed,
                );
                let openings = open(proved.tables, &proved.claims, &index, &index_committed);
                // The observer's side: the reduction's verifier, then the witness opening's first level.
                let (roots, claims) =
                    verify(&index_committed.root, &statement, &proved.proof, circuit.log_rows).unwrap();
                let claims = [claims.witness];
                let fs = opening::seed(&roots[0], &claims);
                replay(&layout, &roots[0], &claims, &fs, &openings.witness)
            })
            .collect();
        let mut fits = vec![];
        for candidate in &candidates {
            // Per block lane: the opened rows less the candidate's codeword, across both proofs, against the
            // first piece's evaluations at those positions.
            let mut all = true;
            for l in (0..lanes).filter(|&l| matches!(layout.lane(l), Lane::Block(_))) {
                let mut points: Vec<(usize, F64)> = vec![];
                for view in &views {
                    let known = rows_at(&layout, candidate, &view.queries);
                    for ((&x, row), k) in view.queries.iter().zip(&view.rows).zip(&known) {
                        points.push((x, row[l] + k[l]));
                    }
                }
                points.sort_unstable_by_key(|p| p.0);
                points.dedup();
                let mut system: Vec<Vec<F64>> = points
                    .iter()
                    .map(|&(x, r)| [&column(s, x)[..piece], &[r][..]].concat())
                    .collect();
                let pivots = rref(&mut system, piece);
                let consistent = system[pivots.len()..].iter().all(|row| row[piece].is_zero());
                all &= consistent;
            }
            fits.push(all);
        }
        println!("seed reused: {reuse}; the secret bit {secret}; which candidates fit: {fits:?}");
        if reuse {
            assert_eq!(fits, [!secret, secret], "a reused seed confirms the witness");
        } else {
            assert_eq!(fits, [false, false], "fresh seeds: neither fits");
        }
    }
}

/// Two proofs that share the masks (fresh seeds): for a candidate witness, the first proof's `a_j` pin the masks,
/// and the second proof's `a_j` then match only for the true witness. From the proofs' scalars alone.
#[test]
fn reused_masks_confirm_the_witness() {
    use crate::protocol::{Index, prove};
    let mut rng = Rng::new(0x3A5C);
    let (circuit, inputs, statement) = two_witnesses();
    let index = Index::new(&circuit);
    let index_root = opening::commit(&index.table).root;
    let m = circuit.log_rows + 2;
    let candidates: Vec<Vec<F64>> = [false, true]
        .iter()
        .map(|&h| coefficients_of(&circuit.cells(&inputs(h))))
        .collect();
    for reuse in [true, false] {
        let secret = rng.bit();
        let cells = circuit.cells(&inputs(secret));
        let first_masks: [[F64; 3]; 4] = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
        let streams: Vec<Vec<F192>> = (0..2)
            .map(|k| {
                let masks = if reuse || k == 0 {
                    first_masks
                } else {
                    std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())))
                };
                let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
                prove(&circuit, &index, &index_root, &statement, &cells, &masks, &seed)
                    .proof
                    .stream
            })
            .collect();
        let fits: Vec<bool> = candidates
            .iter()
            .map(|w_hat| {
                let (mask, _) = pinned_masks(&circuit, &index_root, &statement, &streams[0], w_hat);
                let (_, digits) = pinned_masks(&circuit, &index_root, &statement, &streams[1], w_hat);
                (0..4).all(|j| {
                    let predicted = crate::domain::evaluate(w_hat, j, 4, &digits[2..m])
                        + digits[m] * crate::domain::evaluate(&mask, j, 4, &digits[2..4]);
                    predicted == streams[1][4 + j]
                })
            })
            .collect();
        println!("masks reused: {reuse}; the secret bit {secret}; which candidates fit: {fits:?}");
        if reuse {
            assert_eq!(fits, [!secret, secret], "reused masks confirm the witness");
        } else {
            assert_eq!(fits, [false, false], "fresh masks: neither fits");
        }
    }
}

/// Conditions (R) and (S) at every size `prove` takes (`2^17` to `2^22` rows), at the reduction's own claim
/// points, more draws than `rounds_are_free_at_full_size`.
#[test]
fn rounds_are_free_at_every_size() {
    use crate::hiding::{reduced_points, round_freedom};
    use crate::protocol::{quotient_layout, witness_layout};
    let mut rng = Rng::new(0xA11);
    for log_rows in 17..=22 {
        for draw in 0..8 {
            let (witness, quotient) = reduced_points(log_rows, 1000 * log_rows as u64 + draw);
            let phi = rng.ext_vec(LANE_FOLD);
            let lambdas = powers(rng.ext(), 2);
            let w = std::slice::from_ref(&witness);
            assert_eq!(
                round_freedom(&witness_layout(log_rows), w, &lambdas[..1], &phi, 200, &mut rng),
                (33, 3),
                "witness, 2^{log_rows} rows, draw {draw}"
            );
            assert_eq!(
                round_freedom(&quotient_layout(log_rows), &quotient, &lambdas, &phi, 200, &mut rng),
                (33, 3),
                "quotient, 2^{log_rows} rows, draw {draw}"
            );
        }
    }
}

/// A candidate's witness table as a hidden stack holds it in its block lanes (past their first piece, odd lanes'
/// pieces swapped in pairs), everything else zero: what an observer who knows the public layout can encode.
fn block_data_stack(layout: &Layout, w_hat: &[F64]) -> Vec<F64> {
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let lane = 1usize << log_lane;
    let piece = 1usize << layout.log_piece().unwrap();
    let mut stack = vec![F64::ZERO; layout.placed()];
    for l in 0..lanes {
        if let Lane::Block(b) = layout.lane(l) {
            for k in 1..lane / piece {
                let from = (b << log_lane) + (k ^ (l & 1)) * piece;
                if from + piece <= w_hat.len() {
                    stack[l * lane + k * piece..l * lane + (k + 1) * piece].copy_from_slice(&w_hat[from..from + piece]);
                }
            }
        }
    }
    stack
}

/// The other review's two attacks on the witness opening before the hidden layouts (commit 5ce4c95,
/// `crates/quotient/tests/review_opening_leaks.rs`: a `2^18`-row circuit, `x` secret, `y = H(x | 0x11..)` and
/// `leaf = H(x | 0x22..)` public), adapted to the hidden layout and asserting that they no longer distinguish.
///
/// (a) *The masks from the mask lane.* The twelve mask words now sit in the overflow lane, at the masks' piece,
///     plus the share `ρ`. Solving the overflow lane's opened words for the sixteen mask entries alone is
///     inconsistent; with the lane's random first piece as unknowns too (what it really holds), its 256 columns
///     already reach every value at the ≤ 225 opened positions, so the true masks and any other twelve words are
///     equally consistent: the masks, and so `g_j(w_2(t))`, stay hidden.
/// (b) *Coset fingerprints.* Per coset `a` of `H_lane` the old forms `Σ_b M[a][b]·row[b]` (now read at each
///     block's lane) match no prediction: neither from the coset's true cells, nor from the whole true witness,
///     nor from another witness's. What separates the observed forms from the true witness's prediction is
///     exactly the block lanes' random first pieces (checked with the prover's stack), uniform at the opened
///     positions; and the general check (each block lane's opened words, less a candidate's codeword, within
///     reach of a first piece) passes for every candidate alike.
#[test]
fn coset_fingerprints_and_mask_recovery_fail() {
    use crate::circuit::{Builder, Src, public_words};
    use crate::domain::{chain, point};
    use crate::hiding::rank;
    use crate::protocol::{Index, open, prove, verify, witness_layout};
    use crate::statement::{LEAF_PAD, Statement, Y_PAD, pair};
    const LOG_ROWS: usize = 18;
    let constant_block = |byte: u8| -> Vec<Src> {
        (0..256)
            .map(|i| {
                if (byte >> (i % 8)) & 1 == 1 {
                    Src::One
                } else {
                    Src::Zero
                }
            })
            .collect()
    };
    let circuit = {
        let mut b = Builder::new();
        let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
        let y = b.keccak256_64(&[&x[..], &constant_block(Y_PAD)].concat());
        let leaf = b.keccak256_64(&[&x[..], &constant_block(LEAF_PAD)].concat());
        b.finish(LOG_ROWS, &public_words(&y, &leaf))
    };
    let bits = |x: &[u8; 32]| -> Vec<bool> { (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect() };
    let m = LOG_ROWS + 2;
    let n = 1usize << m;
    let mut rng = Rng::new(0xA77);
    let index = Index::new(&circuit);
    let index_committed = opening::commit(&index.table);
    let index_root = index_committed.root;
    let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let statement = Statement {
        y: pair(&x, &[Y_PAD; 32]),
        root: pair(&x, &[LEAF_PAD; 32]),
    };
    let cells = circuit.cells(&bits(&x));
    let masks: [[F64; 3]; 4] = std::array::from_fn(|_| std::array::from_fn(|_| F64(rng.next_u64())));
    let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
    let proved = prove(&circuit, &index, &index_root, &statement, &cells, &masks, &seed);
    let prover_stack = proved.tables.witness.stack.clone();
    let proof = proved.proof.clone();
    let openings = open(proved.tables, &proved.claims, &index, &index_committed);

    // ---- Public data only from here (but for the check marked as the prover's).
    let (roots, claims) = verify(&index_root, &statement, &proof, LOG_ROWS).expect("an accepted proof");
    let layout = witness_layout(LOG_ROWS);
    let (lanes, log_lane) = (layout.lanes(), layout.log_lane());
    let lane = 1usize << log_lane;
    let s = layout.log_piece().unwrap();
    let piece = 1usize << s;
    let claims = [claims.witness];
    let fs = opening::seed(&roots[0], &claims);
    let view = replay(&layout, &roots[0], &claims, &fs, &openings.witness);
    let mut opened: Vec<(usize, Vec<F64>)> = view.queries.iter().copied().zip(view.rows.iter().cloned()).collect();
    opened.sort_by_key(|o| o.0);
    opened.dedup_by_key(|o| o.0);
    let positions: Vec<usize> = opened.iter().map(|o| o.0).collect();
    let first: Vec<Vec<F64>> = positions.iter().map(|&x| column(s, x)[..piece].to_vec()).collect();
    // Whether `A z = v` has a solution.
    let consistent = |a: &[Vec<F64>], v: &[F64]| -> bool {
        let cols = a[0].len();
        let mut system: Vec<Vec<F64>> = a.iter().zip(v).map(|(row, &x)| [&row[..], &[x]].concat()).collect();
        let pivots = rref(&mut system, cols);
        system[pivots.len()..].iter().all(|row| row[cols].is_zero())
    };

    // (a) The masks are the table's entries `n..n + 16`: the overflow lane's held piece for the table's piece
    // `n >> s`.
    let overflow = layout.overflow().unwrap();
    let held = 1 + layout
        .pieces()
        .iter()
        .position(|&p| p == n >> s)
        .expect("the masks' piece");
    let unit_rows: Vec<Vec<F64>> = (0..16)
        .map(|e| {
            let mut unit = vec![F64::ZERO; layout.placed()];
            unit[overflow * lane + held * piece + e] = F64::ONE;
            rows_at(&layout, &unit, &positions)
                .into_iter()
                .map(|r| r[overflow])
                .collect()
        })
        .collect();
    let observed: Vec<F64> = opened.iter().map(|o| o.1[overflow]).collect();
    let masks_alone: Vec<Vec<F64>> = (0..positions.len())
        .map(|p| (0..16).map(|e| unit_rows[e][p]).collect())
        .collect();
    assert!(
        !consistent(&masks_alone, &observed),
        "(a): the mask lane's words are no longer the masks' codeword"
    );
    let mut truth = [F64::ZERO; 16];
    for (j, coeffs) in masks.iter().enumerate() {
        for (i, &c) in coeffs.iter().enumerate() {
            truth[4 * i + j] = c;
        }
    }
    let mut wrong = truth;
    (0..12).for_each(|k| wrong[k] = F64(rng.next_u64()));
    assert_eq!(
        rank(first.clone()),
        positions.len(),
        "(a): the first piece reaches every opened value"
    );
    for candidate in [truth, wrong] {
        let rest: Vec<F64> = (0..positions.len())
            .map(|p| observed[p] + (0..16).fold(F64::ZERO, |acc, e| acc + candidate[e] * unit_rows[e][p]))
            .collect();
        assert!(
            consistent(&first, &rest),
            "(a): any twelve mask words are consistent with the opening"
        );
    }

    // (b) Coset fingerprints, each block read at its lane.
    let chunk_lanes = 1usize << (m - log_lane);
    let block_lane: Vec<usize> = (0..chunk_lanes)
        .map(|b| {
            (0..lanes)
                .find(|&l| layout.lane(l) == Lane::Block(b))
                .expect("a lane per block")
        })
        .collect();
    let basis_at = |a: usize| -> Vec<F64> {
        let w = chain(point(a << log_lane), m);
        (0..chunk_lanes)
            .map(|l| {
                (log_lane..m).fold(F64::ONE, |acc, k| {
                    if (l >> (k - log_lane)) & 1 == 1 {
                        acc * w[k]
                    } else {
                        acc
                    }
                })
            })
            .collect()
    };
    let forms = |a: usize, rows: &[Vec<F64>]| -> Vec<F64> {
        let ms = basis_at(a);
        rows.iter()
            .map(|row| (0..chunk_lanes).fold(F64::ZERO, |acc, b| acc + ms[b] * row[block_lane[b]]))
            .collect()
    };
    let observed_rows: Vec<Vec<F64>> = opened.iter().map(|o| o.1.clone()).collect();
    let predicted_rows = |values: &[F64]| -> Vec<Vec<F64>> {
        let mut w_hat = values.to_vec();
        crate::domain::coefficients(&mut w_hat, F64::ZERO);
        rows_at(&layout, &block_data_stack(&layout, &w_hat), &positions)
    };
    let x_other: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
    let other = circuit.cells(&bits(&x_other));
    let whole_truth = predicted_rows(&cells);
    let whole_other = predicted_rows(&other);
    // The prover's block lanes' first pieces alone, for the check of what separates the forms.
    let mut firsts = vec![F64::ZERO; layout.placed()];
    for &l in &block_lane {
        firsts[l * lane..l * lane + piece].copy_from_slice(&prover_stack[l * lane..l * lane + piece]);
    }
    let first_rows = rows_at(&layout, &firsts, &positions);
    let mut matches = [0usize; 3];
    for a in [3, 12, 20, 27] {
        let revealed = forms(a, &observed_rows);
        let mut coset_only = vec![F64::ZERO; n];
        coset_only[a << log_lane..(a + 1) << log_lane].copy_from_slice(&cells[a << log_lane..(a + 1) << log_lane]);
        let predictions = [
            forms(a, &predicted_rows(&coset_only)),
            forms(a, &whole_truth),
            forms(a, &whole_other),
        ];
        for (count, predicted) in matches.iter_mut().zip(&predictions) {
            *count += revealed.iter().zip(predicted).filter(|(r, p)| r == p).count();
        }
        let gap: Vec<F64> = revealed.iter().zip(&predictions[1]).map(|(&r, &p)| r + p).collect();
        assert_eq!(
            gap,
            forms(a, &first_rows),
            "(b): coset {a}: the forms differ by the first pieces' alone"
        );
    }
    assert_eq!(matches, [0, 0, 0], "(b): no coset form matches any prediction");
    // The general check, per block lane: within reach of a first piece, for every candidate alike.
    let fits: Vec<bool> = [&whole_truth, &whole_other]
        .iter()
        .map(|predicted| {
            block_lane.iter().all(|&l| {
                let residual: Vec<F64> = observed_rows
                    .iter()
                    .zip(predicted.iter())
                    .map(|(o, p)| o[l] + p[l])
                    .collect();
                consistent(&first, &residual)
            })
        })
        .collect();
    assert_eq!(
        fits,
        [true, true],
        "(b): the opened rows fit the true witness and another one alike"
    );
    println!(
        "{} distinct positions: (a) the masks' 16 columns alone are inconsistent, and with the first piece any \
         masks fit; (b) {} coset forms checked, 0 match (coset cells, whole witness, other witness), both \
         witnesses fit",
        positions.len(),
        4 * positions.len()
    );
}
