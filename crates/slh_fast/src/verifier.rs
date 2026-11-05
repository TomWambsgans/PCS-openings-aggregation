// Part of this repository. The quotient argument's identities at `t` (the row of `t`'s four cells, the copy
// identity, the public weight and its target, the gate's row polynomial) are crates/quotient/src/protocol.rs's
// `reduce_in` (itself adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation,
// commit 651453c6), stated here as relations on committed columns instead of normalised claims; Flock is
// leanvm_flock_gas's `flock_min` (from leanVM 42422001); the link, the stacks and the transcript's shape are new
// (crates/slh_dsa/SPEC-FAST.md). MIT OR Apache-2.0; see NOTICE.md.
//! π1's verifier, generic over the scalar it computes on (`E` with the Keccak-256 chain, or the recorder's symbol
//! for π2): from the stream to one point claim per stack.
//!
//! **The transcript** (§4.1):
//! 1. the seed binds the IV (the setup's root, the parameters, the layouts) and `PK ‖ M` ([`crate::seed`]);
//! 2. `C1`'s root → `α, β, γ` (the copy argument's challenges and the public words' combiner);
//! 3. Flock on `q_flock` (`flock_min::verify_walked_with`, the Keccak block's terminal `T`): its slices' point and
//!    the ring switch's map and target;
//! 4. `C2`'s root → `t`;
//! 5. five values at `t`: `A_j = Ŵ_j(w_2(t), …, w_(m-1)(t))`, `j < 4`, the multilinears of `W`'s `B` coefficients
//!    `4k + j` (a row's four cells' polynomials), and `σ(t)`;
//! 6. `ρ`, which builds `W`'s claim's point and combines each stack's relations;
//! 7. the batching sumcheck (`leanvm_univariate::verifier::batch`, π1-rec3's narrow pairs) → three point claims.
//!
//! **The relations** (all linear in the committed columns; nothing is inverted, so no hint is needed):
//! - `C1`: `Ŵ(ρ, ρ², w_2..w_(m-1)) = Σ_j eq((ρ, ρ²), j) A_j`;
//!   the link, `ℓ_q(t) + Q_link(t) Z(t) = W(t)` with `ℓ_q(t) = q̂_flock(y'_(0..7)(t), 0⁴, y'_(7..)(t))`;
//!   Flock's ring switch, `Φ(eq(p, ·))·q_flock = target`;
//! - `C2`: the copy identity `h(t) d d' + q(t) w_m(t) = d + d' + P(t) W(t) d d'`, the gate identity
//!   `q_gate(t) R(t) = gate(row of t)`, and the sum `Σ_(V_m) h = target(γ)` (the sum of `h`'s `B` coefficients:
//!   `SUM_TWIST`);
//! - setup: `σ̂(w(t)) = σ(t)`.

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::flock_min::{self, End, WalkedCircuit};
use leanvm_flock_gas::ring_tower;
use leanvm_flock_gas::scalar::{Scalar, enter};
use leanvm_flock_gas::transcript::Channel;
use leanvm_univariate::claims::{COMMITMENTS, Column, Combined, Commitment, Relations, Term, term};
use leanvm_univariate::domain::digits;
use leanvm_univariate::verifier::{Opening, RING_TWIST, SUM_TWIST, batch};
use primitives::field::F64;
use quotient::domain as qd;

use crate::{H, Params, REGION, SIGMA, W, copy_chunks, gate_chunks, layouts, link_chunks, q_copy, q_gate, q_link};

/// What the verifier states before the batching sumcheck: the two roots, each stack's relations combined by `ρ`,
/// and the ring switch's map (for its weight at the batch's point).
pub struct Front<S> {
    pub roots: [[S; 2]; 2],
    pub combined: Vec<(Commitment, Combined<S>)>,
    pub ring_map: Vec<S>,
    /// The relations stated, over the three stacks.
    pub relations: usize,
}

/// What the verifier leaves: the two roots and one point claim per stack (`C1`, `C2`, the setup), at one point.
pub struct Reduced<S> {
    pub roots: [[S; 2]; 2],
    pub openings: Vec<(Commitment, Opening<S>)>,
    pub relations: usize,
}

fn k(x: F64) -> E {
    E::new(x.0, 0, 0)
}

/// The weight of bit `j` of a public word of 128 bits (`crates/quotient`'s `bit_weight`): `x^j`, or `y x^(j-64)`.
fn bit_weight(j: usize) -> E {
    if j < 64 { E::new(1 << j, 0, 0) } else { E::new(0, 1 << (j - 64), 0) }
}

/// `1 + m_k` for coordinate `k < 8` of the public region (`crates/quotient`'s `coordinate_weight`): its weight's
/// factor is `1 + x_k (1 + m_k)`. Coordinates 8, 9, 10 are the word's, `γ`, `γ²`, `γ⁴`.
fn slope(k: usize) -> E {
    let one = E::new(1, 0, 0);
    match k {
        0 => one + bit_weight(1),
        1 => one,
        2..8 => one + bit_weight(1 << (k - 1)),
        _ => unreachable!("a word coordinate"),
    }
}

/// `Σ_c scale Π_(c' < c) w_(e_c') · Q_c(w_(<e_c))`: a quotient in chunks, `Q = Q_0 + w_(e_0) (Q_1 + w_(e_1) Q_2)`.
fn chunk_terms<S: Scalar>(column: impl Fn(usize) -> Column, sizes: &[usize], w: &[S], scale: S) -> Vec<Term<S>> {
    let mut factor = scale;
    let mut out = Vec::with_capacity(sizes.len());
    for (chunk, &e) in sizes.iter().enumerate() {
        out.push(term(column(chunk), &w[..e], factor));
        if chunk + 1 < sizes.len() {
            factor *= w[e];
        }
    }
    out
}

/// `y'_l = y_l + y_l(β_(m-1))`, `l < m - 1`: the port coset's coordinates, `y'_l(β_(m-1) + ω_j) = j_l`, from the
/// digits (`y_l = Σ_(i ≥ l) b_(i-l) w_i` on the span of `m - 1` basis vectors, `crates/quotient`'s
/// `domain::coordinates`). The constants `y_l(β_(m-1)) = Σ_i b_(i-l) β_(m-1-i)`.
pub fn port_coordinates<S: Scalar>(w: &[S], port_vars: usize) -> Vec<S> {
    let b = qd::coordinates(port_vars);
    let beta = qd::beta_ext();
    (0..port_vars)
        .map(|l| {
            let shift = (l..port_vars).fold(F64::ZERO, |acc, i| acc + b[i - l] * beta[port_vars - i]);
            (l + 1..port_vars).fold(w[l] + S::constant(k(shift)), |acc, i| acc + S::constant(k(b[i - l])) * w[i])
        })
        .collect()
}

/// `ℓ_q`'s point on `q_flock`'s words: the port word's 7 bits, the 4 bits of the block's other words at 0, the
/// block's bits.
pub fn port_point<S: Scalar>(y: &[S]) -> Vec<S> {
    let (word, block) = y.split_at(crate::PORT_WORD_BITS);
    let zeros = vec![S::zero(); crate::BLOCK_WORD_BITS - crate::PORT_WORD_BITS];
    [word, &zeros[..], block].concat()
}

/// The verifier up to the batching sumcheck: the stream through the values at `t` and `ρ`, and the relations
/// combined. With `expanded`, the ring switch's weight is its 64 twisted terms (what the prover's weights take, as
/// `leanvm_univariate`'s weighted mode), else one term of [`RING_TWIST`] (what the batch evaluates). `public` is
/// [`crate::public_words`], each word in a scalar's low limb.
pub fn front<S: Scalar + PartialEq, C: Channel<S>, T: WalkedCircuit>(
    p: &Params,
    public: [S; 8],
    channel: &mut C,
    expanded: bool,
) -> Result<Front<S>, VerifierError> {
    p.validate();
    let m = p.m();
    let one = S::one();
    let c = S::constant;

    // 2. C1, then the copy argument's challenges.
    let root1 = channel.next_root()?;
    let (alpha, beta, gamma) = (channel.sample(), channel.sample(), channel.sample());

    // 3. Flock on q_flock.
    let (flock_point, end) = flock_min::verify_walked_with::<S, T>(p.flock_log_n(), p.flock, channel)?;
    let End::Ring { map, target: ring_target, .. } = end else {
        unreachable!("the walked variant ends on the ring switch")
    };

    // 4. C2, then the point.
    let root2 = channel.next_root()?;
    let t = channel.sample();

    // 5. The values at t: the four row polynomials, the wiring.
    let a: Vec<S> = channel.next_scalars(4)?;
    let next = channel.next_scalar()?;

    // 6. ρ.
    let rho = channel.sample();

    let _phase = enter("quotient and link: the relations at t");
    let sizes = [link_chunks(p), copy_chunks(p), gate_chunks(p)];
    let top = sizes.iter().flatten().copied().max().expect("chunks").max(m);
    let w = digits(t, top + 1);

    // The four cells of the row of t (roles X, Y, C, V at t, t + 1, t + β_1, t + β_1 + 1): W(x) is the multilinear of
    // the A_j at (w_0(x), w_1(x)), and w_1(t + β_1) = w_1(t) + 1.
    let (s01, s02) = (a[0] + a[1], a[0] + a[2]);
    let s = s01 + a[2] + a[3];
    let cell = |u0: S, u1: S| a[0] + u0 * s01 + u1 * s02 + u0 * u1 * s;
    let theta = c(k(qd::beta()[1]));
    let (t1, w1) = (t + one, w[1] + one);
    let row = [cell(t, w[1]), cell(t1, w[1]), cell(t + theta, w1), cell(t1 + theta, w1)];
    let [x, y, cc, v] = row;
    let gate = v + x + cc + y * cc;

    // The public weight at t (the X and Y cells of the public rows; crates/quotient's), and the words' target: words
    // 0..4 the statement's halves, word 4 the constant 1, the rest zero.
    let gamma2 = gamma * gamma;
    let gammas = [gamma, gamma2, gamma2 * gamma2];
    let b = qd::coordinates(REGION);
    let mut weight = (REGION..m).fold(one, |acc, j| acc * (one + w[j]));
    for kk in 0..REGION {
        let coordinate = (kk + 1..REGION).fold(w[kk], |acc, j| acc + c(k(b[j - kk])) * w[j]);
        let factor = if kk < 8 { c(slope(kk)) } else { one + gammas[kk - 8] };
        weight *= one + coordinate * factor;
    }
    let y_limb = c(E::new(0, 1, 0));
    let half = |h: usize| public[2 * h + 1] + y_limb * public[2 * h];
    let target = half(0) + gamma * half(1) + gamma2 * (half(2) + gamma * half(3)) + gammas[2];

    let (d, d_next) = (alpha + x + beta * t, alpha + x + beta * next);
    let product = d * d_next;
    let copies = d + d_next + weight * x * product;
    let tau = qd::row_vanishing(m);
    let rows = (0..m - 1).fold(S::zero(), |acc, j| acc + c(k(tau[j])) * w[j]);

    // The link: ℓ_q(t) = q̂_flock at the port coset's coordinates of t; Z = w_(m-1) + 1 vanishes on the coset.
    let y_port = port_coordinates(&w, p.port_vars());
    let q_point = port_point(&y_port);
    let z = w[m - 1] + one;

    let mut relations = Relations::default();
    // C1.
    let rho2 = rho * rho;
    let w_point = [&[rho, rho2][..], &w[2..m]].concat();
    relations.push(vec![term(W, &w_point, one)], a[0] + rho * s01 + rho2 * s02 + rho * rho2 * s);
    let mut link = vec![term(Column::Qflock, &q_point, one)];
    link.extend(chunk_terms(q_link, &sizes[0], &w, z));
    relations.push(link, x);
    if expanded {
        let coefficients = ring_tower::coefficients(&map);
        relations.push(
            coefficients
                .iter()
                .enumerate()
                .map(|(twist, &coefficient)| Term {
                    column: Column::Qflock,
                    point: flock_point.clone(),
                    twist: twist as u8,
                    coefficient,
                })
                .collect(),
            ring_target,
        );
    } else {
        relations.push(
            vec![Term {
                column: Column::Qflock,
                point: flock_point.clone(),
                twist: RING_TWIST,
                coefficient: one,
            }],
            ring_target,
        );
    }
    // C2.
    let mut copy = vec![term(H, &w[..m], product)];
    copy.extend(chunk_terms(q_copy, &sizes[1], &w, w[m]));
    relations.push(copy, copies);
    relations.push(chunk_terms(q_gate, &sizes[2], &w, rows), gate);
    relations.push(
        vec![Term {
            column: H,
            point: w[..m].to_vec(),
            twist: SUM_TWIST,
            coefficient: one,
        }],
        target,
    );
    // The setup.
    relations.push(vec![term(SIGMA, &w[..m], one)], next);

    let combined = {
        let _phase = enter("claims: combination (powers of rho, merging)");
        COMMITMENTS
            .iter()
            .filter_map(|&commitment| relations.combine(commitment, rho).map(|claim| (commitment, claim)))
            .collect()
    };
    Ok(Front {
        roots: [root1, root2],
        combined,
        ring_map: map,
        relations: relations.list.len(),
    })
}

/// The verifier: [`front`], then the batching sumcheck over the three stacks to one point claim each.
pub fn reduce<S: Scalar + PartialEq, C: Channel<S>, T: WalkedCircuit>(
    p: &Params,
    public: [S; 8],
    channel: &mut C,
) -> Result<Reduced<S>, VerifierError> {
    let front = front::<S, C, T>(p, public, channel, false)?;
    let layouts = layouts(p);
    let (openings, _) = batch(channel, p.flock.fs, &front.combined, &layouts, None, Some(&front.ring_map), None)?;
    Ok(Reduced {
        roots: front.roots,
        openings,
        relations: front.relations,
    })
}
