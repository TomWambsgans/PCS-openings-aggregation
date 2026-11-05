// Part of this repository. The sum `h` and the two quotients `q`, `q_gate` are computed as in crates/quotient/src/
// protocol.rs's prover (adapted there from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6), without the masks (no zero knowledge here); the link's quotient is new
// (crates/slh_dsa/SPEC-FAST.md §4.5), its shifted cubes crates/quotient's `ntt::shifted_cube`. MIT OR Apache-2.0;
// see NOTICE.md.
//! The prover's polynomials of `C1`'s link and `C2`, as novel coefficients (`crates/quotient`'s basis
//! `X_k = Π_(l ∈ k) w_l`).

use primitives::field::{F64, F192};
use quotient::domain::{self, beta_ext, chain, coordinates, point, row_vanishing};
use quotient::ntt;

use crate::{Params, REGION};

/// The copy argument's polynomials: `h` (its sum over `V_m` the public words' combination) and the two quotients.
pub struct CopyGate {
    pub h: Vec<F192>,
    /// `Σ_(V_m) h`, what the verifier's target must be.
    pub sum: F192,
    pub q: Vec<F192>,
    pub q_gate: Vec<F64>,
    /// Whether both quotients are polynomials of the degrees the verifier declares (they are, for a witness).
    pub fits: bool,
}

fn batch_inverse(values: &mut [F192]) {
    let mut prefix = Vec::with_capacity(values.len());
    let mut acc = F192::ONE;
    for &v in values.iter() {
        prefix.push(acc);
        acc *= v;
    }
    let mut inverse = acc.inv();
    for (v, p) in values.iter_mut().zip(prefix).rev() {
        let next = inverse * *v;
        *v = inverse * p;
        inverse = next;
    }
}

/// The weight of a cell of the public region: `γ^word` times its bit's, or zero off the `X` and `Y` cells.
fn public_weight(cell: usize, gamma: F192) -> F192 {
    if cell & 2 != 0 {
        return F192::ZERO;
    }
    let (j, word) = ((cell & 1) | ((cell >> 2) & 63) << 1, cell >> 8);
    let bit = if j < 64 { F192::new(1 << j, 0, 0) } else { F192::new(0, 1 << (j - 64), 0) };
    (0..word).fold(bit, |acc, _| acc * gamma)
}

/// `1 + m_k` of the public region's coordinate `k < 8` (`crates/quotient`'s `coordinate_weight`; the verifier's
/// `slope`).
fn slope_k(k: usize) -> F192 {
    let bit = |j: usize| if j < 64 { F192::new(1 << j, 0, 0) } else { F192::new(0, 1 << (j - 64), 0) };
    match k {
        0 => F192::ONE + bit(1),
        1 => F192::ONE,
        2..8 => F192::ONE + bit(1 << (k - 1)),
        _ => unreachable!("a word coordinate"),
    }
}

fn gate(row: [F64; 4]) -> F64 {
    let [x, y, c, v] = row;
    v + x + c + y * c
}

/// `h`, `q` and `q_gate` from the cells, the wiring (`sigma` each cell's successor, `sigma_novel` its polynomial's
/// coefficients), `W`'s coefficients and the challenges.
pub fn copy_and_gate(
    p: &Params,
    cells: &[F64],
    sigma: &[u32],
    sigma_novel: &[F64],
    w_novel: &[F64],
    [alpha, beta, gamma]: [F192; 3],
) -> CopyGate {
    let m = p.m();
    let n = 1usize << m;
    assert_eq!(cells.len(), n);

    // h on the cells: 1/d + 1/d' (and the public weight on the region), then its coefficients.
    let mut h = vec![F192::ZERO; n];
    parallel::chunks_mut(&mut h, 1 << 12, |chunk_index, chunk| {
        let base = chunk_index << 12;
        let mut d: Vec<F192> = (0..chunk.len())
            .flat_map(|k| {
                let i = base + k;
                let common = alpha + F192::from(cells[i]);
                [point(i), point(sigma[i] as usize)].map(|to| common + beta.mul_base(to))
            })
            .collect();
        batch_inverse(&mut d);
        for (k, out) in chunk.iter_mut().enumerate() {
            *out = d[2 * k] + d[2 * k + 1];
            if base + k < 1 << REGION {
                *out += public_weight(base + k, gamma).mul_base(cells[base + k]);
            }
        }
    });
    let sum = parallel::map_reduce(n >> 12, || F192::ZERO, |c| h[c << 12..(c + 1) << 12].iter().fold(F192::ZERO, |a, &x| a + x), |a, b| a + b);
    domain::coefficients(&mut h, F64::ZERO);

    // Both quotients, on the coset ω_(4n) + V_(m+2).
    let big = 4 * n;
    let offset = beta_ext()[m + 2];
    let offsets = chain(offset, m + 1);
    let mut w_values = vec![F64::ZERO; big];
    w_values[..n].copy_from_slice(w_novel);
    ntt::values(&mut w_values, offset);
    let mut sigma_values = vec![F64::ZERO; big];
    sigma_values[..n].copy_from_slice(sigma_novel);
    ntt::values(&mut sigma_values, offset);
    let mut q = vec![F192::ZERO; big];
    q[..n].copy_from_slice(&h);
    domain::values(&mut q, offset);
    let mut q_gate = vec![F64::ZERO; big];

    let (b, tau) = (coordinates(REGION), row_vanishing(m));
    let row_poly = |x: F64| chain(x, m - 1).iter().zip(&tau).fold(F64::ZERO, |acc, (&w, &t)| acc + t * w);
    let row_low: [F64; 4] = std::array::from_fn(|c| row_poly(point(c)));
    let gammas = [gamma, gamma * gamma, (gamma * gamma) * (gamma * gamma)];
    parallel::chunks_mut2(&mut q, &mut q_gate, 1 << REGION, |high, q, q_gate| {
        let base = high << REGION;
        let w_at = |k: usize| offsets[k] + point(base >> k);
        // The public weight on this block: its region coordinates are the low index's bits, shifted.
        let indicator = (REGION..m).fold(F64::ONE, |acc, k| acc * (F64::ONE + w_at(k)));
        let mut weights = vec![F192::from(indicator)];
        if !indicator.is_zero() {
            for k in 0..REGION {
                let shift = (k..REGION).fold(F64::ZERO, |acc, j| acc + b[j - k] * w_at(j));
                let slope = if k < 8 { slope_k(k) } else { F192::ONE + gammas[k - 8] };
                let low = F192::ONE + slope.mul_base(shift);
                for i in 0..weights.len() {
                    weights.push(weights[i] * (low + slope));
                    weights[i] *= low;
                }
            }
        }
        let cell_vanishing = w_at(m).inv();
        let row_base = row_poly(offset + point(base));
        let row_vanishing: [F64; 4] = std::array::from_fn(|c| (row_base + row_low[c]).inv());
        for (low, (q, q_gate)) in q.iter_mut().zip(q_gate.iter_mut()).enumerate() {
            let i = base + low;
            let w = w_values[i];
            let common = alpha + F192::from(w);
            let d = common + beta.mul_base(offset + point(i));
            let d_next = common + beta.mul_base(sigma_values[i]);
            let public = weights.get(low).map_or(F192::ZERO, |weight| weight.mul_base(w));
            *q = ((*q + public) * d * d_next + d + d_next).mul_base(cell_vanishing);
            let row = [w, w_values[i ^ 1], w_values[i ^ 2], w_values[i ^ 3]];
            *q_gate = gate(row) * row_vanishing[low & 3];
        }
    });
    domain::coefficients(&mut q, offset);
    ntt::coefficients(&mut q_gate, offset);
    let (copy, gates) = (p.copy_count() as usize, p.gate_count() as usize);
    let fits = q[copy..].iter().all(|v| v.is_zero()) && q_gate[gates..].iter().all(|v| v.is_zero());
    q.truncate(copy);
    q_gate.truncate(gates);
    CopyGate {
        h,
        sum,
        q,
        q_gate,
        fits,
    }
}

/// `q_flock`'s port words as a table of the port region's `2^(m-1)` cells: cell `j` is the word `j mod 2^7` of
/// block `j >> 7`.
pub fn port_table(p: &Params, qflock: &[F64]) -> Vec<F64> {
    let low = (1 << crate::PORT_WORD_BITS) - 1;
    parallel::map_collect(1 << p.port_vars(), |j| {
        qflock[(j & low) | (j >> crate::PORT_WORD_BITS) << crate::BLOCK_WORD_BITS]
    })
}

/// The link's quotient `Q_link = (W + ℓ_q) / Z` (§4.5), `ℓ_q(x) = q̂_port(y'(x))`, `Z = w_(m-1) + 1`: on the coset
/// `ω_D + V_D` of the least power of two `D ≥ 2^m` past its degree, in pieces of `2^(m-1)` points, on each of which
/// `y'` is a shifted cube and `Z` a constant. Returns its coefficients (`link_count` of them) and whether it is a
/// polynomial of that degree (it is, when the ports are `q_flock`'s).
pub fn link_quotient(p: &Params, w_novel: &[F64], port: &[F64]) -> (Vec<F64>, bool) {
    let (m, pv) = (p.m(), p.port_vars());
    assert_eq!(port.len(), 1 << pv);
    let count = p.link_count() as usize;
    let log_d = (count.next_power_of_two().trailing_zeros() as usize).max(m);
    let size = 1usize << log_d;
    let offset = point(size);
    let mut values = vec![F64::ZERO; size];
    values[..w_novel.len()].copy_from_slice(w_novel);
    ntt::values(&mut values, offset);
    let b = coordinates(pv);
    let beta = beta_ext();
    let shifts: Vec<F64> = (0..pv)
        .map(|l| (l..pv).fold(F64::ZERO, |acc, i| acc + b[i - l] * beta[pv - i]))
        .collect();
    // The pieces one after the other (the shifted cube and the products are parallel within one).
    for (piece, out) in values.chunks_mut(1 << pv).enumerate() {
        let first = size + (piece << pv);
        let digits = chain(point(first), pv);
        let delta: Vec<F64> = (0..pv)
            .map(|l| (l..pv).fold(shifts[l], |acc, i| acc + b[i - l] * digits[i]))
            .collect();
        let cube = ntt::shifted_cube(port, &delta, pv);
        let z_inverse = (point(first >> pv) + F64::ONE).inv();
        parallel::chunks_mut(out, 1 << 14, |c, out| {
            for (o, &l) in out.iter_mut().zip(&cube[c << 14..]) {
                *o = (*o + l) * z_inverse;
            }
        });
    }
    ntt::coefficients(&mut values, offset);
    let fits = values[count..].iter().all(|v| v.is_zero());
    values.truncate(count);
    (values, fits)
}
