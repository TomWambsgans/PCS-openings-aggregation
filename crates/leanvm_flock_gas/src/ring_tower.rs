// Part of this repository. The ring switch is leanVM's (https://github.com/leanEthereum/leanVM), commit 42422001, file
// crates/verifier/src/flock.rs: the 64 slices, a map `Φ` of six Frobenius stages drawn after them, the target
// `Σ_i x^i Φ(s_i)` and the weight `Φ(eq(p, ·))`. New here: the stages in tower order (shift 1 innermost, 32
// outermost), so that the target is computed through the subfields of `K` and the weight at a point from the inside
// out. MIT OR Apache-2.0; see NOTICE.md.
//! The ring switch with its map's stages in **tower order**: `Φ = Φ_5 ∘ … ∘ Φ_0`, `Φ_j(a) = a + f_j a^(2^(2^j))`.
//!
//! leanVM applies the shifts 32, 16, …, 1 in that order. Here stage `j` has shift `2^j` and is applied `j`-th, so the
//! outermost stage, `Φ_5`, is `F_5`-linear (`F_j = GF(2^(2^j)) ⊂ K`, `F_6 = K`), the next `F_4`-linear, and so on.
//!
//! **The target** `T = Σ_i x^i Φ(s_i)`. Write each coefficient over the tower, `c = c' + θ_j c''` with `c', c'' ∈ F_j`
//! (`θ_j ∈ F_(j+1) \ F_j`). Since `Φ_j` is `F_j`-linear, `Σ_i c_i Φ_j(u_i) = Φ_j(Σ_i c'_i u_i) + θ_j Φ_j(Σ_i c''_i u_i)`.
//! Down the six levels, the 64 coefficients `x^i` become `GF(2)` vectors: the leaves are 64 sums of slices (`XOR`s),
//! and the tree above them takes `6 · 64` squarings and `3 · 63` products, against leanVM's `64 · 63` squarings.
//!
//! **Soundness of the map.** If the slices differ from the true ones by `δ ≠ 0`, some leaf `Σ_i ε_(i,w) δ_i` is
//! nonzero (the leaves are the coordinates of `δ` in a basis). A node is `(A + θ B) + f_j (A^q + θ B^q)`, `q = |F_j|`,
//! with `A, B` its children: if `(A, B) ≠ 0` the two brackets are not both zero (else `(θ^q + θ) B^q = 0`, so
//! `B = A = 0`), so the node vanishes for at most one `f_j`. Along a path to a nonzero leaf, `T = 0` with probability
//! at most `6/|E|`, against leanVM's order's `2^31/|E|` by Schwartz–Zippel.
//!
//! **The weight** `W = Φ(eq(p, ·)) = Σ_(k<64) d_k eq(φ^k(p), ·)` at a point `r`: the 64 twisted eq products, then the
//! stages from the inside, `G_k ← G_k + f_j^(2^k) G_(k + 2^j)` for `k ≡ 0 mod 2^(j+1)`: 63 products and the chains
//! `f_j^(2^k)`, and no `d_k`.

use std::sync::OnceLock;

use crate::field::{E, GEN, ONE, ZERO};
use crate::layout::K_BITS;
use crate::scalar::Scalar;

/// The map's stages: stage `j` has shift `2^j`.
pub const STAGES: usize = 6;

fn frobenius<S: Scalar>(mut value: S, times: usize) -> S {
    for _ in 0..times {
        value = value.square();
    }
    value
}

/// `Φ(a)`, stage 0 first: `a ← a + f_j a^(2^(2^j))`.
pub fn ring_map<S: Scalar>(mut value: S, map: &[S]) -> S {
    assert_eq!(map.len(), STAGES);
    for (j, &f) in map.iter().enumerate() {
        value += f * frobenius(value, 1 << j);
    }
    value
}

/// The tower's constants: `θ_j`, and for each leaf `w` (its bit `j` set where level `j` took `θ_j`'s part) the slices
/// it sums, as a mask over `i`.
pub struct Tower {
    pub theta: [E; STAGES],
    pub leaves: [u64; K_BITS],
    /// The leaves as an `XOR` network: variable `64 + m` is `xors[m].0 + xors[m].1`, the slices being `0..64`.
    pub xors: Vec<(usize, usize)>,
    /// Each leaf, as the sum of these variables.
    pub sums: Vec<Vec<usize>>,
}

/// Paar's greedy common subexpressions: while some pair of variables occurs in two sums or more, the most frequent
/// pair (the first such) becomes a new variable. Rows are sets of variables, sorted.
fn xor_network(leaves: &[u64; K_BITS]) -> (Vec<(usize, usize)>, Vec<Vec<usize>>) {
    let mut rows: Vec<Vec<usize>> = leaves
        .iter()
        .map(|&mask| (0..K_BITS).filter(|&i| mask >> i & 1 == 1).collect())
        .collect();
    let mut xors = Vec::new();
    loop {
        let vars = K_BITS + xors.len();
        let mut count = vec![0u32; vars * vars];
        for row in &rows {
            for (x, &a) in row.iter().enumerate() {
                for &b in &row[x + 1..] {
                    count[a * vars + b] += 1;
                }
            }
        }
        let (best, &most) = count.iter().enumerate().max_by_key(|&(at, &c)| (c, std::cmp::Reverse(at))).unwrap();
        if most < 2 {
            break;
        }
        let (a, b) = (best / vars, best % vars);
        let new = vars;
        for row in rows.iter_mut() {
            if let (Ok(x), Ok(y)) = (row.binary_search(&a), row.binary_search(&b)) {
                row.remove(y.max(x));
                row.remove(y.min(x));
                row.push(new);
            }
        }
        xors.push((a, b));
    }
    (xors, rows)
}

/// `c^(|F_j|)`.
fn conjugate(c: E, j: usize) -> E {
    frobenius(c, 1 << j)
}

/// `e^((2^64 - 1) / (2^(2^(j+1)) - 1))`, an element of `F_(j+1)`.
fn into_subfield(e: E, j: usize) -> E {
    if j == STAGES - 1 { e } else { e.pow(u64::MAX / ((1u64 << (1 << (j + 1))) - 1)) }
}

impl Tower {
    fn new() -> Self {
        // θ_j = x^((2^64 - 1) / (2^(2^(j+1)) - 1)) generates F_(j+1)^* (x is primitive in K); θ_5 = x.
        Self::with_theta(std::array::from_fn(|j| into_subfield(GEN, j)))
    }

    fn leaves_of(theta: &[E; STAGES]) -> [u64; K_BITS] {
        for (j, &t) in theta.iter().enumerate() {
            assert_eq!(conjugate(t, j + 1), t, "θ_{j} lies in F_{}", j + 1);
            assert_ne!(conjugate(t, j), t, "θ_{j} is not in F_{j}");
        }
        let mut leaves = [0u64; K_BITS];
        for i in 0..K_BITS {
            // Decompose x^i from F_6 down: index bit j = 1 for the θ_j part.
            let mut parts = vec![GEN.pow(i as u64)];
            for j in (0..STAGES).rev() {
                let scale = (theta[j] + conjugate(theta[j], j)).inv();
                let mut next = vec![ZERO; 2 * parts.len()];
                for (w, &c) in parts.iter().enumerate() {
                    let second = (c + conjugate(c, j)) * scale;
                    let first = c + theta[j] * second;
                    debug_assert_eq!(conjugate(first, j), first);
                    next[2 * w] = first;
                    next[2 * w + 1] = second;
                }
                parts = next;
            }
            // Level 5's choice was taken first and is now bit 5, level 0's bit 0: `parts` is indexed by `w`.
            for (w, &bit) in parts.iter().enumerate() {
                assert!(bit == ZERO || bit == ONE, "a GF(2) coordinate");
                if bit == ONE {
                    leaves[w] |= 1 << i;
                }
            }
        }
        leaves
    }

    fn with_theta(theta: [E; STAGES]) -> Self {
        let leaves = Self::leaves_of(&theta);
        let (xors, sums) = xor_network(&leaves);
        Self {
            theta,
            leaves,
            xors,
            sums,
        }
    }

    /// `x^i = Σ_w ε_(i,w) Π_j θ_j^(w_j)`: the basis the leaves are coordinates in.
    pub fn basis(&self, w: usize) -> E {
        (0..STAGES).fold(ONE, |acc, j| if w >> j & 1 == 1 { acc * self.theta[j] } else { acc })
    }
}

pub fn tower() -> &'static Tower {
    static TOWER: OnceLock<Tower> = OnceLock::new();
    TOWER.get_or_init(Tower::new)
}

/// The ring switch's target `Σ_i x^i Φ(s_i)` by the tower: the 64 leaves (sums of slices), then six levels.
pub fn target<S: Scalar>(slices: &[S], map: &[S]) -> S {
    assert_eq!(slices.len(), K_BITS);
    let tower = tower();
    let mut vars = slices.to_vec();
    for &(a, b) in &tower.xors {
        vars.push(vars[a] + vars[b]);
    }
    let mut nodes: Vec<S> = tower
        .sums
        .iter()
        .map(|sum| sum.iter().fold(S::zero(), |acc, &v| acc + vars[v]))
        .collect();
    for (j, &f) in map.iter().enumerate() {
        let theta = S::constant(tower.theta[j]);
        nodes = nodes
            .chunks(2)
            .map(|pair| {
                let (a, b) = (pair[0], pair[1]);
                (a + theta * b) + f * (frobenius(a, 1 << j) + theta * frobenius(b, 1 << j))
            })
            .collect();
    }
    nodes[0]
}

/// `Φ = Σ_(k<64) d_k F^k`: `d_k = Π_(j: k_j = 1) f_j^(2^(k - k mod 2^(j+1)))`, each one product from `d_(k - 2^j)`,
/// `j` its lowest bit.
pub fn coefficients<S: Scalar>(map: &[S]) -> Vec<S> {
    assert_eq!(map.len(), STAGES);
    let mut d = vec![S::one(); K_BITS];
    for k in 1..K_BITS {
        let j = k.trailing_zeros() as usize;
        let exponent = k - k % (2 << j);
        d[k] = d[k - (1 << j)] * frobenius(map[j], exponent);
    }
    d
}

/// The weight `Φ(eq(p, ·))` at `r`, given `a_n = 1 + r_n` (so that each factor `1 + p_n^(2^k) + r_n` is one sum):
/// the twisted products `E_k = Π_n (a_n + p_n^(2^k))`, then the stages from the inside.
pub fn weight_at<S: Scalar>(point: &[S], one_plus_r: &[S], map: &[S]) -> S {
    assert_eq!(point.len(), one_plus_r.len());
    let mut chain = point.to_vec();
    let mut g: Vec<S> = Vec::with_capacity(K_BITS);
    for k in 0..K_BITS {
        if k > 0 {
            chain.iter_mut().for_each(|c| *c = c.square());
        }
        g.push(chain.iter().zip(one_plus_r).fold(S::one(), |acc, (&c, &a)| acc * (a + c)));
    }
    for (j, &f) in map.iter().enumerate() {
        let step = 1 << j;
        let mut power = f; // f_j^(2^k), k = 0, 2^(j+1), ...
        for k in (0..K_BITS).step_by(2 * step) {
            if k > 0 {
                power = frobenius(power, 2 * step);
            }
            g[k] = g[k] + power * g[k + step];
        }
    }
    g[0]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::multilinear::{eq_kernel, poly_eval};

    fn element(seed: &mut u64) -> E {
        let mut next = || {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        };
        E::new(next(), next(), next())
    }

    /// The leaves are the coordinates of `x^i` in the tower basis.
    #[test]
    fn the_leaves_are_the_tower_coordinates() {
        let tower = tower();
        for i in 0..K_BITS {
            let sum = (0..K_BITS)
                .filter(|&w| tower.leaves[w] >> i & 1 == 1)
                .fold(ZERO, |acc, w| acc + tower.basis(w));
            assert_eq!(sum, GEN.pow(i as u64), "x^{i}");
        }
        let ones: u32 = tower.leaves.iter().map(|m| m.count_ones()).sum();
        let xors = tower.xors.len() + tower.sums.iter().map(|s| s.len().saturating_sub(1)).sum::<usize>();
        println!("tower leaves: {ones} slice terms over 64 leaves; {xors} XORs in the network ({} shared)", tower.xors.len());
    }

    /// The coefficients are the map's, the target is `Σ_i x^i Φ(s_i)`, and the weight at a point is the twisted sum.
    #[test]
    fn target_coefficients_and_weight_are_the_maps() {
        let mut seed = 0x70e1_u64;
        let map: Vec<E> = (0..STAGES).map(|_| element(&mut seed)).collect();
        let d = coefficients(&map);
        for _ in 0..4 {
            let a = element(&mut seed);
            let sum = (0..K_BITS).fold(ZERO, |acc, k| acc + d[k] * frobenius(a, k));
            assert_eq!(sum, ring_map(a, &map));
        }
        let slices: Vec<E> = (0..K_BITS).map(|_| element(&mut seed)).collect();
        let images: Vec<E> = slices.iter().map(|&s| ring_map(s, &map)).collect();
        assert_eq!(target(&slices, &map), poly_eval(&images, GEN));
        let point: Vec<E> = (0..5).map(|_| element(&mut seed)).collect();
        let r: Vec<E> = (0..5).map(|_| element(&mut seed)).collect();
        let a: Vec<E> = r.iter().map(|&x| ONE + x).collect();
        let direct = (0..K_BITS).fold(ZERO, |acc, k| {
            let twisted: Vec<E> = point.iter().map(|&p| frobenius(p, k)).collect();
            acc + d[k] * crate::multilinear::eq_eval(&twisted, &r)
        });
        assert_eq!(weight_at(&point, &a, &map), direct);
    }

    /// The XOR network's size for other choices of `θ` (random elements of each `F_(j+1) \ F_j`):
    /// `cargo test --release -p leanvm_flock_gas --lib theta_search -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn theta_search() {
        let mut seed = 0x7e7a_u64;
        let size = |tower: &Tower| tower.xors.len() + tower.sums.iter().map(|s| s.len().saturating_sub(1)).sum::<usize>();
        let base = size(tower());
        let mut best: Vec<(u32, [E; STAGES])> = Vec::new();
        for _ in 0..400 {
            let theta: [E; STAGES] = std::array::from_fn(|j| loop {
                let t = into_subfield(E::new(element(&mut seed).c0, 0, 0), j);
                if conjugate(t, j) != t {
                    break t;
                }
            });
            let ones: u32 = Tower::leaves_of(&theta).iter().map(|m| m.count_ones()).sum();
            best.push((ones, theta));
        }
        best.sort_by_key(|(ones, _)| *ones);
        println!("x's θ: {base} XORs; the fewest slice terms among 400 random θ: {:?}", best.iter().take(5).map(|b| b.0).collect::<Vec<_>>());
        for (ones, theta) in best.iter().take(5) {
            let tower = Tower::with_theta(*theta);
            println!("  {ones} terms: {} XORs; θ = {:x?}", size(&tower), theta.map(|t| t.c0));
        }
    }

    /// The ring switch's identity on a packed table: `Σ_u Φ(eq(p, u)) q(u) = Σ_i x^i Φ(s_i)`, `s_i = ẑ(i, p)`.
    #[test]
    fn the_ring_switch_identity_holds() {
        let mut seed = 0xb175_u64;
        let vars = 4;
        let words: Vec<u64> = (0..1 << vars).map(|_| element(&mut seed).c0).collect();
        let point: Vec<E> = (0..vars).map(|_| element(&mut seed)).collect();
        let map: Vec<E> = (0..STAGES).map(|_| element(&mut seed)).collect();
        let eq = eq_kernel(&point);
        let slices: Vec<E> = (0..K_BITS)
            .map(|i| {
                words
                    .iter()
                    .zip(&eq)
                    .filter(|(w, _)| *w >> i & 1 == 1)
                    .fold(ZERO, |acc, (_, &e)| acc + e)
            })
            .collect();
        let claim = words
            .iter()
            .zip(&eq)
            .fold(ZERO, |acc, (&w, &e)| acc + ring_map(e, &map) * E::new(w, 0, 0));
        assert_eq!(target(&slices, &map), claim);
        // A slice changed changes the target.
        let mut other = slices.clone();
        other[9] += ONE;
        assert_ne!(target(&other, &map), claim);
    }
}
