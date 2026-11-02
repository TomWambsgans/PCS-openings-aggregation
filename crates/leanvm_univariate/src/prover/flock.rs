// Part of this repository. The zerocheck, lincheck and slices are leanVM 42422001's Flock prover, unchanged
// (`crates/lv42_flock`, its `Blake2sSetup::prove_reduction_precomputed`), on its own witness buffers (dumped by
// `dump/trace_dump.rs`); the matrices' reduction follows `leanvm_flock_gas::flock_min`'s verifier (its `sliced` is that
// module's test's). MIT OR Apache-2.0; see NOTICE.md.
//! Flock's prover (SPEC.md §7), behind one call ([`prove`]): leanVM's zerocheck (its skip of 6), lincheck and 64
//! slices, written to the contract's Keccak-256 chain through [`Chain`]; then the matrices' reduction to `A0`, `B0`
//! claims (`k + 6` rounds and `a`, `b`) and the ring map's challenges, as `flock_min::verify` reads them.
//!
//! Only leanVM's skip is built (`FLOCK_LEANVM_SKIP`: skip 6, slices sent). (a′)'s skip of 3 needs another zerocheck
//! prover: leanVM's hard-codes its skip in its bit-sliced kernels.

use std::path::Path;

use leanvm_flock_gas::field::{E, ZERO};
use leanvm_flock_gas::flock::{blake2s_row_values, lagrange_weights};
use leanvm_flock_gas::flock_min::{PACKING, Slices, Variant};
use leanvm_flock_gas::layout::{BLAKE2S_R1CS_LOG_SIZE, FLOCK_NUM_LINCHECK_ROUNDS, K_BITS};
use leanvm_flock_gas::matrices::matrix_values;
use leanvm_flock_gas::multilinear::eq_kernel;
use leanvm_flock_gas::transcript::KeccakWriter;

/// The ring map's challenges (leanVM's `RING_MAP_SHIFTS`, six).
const RING_MAP_CHALLENGES: usize = 6;
/// leanVM's zerocheck's fixed coordinates.
const FIXED: usize = 7;

/// Flock's prover inputs, as leanVM's witness build leaves them.
pub struct FlockWitness {
    pub n_blocks: usize,
    pub z: Vec<u64>,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    pub z_lincheck: Vec<u8>,
}

impl FlockWitness {
    /// What `trace_dump.rs` wrote to `dir/flock.bin`.
    pub fn load(dir: &Path) -> std::io::Result<Self> {
        let meta = std::fs::read_to_string(dir.join("meta.txt"))?;
        let line = meta
            .lines()
            .find(|l| l.starts_with("flock "))
            .expect("meta.txt has Flock's inputs (dump them with the current trace_dump.rs)");
        let n: Vec<usize> = line.split_whitespace().skip(1).map(|x| x.parse().expect("a number")).collect();
        let bytes = std::fs::read(dir.join("flock.bin"))?;
        let words = |from: usize, len: usize| -> Vec<u64> {
            bytes[8 * from..8 * (from + len)]
                .as_chunks::<8>()
                .0
                .iter()
                .map(|w| u64::from_le_bytes(*w))
                .collect()
        };
        let (z, a, b) = (words(0, n[1]), words(n[1], n[2]), words(n[1] + n[2], n[3]));
        let at = 8 * (n[1] + n[2] + n[3]);
        Ok(Self {
            n_blocks: n[0],
            z,
            a,
            b,
            z_lincheck: bytes[at..at + n[4]].to_vec(),
        })
    }
}

/// The contract's chain as leanVM's flock prover's transcript: a scalar sent is 24 calldata bytes, a challenge one
/// Keccak-256 of the state and the bytes since the last; every challenge is kept, in order.
pub struct Chain<'a> {
    pub writer: &'a mut KeccakWriter,
    pub samples: Vec<E>,
}

impl lv42_fiat_shamir::transcript::Transcript for Chain<'_> {
    fn add_scalar(&mut self, x: lv42_primitives::field::F192) {
        self.writer.send(E::new(x.c0, x.c1, x.c2));
    }

    fn sample(&mut self) -> lv42_primitives::field::F192 {
        let e = self.writer.sample();
        self.samples.push(e);
        lv42_primitives::field::F192::new(e.c0, e.c1, e.c2)
    }
}

/// What Flock leaves: the slices' point and values, and the matrices' claim (`A0`, `B0` at `point`).
pub struct FlockOut {
    pub point: Vec<E>,
    pub slices: Vec<E>,
    pub matrices_point: Vec<E>,
    pub a: E,
    pub b: E,
}

/// `G'(x, y) = (Â0 + α B̂0)((x, low, chi_in), (y, chi_in'))` at index `x + 2^k y` (`flock_min`'s test's `sliced`).
fn sliced(k: usize, low: &[E], chi_in: &[E], chi_in_prime: &[E], alpha: E) -> Vec<E> {
    let high = eq_kernel(chi_in_prime);
    let rows = eq_kernel(&[low, chi_in].concat());
    let mut g = vec![ZERO; (1 << k) * K_BITS];
    for y in 0..K_BITS {
        let mut w = vec![ZERO; 1 << BLAKE2S_R1CS_LOG_SIZE];
        for (h, &weight) in high.iter().enumerate() {
            w[h * K_BITS + y] = weight;
        }
        let (left, right) = blake2s_row_values(&w);
        for (row, (&l, &r)) in left.iter().zip(&right).enumerate() {
            g[(row & ((1 << k) - 1)) + (y << k)] += rows[row >> k] * (l + alpha * r);
        }
    }
    g
}

/// `Σ_i Π_t tables[t][i]` by a sumcheck, low bit first, each variable of degree 2: messages `(c0, c2)`.
fn product_sum(writer: &mut KeccakWriter, mut tables: Vec<Vec<E>>, rounds: usize) -> Vec<E> {
    let mut point = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let half = tables[0].len() / 2;
        let mut coefficients = [ZERO; 4];
        for i in 0..half {
            let mut product = vec![E::new(1, 0, 0)];
            for table in &tables {
                let (lo, hi) = (table[2 * i], table[2 * i + 1]);
                let mut next = vec![ZERO; product.len() + 1];
                for (d, &p) in product.iter().enumerate() {
                    next[d] += p * lo;
                    next[d + 1] += p * (lo + hi);
                }
                product = next;
            }
            for (c, p) in coefficients.iter_mut().zip(&product) {
                *c += *p;
            }
        }
        assert_eq!(coefficients[3], ZERO, "degree 2 in every variable");
        writer.send(coefficients[0]);
        writer.send(coefficients[2]);
        let r = writer.sample();
        point.push(r);
        for table in &mut tables {
            for i in 0..half {
                let (lo, hi) = (table[2 * i], table[2 * i + 1]);
                table[i] = lo + r * (lo + hi);
            }
            table.truncate(half);
        }
    }
    point
}

/// Flock at `log_n = 14 + log(instances)` variables, written to `writer` as `flock_min::verify(log_n, variant)` reads
/// it.
pub fn prove(writer: &mut KeccakWriter, witness: &FlockWitness, variant: Variant, log_n: usize) -> Result<FlockOut, String> {
    let k = variant.skip;
    if k != PACKING || variant.slices != Slices::Weighted {
        return Err(format!(
            "Flock {variant:?}: only leanVM's skip of 6 with the slices sent (FLOCK_LEANVM_SKIP) has a prover"
        ));
    }
    lv42_parallel::init();
    let setup = lv42_flock::hash::Blake2sSetup::new(witness.n_blocks);
    if setup.m() != log_n {
        return Err(format!("Flock's witness has {} variables, the verifier's shape {log_n}", setup.m()));
    }
    let mut chain = Chain {
        writer: &mut *writer,
        samples: Vec::new(),
    };
    let claim = setup.prove_reduction_precomputed(&witness.z, &witness.a, &witness.b, &witness.z_lincheck, &mut chain);
    let samples = chain.samples;
    // The challenges, as the verifier draws them: the zerocheck's sampled eq coordinates, the skip's point, its
    // rounds', the lincheck's batching and rounds'.
    let n_r = log_n - k - FIXED;
    let rounds = log_n - k;
    if samples.len() != n_r + 1 + rounds + 1 + FLOCK_NUM_LINCHECK_ROUNDS {
        return Err(format!("Flock's prover drew {} challenges", samples.len()));
    }
    let z_skip = samples[n_r];
    let chi = &samples[n_r + 1..n_r + 1 + rounds];
    let alpha = samples[n_r + 1 + rounds];
    let lincheck = &samples[n_r + 2 + rounds..];
    let (row_low, rest) = chi.split_at(PACKING - k);
    let (chi_in, chi_rest) = rest.split_at(FLOCK_NUM_LINCHECK_ROUNDS);
    let chi_in_prime: Vec<E> = lincheck.iter().rev().copied().collect();
    let point: Vec<E> = [&chi_in_prime[..], chi_rest].concat();
    let theirs: Vec<E> = claim.suffix_point.iter().map(|x| E::new(x.c0, x.c1, x.c2)).collect();
    if theirs != point {
        return Err("Flock's slices are not at the point the verifier derives".into());
    }
    let slices: Vec<E> = claim.s_hat_v.iter().map(|x| E::new(x.c0, x.c1, x.c2)).collect();

    // The matrices' reduction: Σ_(x, y) L(x) s(y) G'(x, y) over the skip's k row bits and the 6 packing bits.
    let g = sliced(k, row_low, chi_in, &chi_in_prime, alpha);
    let skip = lagrange_weights(1 << k, z_skip);
    let size = (1 << k) * K_BITS;
    let skip_table: Vec<E> = (0..size).map(|i| skip[i % (1 << k)]).collect();
    let s_table: Vec<E> = (0..size).map(|i| slices[i >> k]).collect();
    let reduced = product_sum(writer, vec![g, skip_table, s_table], k + PACKING);
    let (rho, sigma) = reduced.split_at(k);
    let matrices_point = [rho, row_low, chi_in, sigma, &chi_in_prime[..]].concat();
    let (a, b) = matrix_values(&matrices_point).map_err(|e| format!("{e:?}"))?;
    writer.send(a);
    writer.send(b);
    // The ring map's challenges.
    for _ in 0..RING_MAP_CHALLENGES {
        writer.sample();
    }
    Ok(FlockOut {
        point,
        slices,
        matrices_point,
        a,
        b,
    })
}
