// Part of this repository. The zerocheck, lincheck and slices are leanVM 42422001's Flock prover (`crates/lv42_flock`,
// its `Blake2sSetup::prove_reduction_precomputed`, unchanged, at leanVM's skip of 6; `prove_reduction_skip`, this
// repository's, below), on its own witness buffers (dumped by `dump/trace_dump.rs`); the matrices' reduction follows
// `leanvm_flock_gas::flock_min`'s verifier (its `sliced` is that module's test's). With π1-rec (`FsShape::Rec`) the
// zerocheck's eq point is the skip module's, as squares. MIT OR Apache-2.0; see NOTICE.md.
//! Flock's prover (SPEC.md §7), behind one call ([`prove`]): the zerocheck (a skip of 3 to 6), lincheck and 64
//! slices, written to the contract's Keccak-256 chain through [`Chain`]; then the matrices' reduction to `A0`, `B0`
//! claims (`k + 6` rounds and `a`, `b`) and the ring map's challenges, as `flock_min::verify` reads them; or, on the
//! point-claim ABI, the ring map's challenges at once and the matrices' reduction's tables ([`Pending`]) for the
//! batching sumcheck, as `flock_min::verify_deferred` reads them (SPEC.md §13, lever 4a).
//!
//! At a skip of 6 (`FLOCK_LEANVM_SKIP`) the zerocheck is leanVM's own; below (the main line's 3, `FLOCK_MAIN`), it is
//! `lv42_flock::zerocheck::skip`'s. The ring map's order (`Slices::Tower` or leanVM's) is the verifier's business:
//! the prover only draws its six challenges. With π1-rec (`FLOCK_REC`, the variant's `FsShape::Rec`) the zerocheck's
//! eq coordinates after the seven fixed ones are `c, c², c⁴, …` of one challenge (`EqPoint::Squares`), at any skip
//! the skip module's.

use std::path::Path;

use leanvm_flock_gas::field::{E, ZERO};
use leanvm_flock_gas::flock::{blake2s_row_values, lagrange_weights};
use leanvm_flock_gas::flock_min::{PACKING, Slices, Variant};
use leanvm_flock_gas::layout::{BLAKE2S_R1CS_LOG_SIZE, FLOCK_NUM_LINCHECK_ROUNDS, K_BITS};
use leanvm_flock_gas::matrices::matrix_values;
use leanvm_flock_gas::multilinear::eq_kernel;
use leanvm_flock_gas::transcript::{FsShape, KeccakWriter};
use lv42_flock::zerocheck::skip::EqPoint;

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

    /// The instances at the BLAKE2S rows' positions ([`super::trace::Trace::place`]): instance `i` to `to[i]` in
    /// `z`, `A z` and `B z` (blocks of `2^14` bits), and the lincheck's stripes rebuilt from `z`. Every instance
    /// satisfies the R1CS alone, so the witness stays one.
    pub fn place(&mut self, to: &[usize]) {
        assert_eq!(to.len() << 8, self.z.len(), "one instance a row");
        super::trace::permute_blocks(&mut self.z, to);
        super::trace::permute_blocks(&mut self.a, to);
        super::trace::permute_blocks(&mut self.b, to);
        // Stripe `g` byte `j` holds bit `j` of instances `8g..8g + 8`, bit `r` instance `8g + r`
        // (`lv42_flock::lincheck`'s layout): an 8×8 bit transpose of the eight instances' byte `j / 8`. Only the
        // stripes an instance moved into change.
        let block_words = 1usize << (BLAKE2S_R1CS_LOG_SIZE - 6);
        let stripe = 1usize << BLAKE2S_R1CS_LOG_SIZE;
        assert_eq!(self.z_lincheck.len(), (to.len() / 8) * stripe, "one stripe per eight instances");
        let mut changed = vec![false; to.len() / 8];
        for (i, &p) in to.iter().enumerate() {
            if p != i {
                changed[p / 8] = true;
            }
        }
        let z = &self.z;
        parallel::chunks_mut(&mut self.z_lincheck, stripe, |g, out| {
            if !changed[g] {
                return;
            }
            for byte in 0..stripe / 8 {
                let word = (0..8).fold(0u64, |w, r| {
                    let instance = &z[(8 * g + r) * block_words..(8 * g + r + 1) * block_words];
                    w | (instance[byte / 8] >> (8 * (byte % 8)) & 0xff) << (8 * r)
                });
                out[8 * byte..8 * byte + 8].copy_from_slice(&transpose_8x8(word).to_le_bytes());
            }
        });
    }
}

/// The 8×8 bit matrix whose byte `r` is row `r`, transposed: bit `8 r + c` to bit `8 c + r` (Hacker's Delight 7-3).
fn transpose_8x8(mut x: u64) -> u64 {
    let t = (x ^ (x >> 7)) & 0x00AA_00AA_00AA_00AA;
    x ^= t ^ (t << 7);
    let t = (x ^ (x >> 14)) & 0x0000_CCCC_0000_CCCC;
    x ^= t ^ (t << 14);
    let t = (x ^ (x >> 28)) & 0x0000_0000_F0F0_F0F0;
    x ^= t ^ (t << 28);
    x
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

/// What Flock leaves: the slices' point and values, where the stream stood after them, and the matrices' reduction,
/// done (its claim on `A0`, `B0`) or left to the batching sumcheck (SPEC.md §13, lever 4a).
pub struct FlockOut {
    pub point: Vec<E>,
    pub slices: Vec<E>,
    /// The stream's length right after the slices.
    pub slices_end: usize,
    pub matrices: Matrices,
    /// The zerocheck and the lincheck's seconds (the rest of Flock's phase is the matrices' tables).
    pub reduction_secs: f64,
}

pub enum Matrices {
    /// Its `k + 6` rounds and `a`, `b` sent after the slices: the claim `A0`, `B0` at `point`.
    Done { point: Vec<E>, a: E, b: E },
    /// Its sum `Σ_(x, y) G'(x, y) L̂(x) ŝ(y)`, run by the batching sumcheck.
    Pending(Pending),
    /// None: the verifier walks the circuit (π1-rec2, `Slices::TowerWalk`).
    Walked,
}

/// The matrices' reduction left to the batching sumcheck: its three tables over the skip's `k` row bits (low) and the
/// column's 6 packing bits, and what its claim's point is made of.
pub struct Pending {
    pub k: usize,
    /// `G'`, the skip's Lagrange weights `L̂` and the slices `ŝ`, at index `x + 2^k y`.
    pub tables: [Vec<E>; 3],
    row_low: Vec<E>,
    chi_in: Vec<E>,
    chi_in_prime: Vec<E>,
}

impl Pending {
    /// The sum's variables: the batching sumcheck's first ones.
    pub fn rounds(&self) -> usize {
        self.k + PACKING
    }

    /// The claim on `A0`, `B0`: at `(ρ, row_low, chi_in, σ, chi_in')`, `(ρ, σ)` the batch point's first coordinates.
    pub fn claim(&self, batch_point: &[E]) -> Result<(Vec<E>, E, E), String> {
        let (rho, sigma) = batch_point[..self.rounds()].split_at(self.k);
        let point = [rho, &self.row_low, &self.chi_in, sigma, &self.chi_in_prime].concat();
        let (a, b) = matrix_values(&point).map_err(|e| format!("{e:?}"))?;
        Ok((point, a, b))
    }
}

/// `G'(x, y) = (Â0 + α B̂0)((x, low, chi_in), (y, chi_in'))` at index `x + 2^k y` (`flock_min`'s test's `sliced`).
fn sliced(k: usize, low: &[E], chi_in: &[E], chi_in_prime: &[E], alpha: E) -> Vec<E> {
    let high = eq_kernel(chi_in_prime);
    let rows = eq_kernel(&[low, chi_in].concat());
    // One walk of the circuit per packing position y, in parallel.
    let columns: Vec<Vec<E>> = parallel::map_collect(K_BITS, |y| {
        let mut w = vec![ZERO; 1 << BLAKE2S_R1CS_LOG_SIZE];
        for (h, &weight) in high.iter().enumerate() {
            w[h * K_BITS + y] = weight;
        }
        let (left, right) = blake2s_row_values(&w);
        let mut column = vec![ZERO; 1 << k];
        for (row, (&l, &r)) in left.iter().zip(&right).enumerate() {
            column[row & ((1 << k) - 1)] += rows[row >> k] * (l + alpha * r);
        }
        column
    });
    let mut g = vec![ZERO; (1 << k) * K_BITS];
    for (y, column) in columns.into_iter().enumerate() {
        g[y << k..(y + 1) << k].copy_from_slice(&column);
    }
    g
}

/// `Σ_i Π_t tables[t][i]` by a sumcheck, low bit first, each variable of degree 2: messages `(c0, c2)`.
fn product_sum(writer: &mut KeccakWriter, tables: Vec<Vec<E>>, rounds: usize) -> Vec<E> {
    product_rounds(tables, rounds, |c0, c2| {
        writer.send(c0);
        writer.send(c2);
        writer.sample()
    })
}

impl Pending {
    /// The matrices' reduction run on its own, as the verifier's weighted mode reads it (`flock_min::verify`), at the
    /// given round challenges instead of the chain's: its `k + 6` rounds' messages, then `a`, `b`. What
    /// [`super::replay::Replay`] serves where the point-claim stream has none (its challenges outside the chain), so
    /// that weighted mode's claims are an honest prover's.
    pub fn off_chain(&self, challenges: &[E]) -> Result<Vec<E>, String> {
        assert_eq!(challenges.len(), self.rounds());
        let mut messages = Vec::with_capacity(2 * self.rounds() + 2);
        let mut next = challenges.iter();
        let point = product_rounds(self.tables.to_vec(), self.rounds(), |c0, c2| {
            messages.extend([c0, c2]);
            *next.next().expect("a challenge a round")
        });
        let (_, a, b) = self.claim(&point)?;
        messages.extend([a, b]);
        Ok(messages)
    }
}

/// The product sum's rounds, each message `(c0, c2)` handed to `round`, which returns the round's challenge.
fn product_rounds(mut tables: Vec<Vec<E>>, rounds: usize, mut round: impl FnMut(E, E) -> E) -> Vec<E> {
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
        let r = round(coefficients[0], coefficients[2]);
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
/// it, or as `flock_min::verify_deferred` does when `deferred` (the matrices' reduction left to the batching sumcheck).
pub fn prove(
    writer: &mut KeccakWriter,
    witness: &FlockWitness,
    variant: Variant,
    log_n: usize,
    deferred: bool,
) -> Result<FlockOut, String> {
    let k = variant.skip;
    if !(lv42_flock::zerocheck::skip::MIN_SKIP..=PACKING).contains(&k) {
        return Err(format!("Flock {variant:?}: a prover for a skip of 3 to 6"));
    }
    let sent = variant.slices != Slices::Claim;
    lv42_parallel::init();
    let setup = lv42_flock::hash::Blake2sSetup::new(witness.n_blocks);
    if setup.m() != log_n {
        return Err(format!("Flock's witness has {} variables, the verifier's shape {log_n}", setup.m()));
    }
    let mut chain = Chain {
        writer: &mut *writer,
        samples: Vec::new(),
    };
    // leanVM's own prover at a skip of 6 (with leanVM's eq point); the skip module's zerocheck and the lincheck at its
    // row weights otherwise.
    let eq = match variant.fs {
        FsShape::Main => EqPoint::Sampled,
        FsShape::Rec => EqPoint::Squares,
    };
    let started = std::time::Instant::now();
    let claim = setup.prove_reduction_skip(k, eq, &witness.z, &witness.a, &witness.b, &witness.z_lincheck, &mut chain);
    let samples = chain.samples;
    // The challenges, as the verifier draws them: the zerocheck's sampled eq coordinates (with π1-rec only the first,
    // the others its squares), the skip's point, its rounds', the lincheck's batching and rounds'.
    let n_r = match eq {
        EqPoint::Sampled => log_n - k - FIXED,
        EqPoint::Squares => usize::from(log_n > k + FIXED),
    };
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
    if !sent {
        // Extension B (`Slices::Claim`): the lincheck's slices, its last 64 scalars, are not sent; nothing was drawn
        // since, so the chain has not absorbed them.
        let len = writer.stream.len() - 24 * K_BITS;
        writer.stream.truncate(len);
    }
    let slices_end = writer.stream.len();

    let reduction_secs = started.elapsed().as_secs_f64();
    // π1-rec2: the verifier checks the lincheck's terminal by walking the circuit; nothing more is sent before the
    // ring map's challenges.
    if variant.slices == Slices::TowerWalk {
        for _ in 0..RING_MAP_CHALLENGES {
            writer.sample();
        }
        return Ok(FlockOut {
            point,
            slices,
            slices_end,
            matrices: Matrices::Walked,
            reduction_secs,
        });
    }
    // The matrices' reduction: Σ_(x, y) L(x) s(y) G'(x, y) over the skip's k row bits and the 6 packing bits.
    let g = sliced(k, row_low, chi_in, &chi_in_prime, alpha);
    let skip = lagrange_weights(1 << k, z_skip);
    let size = (1 << k) * K_BITS;
    let skip_table: Vec<E> = (0..size).map(|i| skip[i % (1 << k)]).collect();
    let s_table: Vec<E> = (0..size).map(|i| slices[i >> k]).collect();
    let pending = Pending {
        k,
        tables: [g, skip_table, s_table],
        row_low: row_low.to_vec(),
        chi_in: chi_in.to_vec(),
        chi_in_prime,
    };
    let matrices = if deferred {
        Matrices::Pending(pending)
    } else {
        let reduced = product_sum(writer, pending.tables.to_vec(), k + PACKING);
        let (point, a, b) = pending.claim(&reduced)?;
        writer.send(a);
        writer.send(b);
        Matrices::Done { point, a, b }
    };
    // The ring map's challenges, if the slices were sent (without them there is no ring switch here).
    if sent {
        for _ in 0..RING_MAP_CHALLENGES {
            writer.sample();
        }
    }
    Ok(FlockOut {
        point,
        slices,
        slices_end,
        matrices,
        reduction_secs,
    })
}
