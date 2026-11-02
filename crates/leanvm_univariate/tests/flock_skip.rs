// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The zerocheck with a univariate skip of 3 to 6 (`lv42_flock::zerocheck::skip`) and Flock's prover on it
//! (`prover::flock`), without a trace:
//!
//! - at a skip of 6, the skip module's round 1 and whole zerocheck write what leanVM's own do, byte for byte;
//! - at skips of 3, 4 and 5, on honest witnesses, the zerocheck's stream is accepted (its rounds re-checked with the
//!   verifier's sumcheck), and its three claims are the witness's evaluations at the point;
//! - Flock end to end on BLAKE2s compressions (128 of them, `log_n = 21`): `flock_min::verify` accepts the stream at
//!   skips of 3 to 6, both ring-map orders, and the 64 slices are the witness's at the verifier's point.
//!
//! `cargo test --release -p leanvm_univariate --test flock_skip -- --nocapture`

use leanvm_flock_gas::field::E;
use leanvm_flock_gas::flock_min::{self, Slices, Variant};
use leanvm_flock_gas::transcript::{Checks, KeccakChannel, KeccakWriter, keccak_seed, sumcheck};
use leanvm_univariate::prover::flock::{Chain, FlockWitness, prove};
use lv42_flock::zerocheck::skip::{prove_skip, round1};
use lv42_flock::zerocheck::univariate_skip_optimized::{
    c_s, medium_challenges, round1_shift_reduce_extract_c_packed_padded, small_challenges,
};
use lv42_flock::zerocheck::{PaddingSpec, prove_packed_padded};
use lv42_primitives::field::{F8, F192};
use lv42_primitives::multilinear::{eq_table, lagrange_weights_naive};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn ext(&mut self) -> F192 {
        F192::new(self.next(), self.next(), self.next())
    }
}

fn to_e(x: F192) -> E {
    E::new(x.c0, x.c1, x.c2)
}

fn from_e(x: E) -> F192 {
    F192::new(x.c0, x.c1, x.c2)
}

/// An honest zerocheck witness: `c = a AND b`, bit `i` at byte `i / 8`, bit `i % 8`; a block's tail zero, as the
/// padding spec says.
fn witness(m: usize, padding: &PaddingSpec, rng: &mut Rng) -> [Vec<u8>; 3] {
    let bytes = (1usize << m) / 8;
    let mut a: Vec<u8> = (0..bytes).map(|_| rng.next() as u8).collect();
    let mut b: Vec<u8> = (0..bytes).map(|_| rng.next() as u8).collect();
    for bit in 0..1usize << m {
        if bit % (1 << padding.k_log) >= padding.useful_bits_per_block {
            a[bit / 8] &= !(1 << (bit % 8));
            b[bit / 8] &= !(1 << (bit % 8));
        }
    }
    let c: Vec<u8> = a.iter().zip(&b).map(|(&x, &y)| x & y).collect();
    [a, b, c]
}

/// `f̂(z, chi)`: the skip's Lagrange weights at `z` on the low `k` bits, eq at `chi` on the rest.
fn quirky(bits: &[u8], k: usize, z: F192, chi: &[F192]) -> F192 {
    let weights = lagrange_weights_naive(k, z);
    let eq = eq_table(chi);
    let mut acc = F192::ZERO;
    for (x, &e) in eq.iter().enumerate() {
        let mut inner = F192::ZERO;
        for (s, &w) in weights.iter().enumerate() {
            let i = (x << k) | s;
            if bits[i / 8] >> (i % 8) & 1 == 1 {
                inner += w;
            }
        }
        acc += e * inner;
    }
    acc
}

/// At a skip of 6, round 1 is leanVM's optimized kernel's message (times its `C_s`).
#[test]
fn round1_at_six_is_leanvms() {
    let mut rng = Rng(0x5eed_0001);
    for m in [14usize, 15, 17] {
        let padding = PaddingSpec {
            k_log: 14,
            useful_bits_per_block: 16_000,
        };
        let [a, b, c] = witness(m, &padding, &mut rng);
        let r_rest: Vec<F192> = small_challenges()
            .into_iter()
            .chain(medium_challenges())
            .chain((0..m - 6 - 7).map(|_| rng.ext()))
            .collect();
        let ntt_s = lv42_pcs::ntt::AdditiveNttGf8::new(6, F8::ZERO);
        let ntt_l = lv42_pcs::ntt::AdditiveNttGf8::new(6, F8(64));
        let table = lv42_pcs::ntt::InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
        let (ab, cc) = round1_shift_reduce_extract_c_packed_padded(&a, &b, &c, m, 6, &r_rest, &table, &padding);
        let theirs: Vec<F192> = ab.iter().zip(&cc).map(|(&x, &y)| c_s() * (x + y)).collect();
        assert_eq!(round1(&a, &b, &c, m, 6, &r_rest), theirs, "m = {m}");
    }
}

/// `BitFold` at every row width, 1 to 128 bytes (GFNI where the build has it), full and short blocks, against the
/// definition: the sum of the weights of the set bits.
#[test]
fn bit_fold_at_every_row_width() {
    use lv42_flock::zerocheck::bit_fold::{BLOCK, BitFold};
    fn check<const CHUNKS: usize>(rng: &mut Rng) {
        let weights: Vec<F192> = (0..8 * CHUNKS).map(|_| rng.ext()).collect();
        let fold = BitFold::new(&weights);
        for len in [BLOCK, 5] {
            let rows: Vec<[u8; CHUNKS]> = (0..len).map(|_| std::array::from_fn(|_| rng.next() as u8)).collect();
            let mut out = [F192::ZERO; BLOCK];
            fold.fold_block(&rows, &mut out);
            for (p, row) in rows.iter().enumerate() {
                let direct = (0..8 * CHUNKS)
                    .filter(|&s| row[s / 8] >> (s % 8) & 1 == 1)
                    .fold(F192::ZERO, |acc, s| acc + weights[s]);
                assert_eq!(out[p], direct, "rows of {CHUNKS} bytes, {len} rows, row {p}");
            }
        }
    }
    let mut rng = Rng(0x5eed_0006);
    check::<1>(&mut rng);
    check::<2>(&mut rng);
    check::<4>(&mut rng);
    check::<8>(&mut rng);
    check::<16>(&mut rng);
    check::<32>(&mut rng);
    check::<64>(&mut rng);
    check::<128>(&mut rng);
}

/// The byte rows' pair pass (products from a table) is the generic pass on one-byte rows, padding included.
#[test]
fn byte_pair_pass_is_the_generic_pass() {
    use lv42_flock::zerocheck::bit_fold::BitFold;
    use lv42_flock::zerocheck::multilinear::{PackedWitness, bit_round_pair, bit_round_pair_bytes};
    let mut rng = Rng(0x5eed_0007);
    for m in [11usize, 14, 17] {
        let padding = PaddingSpec {
            k_log: 14,
            useful_bits_per_block: 16_000,
        };
        let [a, b, c] = witness(m, &padding, &mut rng);
        // Any C bits (the message is linear in them), zero in the blocks' padding as the spec says.
        let [noise, ..] = witness(m, &padding, &mut rng);
        let c: Vec<u8> = c.iter().zip(&noise).map(|(&x, &y)| x ^ y).collect();
        let weights: [F192; 8] = std::array::from_fn(|_| rng.ext());
        let r_eq: Vec<F192> = (0..m - 4).map(|_| rng.ext()).collect();
        let bits = PackedWitness { a: &a, b: &b, c: &c };
        let generic = bit_round_pair(bits, &BitFold::new(&weights), &r_eq, &padding);
        assert_eq!(bit_round_pair_bytes(bits, &weights, &r_eq, &padding), generic, "m = {m}");
    }
}

/// At a skip of 3, the byte kernel's round 1 (GFNI) is the generic one's.
#[test]
fn round1_bytes_is_the_generic_round1() {
    let mut rng = Rng(0x5eed_0005);
    for m in [11usize, 14, 17] {
        let padding = PaddingSpec {
            k_log: 14,
            useful_bits_per_block: 16_000,
        };
        let [a, b, c] = witness(m, &padding, &mut rng);
        // Not an honest witness's C: the message is linear in it, so any bits test the kernel.
        let c: Vec<u8> = c.iter().map(|&x| x ^ rng.next() as u8).collect();
        let r_rest: Vec<F192> = small_challenges()
            .into_iter()
            .chain(medium_challenges())
            .chain((0..m - 3 - 7).map(|_| rng.ext()))
            .collect();
        assert_eq!(
            lv42_flock::zerocheck::skip::round1_bytes(&a, &b, &c, m, &r_rest),
            lv42_flock::zerocheck::skip::round1_generic(&a, &b, &c, m, 3, &r_rest),
            "m = {m}"
        );
    }
}

/// At a skip of 6 the skip module's zerocheck writes leanVM's stream, byte for byte, and leaves its claim.
#[test]
fn zerocheck_at_six_is_leanvms() {
    let mut rng = Rng(0x5eed_0002);
    for m in [14usize, 16, 18] {
        let padding = PaddingSpec {
            k_log: 14,
            useful_bits_per_block: 16_000,
        };
        let [a, b, c] = witness(m, &padding, &mut rng);
        let seed = keccak_seed(b"flock skip test!", &[m as u8; 32], &[6; 32]);
        let (mut w1, mut w2) = (KeccakWriter::new(seed), KeccakWriter::new(seed));
        let theirs = {
            let mut chain = Chain {
                writer: &mut w1,
                samples: Vec::new(),
            };
            prove_packed_padded(&a, &b, &c, m, &padding, &mut chain)
        };
        let mine = {
            let mut chain = Chain {
                writer: &mut w2,
                samples: Vec::new(),
            };
            prove_skip(&a, &b, &c, m, 6, &padding, &mut chain)
        };
        assert_eq!(w1.stream, w2.stream, "m = {m}: the streams");
        assert_eq!(theirs, mine, "m = {m}: the claims");
        println!("m = {m}: skip 6, {} stream bytes, identical to leanVM's", w1.stream.len());
    }
}

/// At skips of 3 to 6, on honest witnesses: the verifier's checks of the zerocheck hold, and the claims are the
/// witness's evaluations at the point.
#[test]
fn zerocheck_skips_verify_and_are_faithful() {
    let mut rng = Rng(0x5eed_0003);
    for k in 3..=6 {
        for m in [k + 8, 14, 17] {
            let padding = PaddingSpec {
                k_log: 14,
                useful_bits_per_block: 16_000,
            };
            let [a, b, c] = witness(m, &padding, &mut rng);
            let seed = keccak_seed(b"flock skip test!", &[m as u8; 32], &[k as u8; 32]);
            let mut writer = KeccakWriter::new(seed);
            let claim = {
                let mut chain = Chain {
                    writer: &mut writer,
                    samples: Vec::new(),
                };
                prove_skip(&a, &b, &c, m, k, &padding, &mut chain)
            };
            // The verifier's side (flock_min's zerocheck): the fixed coordinates, the samples, the coset's values,
            // `z`, the rounds with their eq coordinates, `v_a`, `v_b`.
            let mut channel = KeccakChannel::new(seed, &writer.stream, Checks::Enforce);
            use leanvm_flock_gas::transcript::Channel;
            let mut r: Vec<Option<E>> = small_challenges()
                .into_iter()
                .chain(medium_challenges())
                .map(|x| Some(to_e(x)))
                .collect();
            r.extend(channel.samples(m - k - 7).into_iter().map(Some));
            let coset = channel.next_scalars(1 << k).unwrap();
            let z = channel.sample();
            let values: Vec<E> = [vec![E::default(); 1 << k], coset].concat();
            let start = leanvm_flock_gas::flock::lagrange_weights(2 << k, z)
                .iter()
                .zip(&values)
                .fold(E::default(), |acc, (&w, &v)| acc + w * v);
            let (chi, running) = sumcheck(&mut channel, start, 3, &r).expect("the rounds");
            let (v_a, v_b) = (channel.next_scalar().unwrap(), channel.next_scalar().unwrap());
            channel.finish().expect("the whole stream");
            assert_eq!(from_e(z), claim.z);
            let chi: Vec<F192> = chi.into_iter().map(from_e).collect();
            assert_eq!(chi, claim.mlv_challenges);
            assert_eq!((from_e(v_a), from_e(v_b)), (claim.a_eval, claim.b_eval));
            let v_c = running + v_a * v_b;
            assert_eq!(from_e(v_c), claim.c_eval);
            assert_eq!(claim.a_eval, quirky(&a, k, claim.z, &chi), "k = {k}, m = {m}: â");
            assert_eq!(claim.b_eval, quirky(&b, k, claim.z, &chi), "k = {k}, m = {m}: b̂");
            assert_eq!(claim.c_eval, quirky(&c, k, claim.z, &chi), "k = {k}, m = {m}: ĉ");
            println!("k = {k}, m = {m}: {} stream bytes, accepted, claims true", writer.stream.len());
        }
    }
}

/// The skips' costs on a real trace's Flock witness (`LEANVM_TRACE`; ignored): round 1 alone, the zerocheck, and
/// the whole reduction (with the lincheck), at skips of 3 to 6.
#[test]
#[ignore]
fn skip_timings_on_a_real_witness() {
    let Some(dir) = std::env::var("LEANVM_TRACE").ok() else {
        println!("LEANVM_TRACE is not set");
        return;
    };
    lv42_parallel::init();
    let w = FlockWitness::load(std::path::Path::new(&dir)).expect("Flock's inputs");
    let setup = lv42_flock::hash::Blake2sSetup::new(w.n_blocks);
    let m = setup.m();
    let bytes = |words: &[u64]| -> Vec<u8> { words.iter().flat_map(|x| x.to_le_bytes()).collect() };
    let (a, b, c) = (bytes(&w.a), bytes(&w.b), bytes(&w.z));
    let padding = PaddingSpec {
        k_log: 14,
        useful_bits_per_block: lv42_flock::hash::USEFUL_BITS,
    };
    for k in [3usize, 4, 5, 6] {
        let mut rng = Rng(0x7171 ^ k as u64);
        let r_rest: Vec<F192> = small_challenges()
            .into_iter()
            .chain(medium_challenges())
            .chain((0..m - k - 7).map(|_| rng.ext()))
            .collect();
        let started = std::time::Instant::now();
        let _ = round1(&a, &b, &c, m, k, &r_rest);
        let r1 = started.elapsed().as_secs_f64();
        let seed = keccak_seed(b"flock skip time!", &[k as u8; 32], &[0; 32]);
        let mut writer = KeccakWriter::new(seed);
        let started = std::time::Instant::now();
        {
            let mut chain = Chain {
                writer: &mut writer,
                samples: Vec::new(),
            };
            let _ = prove_skip(&a, &b, &c, m, k, &padding, &mut chain);
        }
        let zc = started.elapsed().as_secs_f64();
        for (stage, secs) in lv42_flock::zerocheck::skip::STAGES.lock().unwrap().iter() {
            println!("  skip {k}: {stage} {secs:.3} s");
        }
        let mut writer = KeccakWriter::new(seed);
        let started = std::time::Instant::now();
        {
            let mut chain = Chain {
                writer: &mut writer,
                samples: Vec::new(),
            };
            let _ = setup.prove_reduction_skip(k, &w.z, &w.a, &w.b, &w.z_lincheck, &mut chain);
        }
        let all = started.elapsed().as_secs_f64();
        println!("skip {k}: round 1 {r1:.3} s; zerocheck (this module's) {zc:.3} s; reduction {all:.3} s");
    }
}

/// Flock end to end on 128 BLAKE2s compressions: the stream `prove` writes is accepted by `flock_min::verify` at
/// every skip from 3 to 6 and both ring-map orders, and its slices are `ẑ(i, p)` at the verifier's point.
#[test]
fn flock_end_to_end_at_every_skip() {
    let mut rng = Rng(0x5eed_0004);
    let n_blocks = 128;
    let blocks: Vec<lv42_flock::hash::Compression> = (0..n_blocks)
        .map(|_| {
            let m: [u32; 16] = std::array::from_fn(|_| rng.next() as u32);
            lv42_flock::hash::pinned_compression(m)
        })
        .collect();
    let n_blocks_log = lv42_flock::hash::min_n_blocks_log(n_blocks);
    let (z, a, b, z_lincheck) = lv42_flock::hash::generate_witness_with_ab_packed_and_lincheck(&blocks, n_blocks_log);
    let mut witness = FlockWitness {
        n_blocks,
        z,
        a,
        b,
        z_lincheck,
    };
    // The placement's stripes are the generator's: unmoved, the witness is the same; moved, it is the instances'.
    let generated = witness.z_lincheck.clone();
    let identity: Vec<usize> = (0..n_blocks).collect();
    witness.place(&identity);
    assert_eq!(witness.z_lincheck, generated, "the stripes rebuilt from z");
    let moved: Vec<usize> = (0..n_blocks).map(|i| (i * 37 + 5) % n_blocks).collect();
    let mut blocks_moved = blocks.clone();
    for (i, &p) in moved.iter().enumerate() {
        blocks_moved[p] = blocks[i];
    }
    witness.place(&moved);
    let regenerated = lv42_flock::hash::generate_witness_with_ab_packed_and_lincheck(&blocks_moved, n_blocks_log);
    assert_eq!(
        (&witness.z, &witness.a, &witness.b, &witness.z_lincheck),
        (&regenerated.0, &regenerated.1, &regenerated.2, &regenerated.3),
        "a placed witness is the moved instances'"
    );
    let log_n = 14 + n_blocks_log;
    for k in 3..=6 {
        for slices in [Slices::Tower, Slices::Weighted] {
            let variant = Variant { skip: k, slices };
            let seed = keccak_seed(b"flock skip e2e!!", &[k as u8; 32], &[slices as u8; 32]);
            let mut writer = KeccakWriter::new(seed);
            let started = std::time::Instant::now();
            let out = prove(&mut writer, &witness, variant, log_n, false).expect("a proof");
            let secs = started.elapsed().as_secs_f64();
            let mut channel = KeccakChannel::new(seed, &writer.stream, Checks::Enforce);
            let reduced = flock_min::verify(log_n, variant, &mut channel).expect("accepted");
            channel.finish().expect("the whole stream");
            assert_eq!(reduced.point, out.point, "the slices' point");
            // The slices are the witness's: s_i = Σ_u eq(p, u) bit_i(z_u), u the packed words.
            let point: Vec<F192> = out.point.iter().map(|&x| from_e(x)).collect();
            let eq = eq_table(&point);
            for (i, &s) in out.slices.iter().enumerate() {
                let direct = witness
                    .z
                    .iter()
                    .zip(&eq)
                    .filter(|(w, _)| *w >> i & 1 == 1)
                    .fold(F192::ZERO, |acc, (_, &e)| acc + e);
                assert_eq!(from_e(s), direct, "k = {k}: slice {i}");
            }
            let (ma, mb) = leanvm_flock_gas::matrices::matrix_values(&reduced.matrices.point).unwrap();
            assert_eq!((ma, mb), (reduced.matrices.a, reduced.matrices.b), "the matrices' claim");
            println!(
                "skip {k}, {slices:?}: {} stream bytes, accepted, slices true ({secs:.3} s)",
                writer.stream.len()
            );
        }
    }
}
