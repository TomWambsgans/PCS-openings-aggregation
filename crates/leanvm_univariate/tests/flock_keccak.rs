// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Flock on the Keccak-f\[1600\] block (`lv42_flock::keccak`, crates/slh_dsa/SPEC-FAST.md §4.2, M1), end to end:
//!
//! - the verifier's walk (`leanvm_flock_gas::keccak_flock`, on `E`) is the prover's (`lv42_flock::keccak`, on `F192`);
//! - `prove_keccak`'s stream is accepted by `flock_min::verify_walked_with::<_, Keccak>` (the walked terminal) at
//!   skips of 3 and 6, both eq points; the slices are the witness's at the verifier's point;
//! - a witness with one state bit flipped (its rows' own values kept, so the zerocheck still holds) and a stream with
//!   one slice changed are rejected;
//! - at 4,096 blocks (3,959 random permutations and Keccak-f(0) padding, `log_n = 29`, ignored): the same, and the
//!   benchmark (witness and proof, median of 3, skips 3 and 6).
//!
//! `cargo test --release -p leanvm_univariate --test flock_keccak -- --nocapture`;
//! `cargo test --release -p leanvm_univariate --test flock_keccak -- --ignored --nocapture` (4,096 blocks).

use leanvm_flock_gas::VerifierError;
use leanvm_flock_gas::field::E;
use leanvm_flock_gas::flock_min::{self, Slices, Variant};
use leanvm_flock_gas::keccak_flock::Keccak;
use leanvm_flock_gas::transcript::{Checks, FsShape, KeccakChannel, KeccakWriter, keccak_seed};
use leanvm_univariate::prover::flock::{FlockWitness, prove_keccak};
use lv42_flock::keccak::{self as block, K, K_LOG, LANES, WORDS};
use lv42_primitives::field::F192;
use lv42_primitives::multilinear::eq_table;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn state(&mut self) -> [u64; LANES] {
        std::array::from_fn(|_| self.next())
    }
}

fn to_e(x: F192) -> E {
    E::new(x.c0, x.c1, x.c2)
}

fn from_e(x: E) -> F192 {
    F192::new(x.c0, x.c1, x.c2)
}

fn witness(inputs: &[[u64; LANES]]) -> FlockWitness {
    let n_blocks_log = block::min_n_blocks_log(inputs.len());
    let (z, a, b, z_lincheck) = block::generate_witness_with_ab_packed_and_lincheck(inputs, n_blocks_log);
    FlockWitness {
        n_blocks: inputs.len(),
        z,
        a,
        b,
        z_lincheck,
    }
}

/// `s_i = Σ_u eq(p, u) bit_i(z_u)`, `u` the packed words.
fn slices_of(z: &[u64], point: &[E]) -> Vec<F192> {
    let point: Vec<F192> = point.iter().map(|&x| from_e(x)).collect();
    let eq = eq_table(&point);
    assert_eq!(eq.len(), z.len());
    let chunk = 1 << 16;
    let parts: Vec<[F192; 64]> = eq
        .chunks(chunk)
        .zip(z.chunks(chunk))
        .map(|(eq, z)| {
            let mut s = [F192::ZERO; 64];
            for (&e, &w) in eq.iter().zip(z) {
                let mut bits = w;
                while bits != 0 {
                    s[bits.trailing_zeros() as usize] += e;
                    bits &= bits - 1;
                }
            }
            s
        })
        .collect();
    (0..64).map(|i| parts.iter().fold(F192::ZERO, |acc, p| acc + p[i])).collect()
}

fn variant(skip: usize, fs: FsShape) -> Variant {
    Variant {
        skip,
        slices: Slices::TowerWalk,
        fs,
    }
}

/// Prove, then verify: the verdict, and the proof's slices' point and slices and stream.
fn run(witness: &FlockWitness, variant: Variant, log_n: usize, seed: [u8; 32]) -> (Result<(), VerifierError>, Vec<E>, Vec<E>, Vec<u8>, f64) {
    let mut writer = KeccakWriter::new(seed);
    let started = std::time::Instant::now();
    let out = prove_keccak(&mut writer, witness, variant, log_n).expect("a proof");
    let secs = started.elapsed().as_secs_f64();
    let verdict = verify(&writer.stream, variant, log_n, seed, &out.point);
    (verdict, out.point, out.slices, writer.stream, secs)
}

fn verify(stream: &[u8], variant: Variant, log_n: usize, seed: [u8; 32], point: &[E]) -> Result<(), VerifierError> {
    let mut channel = KeccakChannel::new(seed, stream, Checks::Enforce);
    let (theirs, _end) = flock_min::verify_walked_with::<E, Keccak>(log_n, variant, &mut channel)?;
    channel.finish()?;
    assert_eq!(theirs, point, "the slices' point");
    Ok(())
}

/// The witness with state `A_j`'s lane `l` bit `z` flipped in block `b`, in `z`, `A z` (a lin-id row: `a = z`) and
/// the stripes: every row still has `a·b = c`, but `A z` is no longer `A_0` applied to `z`.
fn flip_state_bit(w: &mut FlockWitness, b: usize, slot: usize) {
    w.z[b * WORDS + slot / 64] ^= 1 << (slot % 64);
    w.a[b * WORDS + slot / 64] ^= 1 << (slot % 64);
    let stripe = if w.z.len() / WORDS >= 8 { (b / 8) * K } else { 0 };
    w.z_lincheck[stripe + slot] ^= 1 << (b % 8);
}

fn check_end_to_end(witness: &FlockWitness, log_n: usize, label: &str, cases: &[(usize, FsShape)]) {
    for &(skip, fs) in cases {
        let v = variant(skip, fs);
        let seed = keccak_seed(b"flock keccak e2e", &[skip as u8; 32], &[fs as u8; 32]);
        let (verdict, point, slices, stream, secs) = run(witness, v, log_n, seed);
        assert_eq!(verdict, Ok(()), "{label}: skip {skip} {fs:?} accepted");
        assert_eq!(v.scalars_with(log_n, K_LOG - 6) * 24, stream.len(), "the stream's length");
        let direct = slices_of(&witness.z, &point);
        let ours: Vec<F192> = slices.iter().map(|&s| from_e(s)).collect();
        assert_eq!(ours, direct, "{label}: the slices are the witness's");
        // One slice changed: rejected (the terminal no longer holds).
        let end = stream.len();
        let mut wrong = stream.clone();
        wrong[end - 24 * 64 + 24 * 17 + 23] ^= 1;
        assert!(verify(&wrong, v, log_n, seed, &point).is_err(), "{label}: a wrong slice is rejected");
        println!("{label}, skip {skip}, {fs:?}: {} stream bytes, accepted, slices true ({secs:.3} s)", stream.len());
    }
}

#[test]
fn the_walks_agree() {
    let mut rng = Rng(0x3a1c);
    let w: Vec<F192> = (0..K).map(|_| F192::new(rng.next(), rng.next(), rng.next())).collect();
    let (a, b) = block::row_values_walk(&w);
    let we: Vec<E> = w.iter().map(|&x| to_e(x)).collect();
    let (ae, be) = leanvm_flock_gas::keccak_flock::row_values(&we);
    assert!(a.iter().zip(&ae).all(|(&x, &y)| to_e(x) == y), "A0 w");
    assert!(b.iter().zip(&be).all(|(&x, &y)| to_e(x) == y), "B0 w");
    assert_eq!(block::CONST_POS, leanvm_flock_gas::keccak_flock::CONSTANT_COLUMN);
}

/// 128 blocks (`log_n = 24`, the walked verifier's least).
#[test]
fn flock_keccak_end_to_end() {
    let mut rng = Rng(0x5eed_0006);
    let inputs: Vec<[u64; LANES]> = (0..121).map(|_| rng.state()).collect();
    let mut w = witness(&inputs);
    let log_n = K_LOG + 7;
    check_end_to_end(&w, log_n, "128 blocks", &[(3, FsShape::Rec), (6, FsShape::Rec), (3, FsShape::Main), (6, FsShape::Main)]);
    // A flipped state bit (A_9 lane 13 bit 40 of block 77): rejected at both skips.
    flip_state_bit(&mut w, 77, 64 * block::a_word(9, 13) + 40);
    for skip in [3, 6] {
        let v = variant(skip, FsShape::Rec);
        let seed = keccak_seed(b"flock keccak bad", &[skip as u8; 32], &[0; 32]);
        let (verdict, ..) = run(&w, v, log_n, seed);
        assert!(verdict.is_err(), "skip {skip}: a flipped bit is rejected ({verdict:?})");
    }
}

/// 4,096 blocks: 3,959 random permutations (SLH-DSA-SHAKE-128s's count) and Keccak-f(0) padding, `log_n = 29`; the
/// end-to-end checks, a flipped output bit rejected, and the benchmark.
#[test]
#[ignore]
fn flock_keccak_4096() {
    lv42_parallel::init();
    let mut rng = Rng(0x5eed_1000);
    let inputs: Vec<[u64; LANES]> = (0..3959).map(|_| rng.state()).collect();
    let log_n = K_LOG + 12;
    let mut w = witness(&inputs);
    check_end_to_end(&w, log_n, "4,096 blocks", &[(3, FsShape::Rec), (6, FsShape::Rec)]);
    // Benchmark: witness and proof, median of 3.
    let median = |mut x: Vec<f64>| {
        x.sort_by(f64::total_cmp);
        x[x.len() / 2]
    };
    let witness_secs = median(
        (0..3)
            .map(|_| {
                let started = std::time::Instant::now();
                let w = witness(&inputs);
                let secs = started.elapsed().as_secs_f64();
                drop(w);
                secs
            })
            .collect(),
    );
    for skip in [3, 6] {
        let v = variant(skip, FsShape::Rec);
        let seed = keccak_seed(b"flock keccak 4k!", &[skip as u8; 32], &[0; 32]);
        let mut times = Vec::new();
        let mut reductions = Vec::new();
        for _ in 0..3 {
            let mut writer = KeccakWriter::new(seed);
            let started = std::time::Instant::now();
            let out = prove_keccak(&mut writer, &w, v, log_n).expect("a proof");
            times.push(started.elapsed().as_secs_f64());
            reductions.push(out.reduction_secs);
        }
        println!(
            "BENCH Flock, 4,096 Keccak-f (2^{log_n} bits), skip {skip}: witness {witness_secs:.3} s, prove {:.3} s (runs {:?})",
            median(times.clone()),
            times.iter().map(|t| format!("{t:.3}")).collect::<Vec<_>>()
        );
        for (stage, secs) in lv42_flock::zerocheck::skip::STAGES.lock().unwrap().iter() {
            println!("  skip {skip}: zerocheck {stage} {secs:.3} s");
        }
    }
    // A flipped output bit of block 1000: rejected.
    flip_state_bit(&mut w, 1000, 64 * block::port_word(4, block::ROLE_X) + 9);
    let v = variant(3, FsShape::Rec);
    let seed = keccak_seed(b"flock keccak bad", &[3; 32], &[1; 32]);
    let (verdict, ..) = run(&w, v, log_n, seed);
    assert!(verdict.is_err(), "a flipped output bit is rejected ({verdict:?})");
}
