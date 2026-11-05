// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Probe for `crates/slh_dsa/SPEC-FAST.md` (appendix A): Flock's prover (`leanvm_univariate::prover::flock::prove`,
//! the π1 main line's Flock: zerocheck with a univariate skip, lincheck, slices) on synthetic BLAKE2s compressions at
//! the bit count of SLH-DSA-SHAKE-128s's Keccak-f table (4,096 blocks of 2^16 bits = 2^28 bits = 2^14 BLAKE2s blocks
//! of 2^14 bits), and at 2^30 bits. Not part of the build: copy it to `crates/leanvm_univariate/tests/` and run
//! `cargo test --release -p leanvm_univariate --test flock_scale -- --ignored --nocapture`.

use leanvm_flock_gas::flock_min::{self, Slices, Variant};
use leanvm_flock_gas::transcript::{Checks, FsShape, KeccakChannel, KeccakWriter, keccak_seed};
use leanvm_univariate::prover::flock::{FlockWitness, prove};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
#[ignore]
fn flock_prover_at_slh_scale() {
    lv42_parallel::init();
    for n_blocks_log in [14usize, 16] {
        let mut rng = Rng(0x5eed_0005 ^ n_blocks_log as u64);
        let n_blocks = 1usize << n_blocks_log;
        let started = std::time::Instant::now();
        let blocks: Vec<lv42_flock::hash::Compression> = (0..n_blocks)
            .map(|_| {
                let m: [u32; 16] = std::array::from_fn(|_| rng.next() as u32);
                lv42_flock::hash::pinned_compression(m)
            })
            .collect();
        let (z, a, b, z_lincheck) =
            lv42_flock::hash::generate_witness_with_ab_packed_and_lincheck(&blocks, n_blocks_log);
        let witness_s = started.elapsed().as_secs_f64();
        let witness = FlockWitness {
            n_blocks,
            z,
            a,
            b,
            z_lincheck,
        };
        let log_n = 14 + n_blocks_log;
        for k in [3usize, 6] {
            let variant = Variant {
                skip: k,
                slices: Slices::Tower,
                fs: FsShape::Rec,
            };
            let seed = keccak_seed(b"flock slh scale!", &[k as u8; 32], &[0; 32]);
            let mut writer = KeccakWriter::new(seed);
            let started = std::time::Instant::now();
            let _out = prove(&mut writer, &witness, variant, log_n, false).expect("a proof");
            let secs = started.elapsed().as_secs_f64();
            let mut channel = KeccakChannel::new(seed, &writer.stream, Checks::Enforce);
            flock_min::verify(log_n, variant, &mut channel).expect("accepted");
            println!(
                "Flock, 2^{n_blocks_log} BLAKE2s blocks (2^{log_n} bits), skip {k}: witness {witness_s:.2} s, prove {secs:.3} s, stream {} B",
                writer.stream.len()
            );
        }
    }
}
