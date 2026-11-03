// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The templates on random inputs: every pull equals its push, and the results are the reference's.

use leanvm_flock_gas::field::K;
use leanvm_flock_gas::transcript::keccak256;

use super::keccak::{Bit, D32, Permutation, Sponge, keccak_f};
use super::keccak16::D16;
use super::layout::{Builder, Finished, Value};
use super::spec::PublicInputs;
use super::units::{Bools, Packer};

fn xorshift(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn no_public() -> PublicInputs {
    PublicInputs {
        statement: [0; 32],
        roots: vec![],
        elements: vec![],
    }
}

/// Hash `messages` with free bits on a permutation template; returns the finished layout and each digest's values.
fn hash_all<P: Permutation>(
    log_width: u8,
    make: impl FnOnce(&mut Builder) -> P,
    messages: &[Vec<u8>],
) -> (Finished, Vec<Vec<Value>>) {
    let mut b = Builder::new(log_width);
    let p = make(&mut b);
    let mut sponge = Sponge::new(&mut b, p);
    let mut bools = Bools::new(&mut b);
    let mut digests = Vec::new();
    for m in messages {
        let bits: Vec<Bit> = m
            .iter()
            .flat_map(|byte| (0..8).map(move |j| byte >> j & 1 == 1))
            .map(|bit| Bit::V(bools.bit_and_copy(&mut b, bit).1))
            .collect();
        digests.push(sponge.keccak256(&mut b, &bits));
    }
    (b.finish(), digests)
}

fn digest_bytes(f: &Finished, digest: &[Value]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, &v) in digest.iter().enumerate() {
        let w = f.words[v as usize];
        assert!(w == K(0) || w == K(1), "a digest bit is a bit");
        out[i / 8] |= (w.0 as u8) << (i % 8);
    }
    out
}

pub(super) fn check_keccak<P: Permutation>(log_width: u8, make: impl FnOnce(&mut Builder) -> P) {
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let messages: Vec<Vec<u8>> = [0usize, 1, 32, 80, 135, 136, 137, 271, 300]
        .iter()
        .map(|&len| (0..len).map(|_| xorshift(&mut seed) as u8).collect())
        .collect();
    let (f, digests) = hash_all(log_width, make, &messages);
    assert_eq!(
        f.circuit.check(&f.witness, &no_public()),
        Ok(()),
        "every pull equals its push"
    );
    for (m, d) in messages.iter().zip(&digests) {
        assert_eq!(digest_bytes(&f, d), keccak256(m), "the digest of {} bytes", m.len());
    }
    println!("{:?}", f.stats);
    // A changed word at any wired position (not a self-loop no formula reads) is caught.
    let wired: Vec<usize> = (0..f.stats.positions_used)
        .filter(|&i| f.circuit.sigma[i] as usize != i)
        .collect();
    for k in 0..20 {
        let mut w = f.witness.clone();
        let i = wired[(xorshift(&mut seed) as usize) % wired.len()];
        w[i] = w[i] + K(1 + k);
        assert!(f.circuit.check(&w, &no_public()).is_err(), "a change at {i} is caught");
    }
}

#[test]
fn the_reference_permutation_is_keccak() {
    // keccak256 of the empty message: one block, 0x01 at byte 0 and 0x80 at byte 135.
    let mut a = [0u64; 25];
    a[0] = 1;
    a[16] = 0x80 << 56;
    keccak_f(&mut a);
    let bytes: Vec<u8> = a[..4].iter().flat_map(|l| l.to_le_bytes()).collect();
    assert_eq!(bytes, keccak256(&[]));
}

#[test]
fn d32_keccak256_on_random_inputs() {
    check_keccak(5, D32::new);
}

#[test]
fn packings_are_the_words() {
    let mut seed = 7u64;
    for log_width in [4u8, 5] {
        let mut b = Builder::new(log_width);
        let mut consts = super::keccak::Constants::new();
        let mut bools = Bools::new(&mut b);
        let mut packer = Packer::new(&mut b);
        let mut expected = Vec::new();
        let mut packed = Vec::new();
        for width in [1usize, 4, 15, 16, 31, 64, 64, 64] {
            let word = xorshift(&mut seed) & if width == 64 { u64::MAX } else { (1 << width) - 1 };
            // Every other bit, for the sparse case, when narrow.
            let bits: Vec<(usize, Value)> = (0..width)
                .filter(|e| width == 64 || width < 16 || e % 2 == 0)
                .map(|e| (e, bools.bit(&mut b, word >> e & 1 == 1)))
                .collect();
            let w: u64 = bits.iter().map(|&(e, _)| word & 1 << e).fold(0, |a, x| a | x);
            expected.push(w);
            packed.push(packer.pack(&mut b, &mut consts, &bits));
        }
        let f = b.finish();
        assert_eq!(f.circuit.check(&f.witness, &no_public()), Ok(()));
        for (&v, &e) in packed.iter().zip(&expected) {
            assert_eq!(f.words[v as usize], K(e));
        }
    }
}

#[test]
fn d16_keccak256_on_random_inputs() {
    check_keccak(4, D16::new);
}

/// D16v's rows a permutation (SPEC-REC.md §2.4.1): 1,536 `k0`, 6,144 `k1`, 160 `kprep`, and 344 `kd` for the D units
/// the `k0` and `kprep` rows lack. So 8,184 rows, 130,944 positions.
#[test]
fn d16_rows_a_permutation() {
    let perms = 4;
    let messages: Vec<Vec<u8>> = (0..perms).map(|k| vec![k as u8; 100]).collect();
    let (f, _) = hash_all(4, D16::new, &messages);
    let rows = |name: &str| f.stats.rows.get(name).copied().unwrap_or(0);
    assert_eq!(rows("keccak16/k0"), 1536 * perms);
    assert_eq!(rows("keccak16/k1"), 6144 * perms);
    assert_eq!(rows("keccak16/kprep"), 160 * perms);
    assert_eq!(rows("keccak16/kd"), 344 * perms);
    let steady = 1536 + 6144 + 160 + 344;
    assert_eq!((steady, 16 * steady), (8184, 130_944));
    // The constants (padding, the first block's capacity) are in `k1`'s spare role: no rows of their own.
    assert_eq!(rows("const"), 0);
    println!("{:?}", f.stats);
}
