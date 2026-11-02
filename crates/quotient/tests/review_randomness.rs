// Part of this repository (written by an adversarial review of c004698: the per-proof randomness and the opening
// transcript in the form F2 proves). MIT OR Apache-2.0; see NOTICE.md.
//! Attacks on the per-proof randomness (`protocol::fresh_seed`, `Randomness::derive`, the padding's ChaCha12 lanes)
//! and on the opening's transcript (`opening::prefix`, `iv`, `layout_id`, the root as the proof's first two
//! scalars), against independent re-implementations of what the doc comments specify.
//!
//! Everything here runs at `2^17` rows or on small layouts: `cargo test --release -p quotient --test
//! review_randomness`.
//!
//! * The KDF is its specification, recomputed with `sha3`'s Keccak-256: the cells' digest (runs of `2^12`, the
//!   count), the key, the masks' three blocks and their word order, the padding.
//! * Every hash input of the derivation (key, mask blocks, padding, table seeds, lane keys) is separated from the
//!   others by its tag or its length, and from every hash the proof publishes (Merkle leaves and nodes, the
//!   reduction's chain) by its length.
//! * `StdRng` is ChaCha12 (an independent ChaCha12 here), and the prover's two tables are filled lane by lane by
//!   ChaCha12 keyed by Keccak-256(table seed ‖ `l`), the table seed Keccak-256(`"pcs-quotient-pad-"` ‖ name ‖
//!   padding): the random first pieces, the overflow lane, the share lane `ρ`, the random lanes. No two lanes of
//!   the two tables share a key; the masks sit in the witness table where `derive` says.
//! * `prove` never repeats (two proofs of one witness share no root and no `a_j`); `derive` hedges (a repeated seed
//!   repeats the proof for the same witness only); no word of the seed, the key, the cells' digest, the padding, a
//!   table seed, a lane key or a mask appears in what the prover publishes.
//! * `layout_id` hashes an encoding that a decoder inverts (so it is injective), recomputed from `Layout`'s public
//!   accessors; over 200+ layouts, equal ids exactly for equal layouts.
//! * The version-1 seed hashed no layout and no count: two claims under a layout of `v` variables and one claim
//!   under one of `2v + 1` had the same seed. The prefix separates them.
//! * Openings do not replay across the layouts that share `vars` and `log_n` (the witness layout at `2^r` rows and
//!   the wiring layout at `2^(r+1)`); the root's two scalars are canonical, checked first, and a proof re-labelled
//!   for another root fails; claims reordered, dropped, duplicated, appended, or of the wrong arity are rejected.
//!   An opening of **no** claims is accepted (vacuous: `PCS_OPEN` requires `k ≥ 1`).

use std::collections::{HashMap, HashSet};

use fiat_shamir::merkle::hash_to_scalars;
use primitives::field::{F64, F192};
use primitives::test_rng::Rng;
use quotient::circuit::{Builder, Circuit, Src, public_words};
use quotient::opening::{self, Claim, LOG_INV_RATE, LOG_PIECE, Lane, Layout, PREFIX_LEN, Table, VERSION};
use quotient::protocol::{
    self, Index, MAX_LOG_ROWS, MIN_LOG_ROWS, Proved, Randomness, label, prove, prove_with_randomness, quotient_layout,
    wiring_layout, witness_layout,
};
use quotient::statement::{Statement, pair};
use rand::{RngCore, SeedableRng, rngs::StdRng};
use sha3::{Digest as _, Keccak256};
use verifier::{Digest, VerifierError};

/// Keccak-256 by `sha3`, not by `primitives::hash`.
fn keccak(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    parts.iter().for_each(|p| hasher.update(p));
    hasher.finalize().into()
}

fn le_words(bytes: &[u8]) -> Vec<u64> {
    bytes
        .as_chunks::<8>()
        .0
        .iter()
        .map(|&c| u64::from_le_bytes(c))
        .collect()
}

// ---------------------------------------------------------------------------------------------------------------
// The KDF, re-implemented from `protocol.rs`'s doc comments.

const KDF_KEY: &[u8] = b"pcs-quotient-kdf-v1-key";
const KDF_CELLS: &[u8] = b"pcs-quotient-kdf-v1-cells";
const KDF_MASKS: &[u8] = b"pcs-quotient-kdf-v1-masks";
const KDF_PADDING: &[u8] = b"pcs-quotient-kdf-v1-padding";
const PAD: &[u8] = b"pcs-quotient-pad-";

fn spec_cells_digest(cells: &[F64]) -> [u8; 32] {
    let runs: Vec<[u8; 32]> = cells
        .chunks(1 << 12)
        .map(|run| {
            let bytes: Vec<u8> = run.iter().flat_map(|w| w.0.to_le_bytes()).collect();
            keccak(&[&bytes])
        })
        .collect();
    let mut parts: Vec<&[u8]> = vec![KDF_CELLS];
    let count = (cells.len() as u64).to_le_bytes();
    parts.push(&count);
    runs.iter().for_each(|r| parts.push(r));
    keccak(&parts)
}

struct SpecKdf {
    key: [u8; 32],
    cells_digest: [u8; 32],
    masks: [[F64; 3]; 4],
    padding: [u8; 32],
}

fn spec_derive(seed: &[u8; 32], index_root: &[u8; 32], statement: &Statement, cells: &[F64]) -> SpecKdf {
    let cells_digest = spec_cells_digest(cells);
    let key = keccak(&[KDF_KEY, seed, &label(index_root, statement), &cells_digest]);
    let words: Vec<u64> = (0..3u8)
        .flat_map(|k| le_words(&keccak(&[KDF_MASKS, &key, &[k]])))
        .collect();
    // Word `4k + i` is `masks[(4k + i) / 3][(4k + i) % 3]`.
    let mut masks = [[F64::ZERO; 3]; 4];
    for (w, &word) in words.iter().enumerate() {
        masks[w / 3][w % 3] = F64(word);
    }
    SpecKdf {
        key,
        cells_digest,
        masks,
        padding: keccak(&[KDF_PADDING, &key]),
    }
}

fn spec_table_seed(padding: &[u8; 32], name: &[u8]) -> [u8; 32] {
    keccak(&[PAD, name, padding])
}

fn spec_lane_key(table_seed: &[u8; 32], l: usize) -> [u8; 32] {
    keccak(&[table_seed, &(l as u64).to_le_bytes()])
}

/// `Randomness::derive` is exactly its documented construction, at run boundaries of the cells' digest (no cells,
/// one, `2^12 - 1`, `2^12`, `2^12 + 1`, three runs and a bit) and for random seeds, roots and statements.
#[test]
fn kdf_is_its_specification() {
    let mut rng = Rng::new(0xD0C);
    for len in [0usize, 1, 4095, 4096, 4097, 3 * 4096 + 5, 1 << 16] {
        for _ in 0..3 {
            let cells: Vec<F64> = (0..len).map(|_| F64(rng.next_u64())).collect();
            let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
            let root: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
            let statement = Statement {
                y: std::array::from_fn(|_| rng.next_u8()),
                root: std::array::from_fn(|_| rng.next_u8()),
            };
            let got = Randomness::derive(&seed, &root, &statement, &cells);
            let want = spec_derive(&seed, &root, &statement, &cells);
            assert!(got.masks == want.masks, "masks, {len} cells");
            assert_eq!(got.padding, want.padding, "padding, {len} cells");
        }
    }
}

/// Every hash input of the derivation is separated from every other by its tag or its length: the key
/// (`23 + 32 + 112 + 32` bytes), a mask block (`25 + 32 + 1`), the padding (`27 + 32`), a table seed (`17 + 7 + 32`,
/// `17 + 8 + 32`), a lane key (`32 + 8`), the cells' digest (`25 + 8 + 32 r`), a run (`8 · 2^12`, or less for the
/// last). And none has the length of a hash the proof publishes: a Merkle node (64), a leaf (a row: `8 · lanes` at
/// the first level, `3 · 8 · 2^4` deeper), a step of the reduction's chain (`32 + 32 k`). No tag is a prefix of
/// another.
#[test]
fn kdf_hash_inputs_are_separated() {
    let tags = [KDF_KEY, KDF_CELLS, KDF_MASKS, KDF_PADDING, PAD];
    for (i, a) in tags.iter().enumerate() {
        for (j, b) in tags.iter().enumerate() {
            if i != j {
                assert!(
                    !b.starts_with(a),
                    "{:?} prefixes {:?}",
                    String::from_utf8_lossy(a),
                    String::from_utf8_lossy(b)
                );
            }
        }
    }
    let secret_lengths = [
        KDF_KEY.len() + 32 + 112 + 32,
        KDF_MASKS.len() + 32 + 1,
        KDF_PADDING.len() + 32,
        PAD.len() + b"witness".len() + 32,
        PAD.len() + b"quotient".len() + 32,
        32 + 8,
    ];
    let distinct: HashSet<_> = secret_lengths.iter().collect();
    assert_eq!(distinct.len(), secret_lengths.len(), "{secret_lengths:?}");
    // The cells' digest and the runs: `25 + 8 + 32 r` and `8 · 2^12` bytes (the protocol's cells are a power of
    // two above `2^12`, so every run is whole), never one of the lengths above.
    for runs in 0..(1 << 12) {
        assert!(!secret_lengths.contains(&(KDF_CELLS.len() + 8 + 32 * runs)));
    }
    assert!(!secret_lengths.contains(&(8 << 12)));
    // Public hash inputs: Merkle nodes, the leaves of every level of the three layouts, the reduction's chain.
    let mut public = vec![64usize];
    for log_rows in MIN_LOG_ROWS..=MAX_LOG_ROWS {
        for layout in [
            witness_layout(log_rows),
            wiring_layout(log_rows),
            quotient_layout(log_rows),
        ] {
            public.push(8 * layout.lanes());
        }
    }
    public.extend([8 * 64, 3 * 8 * 16]);
    public.extend((0..8).map(|k| 32 + 32 * k));
    for len in public {
        assert!(!secret_lengths.contains(&len), "a public hash input of {len} bytes");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// ChaCha12, independently of `rand_chacha`.

fn quarter(s: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    s[a] = s[a].wrapping_add(s[b]);
    s[d] = (s[d] ^ s[a]).rotate_left(16);
    s[c] = s[c].wrapping_add(s[d]);
    s[b] = (s[b] ^ s[c]).rotate_left(12);
    s[a] = s[a].wrapping_add(s[b]);
    s[d] = (s[d] ^ s[a]).rotate_left(8);
    s[c] = s[c].wrapping_add(s[d]);
    s[b] = (s[b] ^ s[c]).rotate_left(7);
}

/// The first `count` 64-bit words of ChaCha12 keyed by `key`, block counter from 0 (words 12, 13), stream 0
/// (words 14, 15), each word two consecutive 32-bit outputs, the low one first.
fn chacha12(key: &[u8; 32], count: usize) -> Vec<u64> {
    let k: [u32; 8] = std::array::from_fn(|i| u32::from_le_bytes(key[4 * i..4 * i + 4].try_into().unwrap()));
    let mut out = Vec::with_capacity(count + 8);
    let mut counter = 0u64;
    while out.len() < count {
        let init: [u32; 16] = [
            0x6170_7865,
            0x3320_646e,
            0x7962_2d32,
            0x6b20_6574,
            k[0],
            k[1],
            k[2],
            k[3],
            k[4],
            k[5],
            k[6],
            k[7],
            counter as u32,
            (counter >> 32) as u32,
            0,
            0,
        ];
        let mut s = init;
        for _ in 0..6 {
            quarter(&mut s, 0, 4, 8, 12);
            quarter(&mut s, 1, 5, 9, 13);
            quarter(&mut s, 2, 6, 10, 14);
            quarter(&mut s, 3, 7, 11, 15);
            quarter(&mut s, 0, 5, 10, 15);
            quarter(&mut s, 1, 6, 11, 12);
            quarter(&mut s, 2, 7, 8, 13);
            quarter(&mut s, 3, 4, 9, 14);
        }
        for i in 0..16 {
            s[i] = s[i].wrapping_add(init[i]);
        }
        out.extend((0..8).map(|i| s[2 * i] as u64 | (s[2 * i + 1] as u64) << 32));
        counter += 1;
    }
    out.truncate(count);
    out
}

/// `rand`'s `StdRng`, which `opening::lane_rng` keys, is ChaCha12 (HIDING.md, STATUS.md), word for word.
#[test]
fn std_rng_is_chacha12() {
    let mut rng = Rng::new(0xC4AC);
    for _ in 0..8 {
        let key: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        let mut std = StdRng::from_seed(key);
        let ours = chacha12(&key, 1000);
        let theirs: Vec<u64> = (0..1000).map(|_| std.next_u64()).collect();
        assert_eq!(ours, theirs);
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The protocol at `2^17` rows.

/// The protocol tests' toy circuit (`protocol::tests::toy`): `root` is a Keccak-256 of `y`, at `2^17` rows.
fn toy() -> Circuit {
    let mut b = Builder::new();
    let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
    let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
    b.finish(17, &public_words(&x, &digest))
}

fn toy_statement(x: &[u8; 32]) -> Statement {
    Statement {
        y: *x,
        root: pair(x, x),
    }
}

fn toy_inputs(x: &[u8; 32]) -> Vec<bool> {
    (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect()
}

struct Toy {
    circuit: Circuit,
    index: Index,
    index_committed: opening::Committed,
}

fn toy_setup() -> Toy {
    let circuit = toy();
    let index = Index::new(&circuit);
    let index_committed = opening::commit(&index.table);
    Toy {
        circuit,
        index,
        index_committed,
    }
}

/// The checks of one hidden table's padding against ChaCha12 keyed by `spec_lane_key(table_seed, l)`; the lane
/// keys it used.
fn check_padding(table: &Table, table_seed: &[u8; 32], name: &str) -> Vec<[u8; 32]> {
    let layout = &table.layout;
    let (log_lane, s) = (layout.log_lane(), layout.log_piece().expect("a hidden layout"));
    let (lane_len, piece) = (1usize << log_lane, 1usize << s);
    let held = layout.pieces().len();
    let share = layout.share().expect("a share lane");
    let overflow = layout.overflow().expect("an overflow lane");
    let lane = |l: usize| &table.stack[l * lane_len..(l + 1) * lane_len];
    let mut keys = vec![];
    for l in 0..layout.lanes() {
        let key = spec_lane_key(table_seed, l);
        keys.push(key);
        let needed = if matches!(layout.lane(l), Lane::Block(_)) {
            piece
        } else {
            lane_len
        };
        let stream: Vec<F64> = chacha12(&key, needed).into_iter().map(F64).collect();
        let words = lane(l);
        match layout.lane(l) {
            Lane::Block(_) => assert_eq!(
                &words[..piece],
                &stream[..piece],
                "{name}: block lane {l}'s first piece"
            ),
            Lane::Overflow => {
                assert_eq!(
                    &words[..piece],
                    &stream[..piece],
                    "{name}: the overflow lane's first piece"
                );
                let tail = lane_len - (held + 1) * piece;
                assert_eq!(
                    &words[(held + 1) * piece..],
                    &stream[piece..piece + tail],
                    "{name}: the overflow lane past its pieces"
                );
            }
            Lane::Random => assert_eq!(words, &stream[..], "{name}: random lane {l}"),
        }
    }
    // The overflow lane's pieces are the table's plus the share lane's: `Table::read` is their sum, and the share
    // lane's pieces are its own stream (checked above), so the overflow lane is the table masked by `ρ`.
    let mut read = vec![F64::ZERO; held * piece];
    for (k, &p) in layout.pieces().iter().enumerate() {
        table.read(p * piece, &mut read[k * piece..(k + 1) * piece]);
    }
    let (o, sh) = (lane(overflow), lane(share));
    for i in 0..held * piece {
        assert_eq!(o[piece + i] + sh[piece + i], read[i], "{name}: overflow word {i}");
    }
    keys
}

fn prove_toy(toy: &Toy, x: &[u8; 32], seed: &[u8; 32]) -> (Proved, Randomness, SpecKdf, Vec<F64>) {
    let statement = toy_statement(x);
    let cells = toy.circuit.cells(&toy_inputs(x));
    let randomness = Randomness::derive(seed, &toy.index_committed.root, &statement, &cells);
    let spec = spec_derive(seed, &toy.index_committed.root, &statement, &cells);
    let proved = prove_with_randomness(
        &toy.circuit,
        &toy.index,
        &toy.index_committed.root,
        &statement,
        &cells,
        &randomness,
    );
    (proved, randomness, spec, cells)
}

/// The prover's two tables are padded as documented: ChaCha12 per lane, keyed by Keccak-256 of the table's seed
/// and the lane, the table's seed Keccak-256(`"pcs-quotient-pad-"` ‖ name ‖ padding); the masks sit at the witness
/// table's entries `n .. n + 12`, coefficient `i` of row polynomial `j` at `n + 4 i + j`, and `n + 12 .. n + 16` are
/// zero. No two of the 103 lanes share a key, and the two tables' seeds, the padding and the key differ.
#[test]
fn prover_padding_is_chacha12_per_table_and_lane() {
    let toy = toy_setup();
    let x = [0x5A; 32];
    let seed = [0x17; 32];
    let (proved, randomness, spec, _) = prove_toy(&toy, &x, &seed);
    let witness_seed = spec_table_seed(&randomness.padding, b"witness");
    let quotient_seed = spec_table_seed(&randomness.padding, b"quotient");
    let mut keys = check_padding(&proved.tables.witness, &witness_seed, "witness");
    keys.extend(check_padding(&proved.tables.quotient, &quotient_seed, "quotient"));
    keys.extend([
        witness_seed,
        quotient_seed,
        randomness.padding,
        spec.key,
        spec.cells_digest,
        seed,
    ]);
    let distinct: HashSet<_> = keys.iter().collect();
    assert_eq!(distinct.len(), keys.len(), "keys and seeds are pairwise distinct");

    let n = 1usize << (toy.circuit.log_rows + 2);
    let mut mask = vec![F64::ZERO; 1 << LOG_PIECE];
    proved.tables.witness.read(n, &mut mask);
    for j in 0..4 {
        for i in 0..3 {
            assert_eq!(mask[4 * i + j], randomness.masks[j][i], "mask {j}, coefficient {i}");
        }
        assert_eq!(mask[12 + j], F64::ZERO);
    }
    assert!(mask[16..].iter().all(|w| w.is_zero()));
}

/// The masks' words and the padding are uniform 64-bit words (any word is an element of `K = GF(2^64)`, so no
/// value is excluded and none is biased): over 4,000 seeds, every bit of every mask coefficient and of the padding
/// is set within 6 σ of half the time; no mask word ever equals a padding word or another mask word.
#[test]
fn masks_and_padding_bits_are_balanced() {
    let mut rng = Rng::new(0xB17);
    let cells: Vec<F64> = (0..100).map(|_| F64(rng.next_u64())).collect();
    let statement = toy_statement(&[9; 32]);
    let trials = 4000usize;
    let mut mask_bits = vec![[0usize; 64]; 12];
    let mut pad_bits = [0usize; 256];
    for _ in 0..trials {
        let seed: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        let r = Randomness::derive(&seed, &[1; 32], &statement, &cells);
        let words = r.masks.as_flattened();
        let pad = le_words(&r.padding);
        for (k, w) in words.iter().enumerate() {
            assert!(!pad.contains(&w.0) && !words[..k].contains(w));
            for b in 0..64 {
                mask_bits[k][b] += ((w.0 >> b) & 1) as usize;
            }
        }
        for b in 0..256 {
            pad_bits[b] += ((r.padding[b / 8] >> (b % 8)) & 1) as usize;
        }
    }
    let (mean, sigma) = (trials as f64 / 2.0, (trials as f64 / 4.0).sqrt());
    let ok = |c: usize| (c as f64 - mean).abs() < 6.0 * sigma;
    for (k, bits) in mask_bits.iter().enumerate() {
        for (b, &c) in bits.iter().enumerate() {
            assert!(ok(c), "mask word {k}, bit {b}: {c} of {trials}");
        }
    }
    for (b, &c) in pad_bits.iter().enumerate() {
        assert!(ok(c), "padding bit {b}: {c} of {trials}");
    }
}

/// Every nonzero 64-bit word of the proof and its three openings: stream limbs, rows, sibling hashes, the roots.
fn public_words_of(
    proof: &quotient::transcript::Proof,
    roots: &[[u8; 32]; 2],
    openings: &protocol::Openings,
) -> HashSet<u64> {
    let mut words = HashSet::new();
    let scalars = |words: &mut HashSet<u64>, xs: &[F192]| {
        xs.iter().for_each(|x| {
            words.extend([x.c0, x.c1, x.c2]);
        })
    };
    scalars(&mut words, &proof.stream);
    for root in roots {
        words.extend(le_words(root));
    }
    for opening in [&openings.witness, &openings.wiring, &openings.quotient] {
        scalars(&mut words, &opening.stream);
        for paths in &opening.merkle {
            for row in &paths.leaf_data {
                words.extend(row.iter().map(|w| w.0));
            }
            for hash in &paths.sibling_hashes {
                words.extend(le_words(hash));
            }
        }
    }
    words.remove(&0);
    words
}

/// `prove` never repeats: two proofs of one witness share no root and no `a_j`, and both verify with their
/// openings. `derive` hedges: the same seed for the same witness gives the same proof byte for byte; for a
/// witness one input bit apart, nothing in common. And no word of the secrets (the seed, the key, the cells'
/// digest, the padding, the table seeds, the 103 lane keys, the 12 mask words) appears among the words the
/// prover publishes.
#[test]
fn prove_never_repeats_and_hedges() {
    let toy = toy_setup();
    let x = [0x3C; 32];
    let statement = toy_statement(&x);
    let cells = toy.circuit.cells(&toy_inputs(&x));
    let root = &toy.index_committed.root;
    let a = prove(&toy.circuit, &toy.index, root, &statement, &cells);
    let b = prove(&toy.circuit, &toy.index, root, &statement, &cells);
    for (k, (ra, rb)) in a.roots.iter().zip(&b.roots).enumerate() {
        assert_ne!(ra, rb, "root {k}");
    }
    let shared: Vec<_> = a.proof.stream[4..8]
        .iter()
        .filter(|s| b.proof.stream[4..8].contains(s))
        .collect();
    assert!(shared.is_empty(), "the a_j of two proofs");
    for proved in [a, b] {
        let openings = protocol::open(proved.tables, &proved.claims, &toy.index, &toy.index_committed);
        assert_eq!(
            protocol::verify_openings(17, root, &proved.roots, &proved.claims, &openings),
            Ok(())
        );
    }

    let seed = [0xA7; 32];
    let (p1, _, _, _) = prove_toy(&toy, &x, &seed);
    let (p2, r2, spec2, _) = prove_toy(&toy, &x, &seed);
    assert_eq!(p1.proof, p2.proof, "the same seed and witness: the same proof");
    let mut y = x;
    y[0] ^= 1;
    let (p3, r3, _, _) = prove_toy(&toy, &y, &seed);
    assert!(p3.roots.iter().all(|r| !p1.roots.contains(r)));
    let shared = r3
        .masks
        .as_flattened()
        .iter()
        .filter(|w| r2.masks.as_flattened().contains(w))
        .count();
    assert_eq!(shared, 0);
    assert_ne!(r3.padding, r2.padding);

    // The secrets of `p2`, and what it publishes.
    let witness_seed = spec_table_seed(&r2.padding, b"witness");
    let quotient_seed = spec_table_seed(&r2.padding, b"quotient");
    let mut secrets: Vec<u64> = [
        seed,
        spec2.key,
        spec2.cells_digest,
        r2.padding,
        witness_seed,
        quotient_seed,
    ]
    .iter()
    .flat_map(|s| le_words(s))
    .collect();
    for (table_seed, lanes) in [
        (witness_seed, witness_layout(17).lanes()),
        (quotient_seed, quotient_layout(17).lanes()),
    ] {
        for l in 0..lanes {
            secrets.extend(le_words(&spec_lane_key(&table_seed, l)));
        }
    }
    secrets.extend(r2.masks.as_flattened().iter().map(|w| w.0));
    let (proof, roots) = (p2.proof.clone(), p2.roots);
    let openings = protocol::open(p2.tables, &p2.claims, &toy.index, &toy.index_committed);
    let published = public_words_of(&proof, &roots, &openings);
    let leaked: Vec<_> = secrets.iter().filter(|w| published.contains(w)).collect();
    assert!(leaked.is_empty(), "secret words published: {leaked:x?}");
    assert!(published.len() > 10_000, "{} published words", published.len());
}

// ---------------------------------------------------------------------------------------------------------------
// The layout's id.

/// A layout's fields, read back from its encoding.
#[derive(Debug, PartialEq, Eq)]
struct Fields {
    vars: usize,
    log_n: usize,
    lanes: Vec<Lane>,
    log_piece: Option<usize>,
    pieces: Vec<usize>,
    share: Option<usize>,
}

fn fields(layout: &Layout) -> Fields {
    Fields {
        vars: layout.vars,
        log_n: layout.log_n,
        lanes: (0..layout.lanes()).map(|l| layout.lane(l)).collect(),
        log_piece: layout.log_piece(),
        pieces: layout.pieces().to_vec(),
        share: layout.share(),
    }
}

/// `encode_layout`, from its doc comment and `Layout`'s public accessors.
fn encode(f: &Fields) -> Vec<u8> {
    let mut bytes = vec![];
    let mut put = |n: usize| bytes.extend_from_slice(&(n as u64).to_le_bytes());
    put(f.vars);
    put(f.log_n);
    put(f.lanes.len());
    for lane in &f.lanes {
        let (kind, block) = match *lane {
            Lane::Block(b) => (0, b),
            Lane::Overflow => (1, 0),
            Lane::Random => (2, 0),
        };
        put(kind);
        put(block);
    }
    let option = |v: Option<usize>, put: &mut dyn FnMut(usize)| match v {
        None => put(0),
        Some(v) => {
            put(1);
            put(v)
        }
    };
    option(f.log_piece, &mut put);
    put(f.pieces.len());
    f.pieces.iter().for_each(|&p| put(p));
    option(f.share, &mut put);
    bytes
}

/// The encoding's inverse: `None` on a byte string no layout encodes to (a bad tag, a short read, bytes left).
fn decode(bytes: &[u8]) -> Option<Fields> {
    let mut words = bytes.as_chunks::<8>().0.iter().map(|&c| u64::from_le_bytes(c) as usize);
    if !bytes.len().is_multiple_of(8) {
        return None;
    }
    let mut next = || words.next();
    let (vars, log_n, count) = (next()?, next()?, next()?);
    let mut lanes = vec![];
    for _ in 0..count {
        let (kind, block) = (next()?, next()?);
        lanes.push(match (kind, block) {
            (0, b) => Lane::Block(b),
            (1, 0) => Lane::Overflow,
            (2, 0) => Lane::Random,
            _ => return None,
        });
    }
    let option = |next: &mut dyn FnMut() -> Option<usize>| -> Option<Option<usize>> {
        match next()? {
            0 => Some(None),
            1 => Some(Some(next()?)),
            _ => None,
        }
    };
    let log_piece = option(&mut next)?;
    let held = next()?;
    let pieces = (0..held).map(|_| next()).collect::<Option<Vec<_>>>()?;
    let share = option(&mut next)?;
    next().is_none().then_some(Fields {
        vars,
        log_n,
        lanes,
        log_piece,
        pieces,
        share,
    })
}

/// Whether `Layout::hidden_with` takes these arguments (its assertions, computed rather than caught).
fn hidden_takes(
    vars: usize,
    log_chunk: usize,
    log_n: usize,
    chunks: &[(usize, usize)],
    random: usize,
    s: usize,
) -> bool {
    let log_lane = log_n - opening::LANE_FOLD;
    if !(s < log_lane && log_lane <= log_chunk && log_chunk <= vars) {
        return false;
    }
    if chunks
        .iter()
        .any(|&(c, len)| c >> (vars - log_chunk) != 0 || len > 1 << log_chunk)
    {
        return false;
    }
    let blocks: usize = chunks.iter().map(|&(_, len)| len >> log_lane).sum();
    let tails: usize = chunks
        .iter()
        .map(|&(_, len)| (len - ((len >> log_lane) << log_lane)).div_ceil(1 << s))
        .sum();
    let total = blocks + 1 + random;
    if random < 4 || total > 64 {
        return false;
    }
    let pairs = (total - 2) / 2;
    let at: HashSet<usize> = (0..random - 1).map(|k| 2 * (k * pairs / (random - 1)) + 1).collect();
    let pieces = blocks + tails;
    at.len() == random - 1 && pieces > 0 && pieces < 1 << (log_lane - s)
}

fn new_takes(vars: usize, log_chunk: usize, log_n: usize, chunks: &[(usize, usize)]) -> bool {
    let log_lane = log_n - opening::LANE_FOLD;
    if !(log_lane <= log_chunk && log_chunk <= vars) {
        return false;
    }
    if chunks
        .iter()
        .any(|&(c, len)| c >> (vars - log_chunk) != 0 || len > 1 << log_chunk)
    {
        return false;
    }
    let blocks: usize = chunks.iter().map(|&(_, len)| len.div_ceil(1 << log_lane)).sum();
    blocks > 0 && blocks <= 64
}

/// The protocol's 18 layouts, and some 200 more of both kinds.
fn many_layouts() -> Vec<Layout> {
    let mut layouts = vec![];
    for log_rows in MIN_LOG_ROWS..=MAX_LOG_ROWS {
        layouts.extend([
            witness_layout(log_rows),
            wiring_layout(log_rows),
            quotient_layout(log_rows),
        ]);
    }
    for (vars, log_chunk, log_n) in [
        (15, 15, 15),
        (16, 15, 15),
        (16, 16, 16),
        (17, 15, 16),
        (20, 15, 20),
        (21, 15, 20),
        (20, 14, 20),
        (20, 16, 20),
    ] {
        let full = 1usize << log_chunk;
        let chunk_sets: Vec<Vec<(usize, usize)>> = vec![
            vec![(0, full)],
            vec![(0, 3000)],
            vec![(1, full)],
            vec![(0, full), (1, 16)],
            vec![(0, 1)],
            vec![(0, full / 2)],
            vec![(3, full), (0, 3000)],
            vec![(0, 3000), (3, full)],
            vec![(0, full / 2 + 1)],
        ];
        for chunks in &chunk_sets {
            if new_takes(vars, log_chunk, log_n, chunks) {
                layouts.push(Layout::new(vars, log_chunk, log_n, chunks));
            }
            for random in [4, 5, 7] {
                for s in [2, 3, 5, LOG_PIECE] {
                    if hidden_takes(vars, log_chunk, log_n, chunks, random, s) {
                        layouts.push(Layout::hidden_with(vars, log_chunk, log_n, chunks, random, s));
                    }
                }
            }
        }
    }
    layouts
}

/// `layout_id` is Keccak-256 of the documented encoding, which a decoder inverts: the id is injective up to a
/// Keccak-256 collision, and it covers every field the verifier reads (vars, the stack's size, the lanes, the
/// piece, the overflow pieces, the share lane). Over the 18 deployed layouts and ~200 more: equal ids and equal
/// prefixes exactly for equal layouts. The prefix is 76 bytes of fixed-width fields, the id at bytes `28..60`.
#[test]
fn layout_id_is_injective() {
    let layouts = many_layouts();
    assert!(layouts.len() > 150, "{} layouts", layouts.len());
    let mut by_id: HashMap<[u8; 32], usize> = HashMap::new();
    for (i, layout) in layouts.iter().enumerate() {
        let f = fields(layout);
        let bytes = encode(&f);
        assert_eq!(
            keccak(&[&bytes]),
            opening::layout_id(layout),
            "layout {i}: the id is the documented encoding's hash"
        );
        assert_eq!(decode(&bytes).as_ref(), Some(&f), "layout {i}: the encoding decodes");
        // No proper prefix of an encoding decodes, nor the encoding with a word more.
        for cut in (0..bytes.len()).step_by(8) {
            assert_eq!(decode(&bytes[..cut]), None, "layout {i}: a prefix of {cut} bytes");
        }
        assert_eq!(decode(&[&bytes[..], &[0; 8]].concat()), None);
        let pre = opening::prefix(layout);
        assert_eq!(pre.len(), PREFIX_LEN);
        assert_eq!(
            pre.to_vec(),
            [
                &b"pcs-quotient-opening"[..],
                &VERSION.to_le_bytes(),
                &opening::layout_id(layout),
                &(layout.log_n as u64).to_le_bytes(),
                &(LOG_INV_RATE as u64).to_le_bytes(),
            ]
            .concat()
        );
        if let Some(&j) = by_id.get(&opening::layout_id(layout)) {
            assert_eq!(layouts[j], *layout, "layouts {j} and {i} share an id");
        }
        by_id.insert(opening::layout_id(layout), i);
    }
    for (i, a) in layouts.iter().enumerate() {
        for b in &layouts[i + 1..] {
            assert_eq!(a == b, opening::prefix(a) == opening::prefix(b));
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The opening's transcript.

fn claim_bytes(claims: &[Claim]) -> Vec<u8> {
    claims
        .iter()
        .flat_map(|c| c.point.iter().chain([&c.value]))
        .flat_map(|x| [x.c0, x.c1, x.c2])
        .flat_map(|l| l.to_le_bytes())
        .collect()
}

/// The version-1 seed, `(keccak256(LABEL), keccak256(root ‖ claims))` (`VERSION`'s doc comment), hashed no layout and
/// no count of claims: two claims under a layout of `v` variables and one claim under a layout of `2v + 1` wrote the
/// same bytes, so the two openings shared their transcript. The prefix (the layout's id) separates them now; the IV
/// is also the documented hash, recomputed.
#[test]
fn version_one_conflated_claim_lists_and_the_prefix_does_not() {
    let a = Layout::new(16, 15, 15, &[(0, 1 << 15)]);
    let b = Layout::new(33, 15, 15, &[(0, 1 << 15)]);
    let mut rng = Rng::new(0x1E1);
    let c1 = Claim {
        point: rng.ext_vec(16),
        value: rng.ext(),
    };
    let c2 = Claim {
        point: rng.ext_vec(16),
        value: rng.ext(),
    };
    let joined = Claim {
        point: [&c1.point[..], &[c1.value], &c2.point[..]].concat(),
        value: c2.value,
    };
    let (two, one) = (vec![c1, c2], vec![joined]);
    assert_eq!(claim_bytes(&two), claim_bytes(&one), "the claims write the same bytes");
    let root = [0x42; 32];
    let v1 = |claims: &[Claim]| keccak(&[&root, &claim_bytes(claims)]);
    assert_eq!(v1(&two), v1(&one), "version 1: one seed for both");
    assert_ne!(
        opening::iv(&a, &two),
        opening::iv(&b, &one),
        "version 2: the prefix separates them"
    );
    for (layout, claims) in [(&a, &two), (&b, &one)] {
        assert_eq!(
            opening::iv(layout, claims),
            keccak(&[&opening::prefix(layout), &claim_bytes(claims)])
        );
    }
}

/// A table of `layout`, every entry it holds pseudo-random (hidden: padded from `seed`), committed, with `count`
/// true claims at random points, opened.
fn opened(layout: &Layout, count: usize, seed: u64) -> (Table, opening::Committed, Vec<Claim>, verifier::Proof) {
    let pseudo = |i: usize| F64(((i as u64) + seed).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(23));
    let table = if layout.log_piece().is_some() {
        Table::hidden(layout.clone(), &[seed as u8; 32], |start, out| {
            out.iter_mut().enumerate().for_each(|(k, o)| *o = pseudo(start + k));
        })
    } else {
        let lane = 1usize << layout.log_lane();
        Table::new(layout.clone(), |l, _, out| {
            out.iter_mut().enumerate().for_each(|(k, o)| *o = pseudo(l * lane + k));
        })
    };
    let mut rng = Rng::new(seed);
    let claims: Vec<Claim> = (0..count)
        .map(|_| {
            let point = rng.ext_vec(layout.vars);
            Claim {
                value: table.eval(&point),
                point,
            }
        })
        .collect();
    let committed = opening::commit(&table);
    let proof = opening::wire_proof(&opening::open(&table, &committed, &claims));
    assert_eq!(opening::verify(layout, &committed.root, &claims, &proof), Ok(()));
    (table, committed, claims, proof)
}

/// The layouts that share `vars` and `log_n` are the witness layout at `2^r` rows and the wiring layout at
/// `2^(r+1)` (`m + 1` both); among the 18 no other two do. An opening under one is rejected under the other, both
/// ways, with the same root and claims; the quotient layout's opening is rejected under the one layout of its arity
/// (the witness layout at `2^22` rows), and by the shape check under layouts of another arity.
#[test]
fn openings_do_not_replay_across_layouts() {
    let mut shapes: HashMap<(usize, usize), Vec<String>> = HashMap::new();
    for r in MIN_LOG_ROWS..=MAX_LOG_ROWS {
        for (name, layout) in [
            ("witness", witness_layout(r)),
            ("wiring", wiring_layout(r)),
            ("quotient", quotient_layout(r)),
        ] {
            shapes
                .entry((layout.vars, layout.log_n))
                .or_default()
                .push(format!("{name} {r}"));
        }
    }
    let shared: Vec<_> = shapes.values().filter(|v| v.len() > 1).collect();
    assert_eq!(shared.len(), MAX_LOG_ROWS - MIN_LOG_ROWS, "{shared:?}");
    assert!(
        shared
            .iter()
            .all(|v| v.len() == 2 && v[0].starts_with("witness") && v[1].starts_with("wiring"))
    );

    let (hidden, public) = (witness_layout(17), wiring_layout(18));
    assert_eq!((hidden.vars, hidden.log_n), (public.vars, public.log_n));
    for (from, to) in [(&hidden, &public), (&public, &hidden)] {
        let (_, committed, claims, proof) = opened(from, 1, 0x77);
        let other = opening::verify(to, &committed.root, &claims, &proof);
        assert!(other.is_err(), "{other:?}");
    }
    // Same arity, another stack: the quotient layout at `2^17` rows and the witness layout at `2^22` (25
    // variables, stacks of `2^23` and `2^25`), the only other pair of the 18 with equal `vars`. The claims pass the
    // shape check; the transcript (another IV) and the WHIR shape reject.
    let (_, committed, claims, proof) = opened(&quotient_layout(17), 2, 0x78);
    assert_eq!(quotient_layout(17).vars, witness_layout(22).vars);
    let other = opening::verify(&witness_layout(22), &committed.root, &claims, &proof);
    assert!(other.is_err() && other != Err(VerifierError::WhirShape), "{other:?}");
    for to in [witness_layout(17), wiring_layout(17)] {
        assert_eq!(
            opening::verify(&to, &committed.root, &claims, &proof),
            Err(VerifierError::WhirShape)
        );
    }
}

/// The root rides the proof as its first two scalars, read and checked before the first challenge: a third limb
/// set is `DigestHalf`, the halves swapped or one bit changed is `MerkleRootMismatch`, and so is the right proof
/// against another root. The encoding is a bijection (`Digest::from_halves` inverts `hash_to_scalars` and nothing
/// else reaches the same digest), so no second encoding of the root passes. A proof whose first two scalars are
/// re-written for another root (as a forger would, to keep the root check) fails further on.
#[test]
fn root_scalars_are_canonical_and_checked_first() {
    let mut rng = Rng::new(0x2007);
    for _ in 0..1000 {
        let root: [u8; 32] = std::array::from_fn(|_| rng.next_u8());
        let [s0, s1] = hash_to_scalars(&root);
        let to = |x: F192| verifier::E::new(x.c0, x.c1, x.c2);
        assert_eq!(Digest::from_halves(to(s0), to(s1)), Ok(Digest(root)));
        let (h, limb, bit) = (
            (rng.next_u64() & 1) as usize,
            (rng.next_u64() % 3) as usize,
            rng.next_u64() % 64,
        );
        let mut halves = [to(s0), to(s1)];
        let x = &mut halves[h];
        match limb {
            0 => x.c0 ^= 1 << bit,
            1 => x.c1 ^= 1 << bit,
            _ => x.c2 ^= 1 << bit,
        }
        let other = Digest::from_halves(halves[0], halves[1]);
        assert!(other.is_err() || other != Ok(Digest(root)));
        assert_eq!(other.is_err(), limb == 2);
    }

    let layout = witness_layout(17);
    let (_, committed, claims, proof) = opened(&layout, 1, 0x99);
    let check = |proof: &verifier::Proof, root: &[u8; 32]| opening::verify(&layout, root, &claims, proof);
    let mut third = proof.clone();
    third.stream[1].c2 = 1;
    assert_eq!(check(&third, &committed.root), Err(VerifierError::DigestHalf));
    let mut swapped = proof.clone();
    swapped.stream.swap(0, 1);
    assert_eq!(check(&swapped, &committed.root), Err(VerifierError::MerkleRootMismatch));
    for bit in [0, 63, 64, 127] {
        let mut flipped = proof.clone();
        let x = &mut flipped.stream[bit / 128];
        if bit % 128 < 64 {
            x.c0 ^= 1 << (bit % 64);
        } else {
            x.c1 ^= 1 << (bit % 64);
        }
        assert_eq!(
            check(&flipped, &committed.root),
            Err(VerifierError::MerkleRootMismatch),
            "bit {bit}"
        );
    }
    let mut elsewhere = committed.root;
    elsewhere[31] ^= 0x80;
    assert_eq!(check(&proof, &elsewhere), Err(VerifierError::MerkleRootMismatch));
    let mut relabelled = proof.clone();
    let [e0, e1] = hash_to_scalars(&elsewhere);
    relabelled.stream[0] = verifier::E::new(e0.c0, e0.c1, 0);
    relabelled.stream[1] = verifier::E::new(e1.c0, e1.c1, 0);
    let result = check(&relabelled, &elsewhere);
    assert!(result.is_err(), "{result:?}");
    assert_ne!(result, Err(VerifierError::DigestHalf));

    // A stream cut before, at or after the root's scalars: an error, not a panic.
    for keep in [0, 1, 2, 3] {
        let mut cut = proof.clone();
        cut.stream.truncate(keep);
        assert_eq!(check(&cut, &committed.root), Err(VerifierError::StreamExhausted), "{keep} scalars");
    }
}

/// The claims an opening is of, exactly, in order: reordered, one dropped, one duplicated, a true one appended, a
/// value changed, are each rejected; a claim of the wrong arity is `WhirShape` before anything is read. An opening of
/// no claims at all is **accepted**: it proves nothing (the target and the weight are zero), and `PCS_OPEN` asks for
/// `k ≥ 1`.
#[test]
fn claim_lists_are_bound_exactly() {
    let layout = quotient_layout(17);
    let (table, committed, claims, proof) = opened(&layout, 3, 0xC1A);
    let root = committed.root;
    let verify = |claims: &[Claim]| opening::verify(&layout, &root, claims, &proof);
    assert_eq!(verify(&claims), Ok(()));
    let mut rng = Rng::new(5);
    let point = rng.ext_vec(layout.vars);
    let extra = Claim {
        value: table.eval(&point),
        point,
    };
    let lists: Vec<(&str, Vec<Claim>)> = vec![
        (
            "reordered",
            vec![claims[1].clone(), claims[0].clone(), claims[2].clone()],
        ),
        ("dropped", claims[..2].to_vec()),
        (
            "duplicated",
            vec![
                claims[0].clone(),
                claims[0].clone(),
                claims[1].clone(),
                claims[2].clone(),
            ],
        ),
        ("appended", [&claims[..], &[extra]].concat()),
        ("value", {
            let mut c = claims.clone();
            c[2].value += F192::ONE;
            c
        }),
    ];
    for (name, list) in lists {
        assert!(verify(&list).is_err(), "{name}");
    }
    let mut short = claims.clone();
    short[1].point.pop();
    assert_eq!(verify(&short), Err(VerifierError::WhirShape));
    let mut long = claims.clone();
    long[0].point.push(F192::ZERO);
    assert_eq!(verify(&long), Err(VerifierError::WhirShape));

    // No claims: accepted, of a table it says nothing about.
    let empty = opening::wire_proof(&opening::open(&table, &committed, &[]));
    assert_eq!(opening::verify(&layout, &root, &[], &empty), Ok(()));
    assert!(opening::verify(&layout, &root, &claims[..1], &empty).is_err());
}

/// Every claim's bytes in the IV are its point then its value, three little-endian limbs each, so a field element is
/// read back exactly: no two claim lists of one layout share an IV unless they are equal (the length fixes the
/// count, the layout the arity).
#[test]
fn iv_reads_back_the_claims() {
    let layout = wiring_layout(17);
    let mut rng = Rng::new(0x1717);
    let claims: Vec<Claim> = (0..3)
        .map(|_| Claim {
            point: rng.ext_vec(layout.vars),
            value: rng.ext(),
        })
        .collect();
    let bytes = claim_bytes(&claims);
    let per = 24 * (layout.vars + 1);
    assert_eq!(bytes.len(), 3 * per);
    let back: Vec<Claim> = bytes
        .chunks_exact(per)
        .map(|c| {
            let xs: Vec<F192> = c
                .as_chunks::<24>()
                .0
                .iter()
                .map(|e| {
                    let w = le_words(e);
                    F192::new(w[0], w[1], w[2])
                })
                .collect();
            let (value, point) = xs.split_last().unwrap();
            Claim {
                point: point.to_vec(),
                value: *value,
            }
        })
        .collect();
    assert_eq!(back, claims);
    assert_eq!(
        opening::iv(&layout, &claims),
        keccak(&[&opening::prefix(&layout), &bytes])
    );
    assert_eq!(opening::PUBLIC_DIGEST, [0; 32]);
}
