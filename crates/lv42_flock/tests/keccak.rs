// New in this repository: tests of `lv42_flock::keccak` (the Keccak-f[1600] block, crates/slh_dsa/SPEC-FAST.md
// §4.2, §4.5). MIT OR Apache-2.0; see NOTICE.md.
//! The Keccak-f block R1CS:
//!
//! - its Keccak-f is RustCrypto's (`keccak::Keccak::with_f1600`, sha3's permutation) on random states;
//! - the witness satisfies `(A_0 z)·(B_0 z) = z` on every row of every block (padding blocks too), its port quads hold
//!   what SPEC-FAST §4.5 says, and its lincheck stripes are `z`'s transpose;
//! - every flipped witness bit (in each region: inputs, products, states, outputs, copies, constants, padding) breaks
//!   a row;
//! - the rows that are not empty are exactly the layout's slots;
//! - the backward walk is the forward walk's transpose.
//!
//! `cargo test --release -p lv42_flock --test keccak`

use lv42_flock::keccak::*;
use primitives::field::F192;

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
    fn ext(&mut self) -> F192 {
        F192::new(self.next(), self.next(), self.next())
    }
}

fn reference(mut state: [u64; LANES]) -> [u64; LANES] {
    keccak::Keccak::new().with_f1600(|f| f(&mut state));
    state
}

fn bits_of(block: &[u64]) -> Vec<F192> {
    (0..K)
        .map(|i| if block[i / 64] >> (i % 64) & 1 == 1 { F192::ONE } else { F192::ZERO })
        .collect()
}

/// The rows `(A_0 z)·(B_0 z) = z` that fail, of one block's bits.
fn failing_rows(block: &[u64]) -> Vec<usize> {
    let z = bits_of(block);
    let (a, b) = row_values_walk(&z);
    (0..K).filter(|&i| a[i] * b[i] != z[i]).collect()
}

#[test]
fn keccak_f_is_rustcryptos() {
    let mut rng = Rng(0x6b65_6363_616b);
    for _ in 0..64 {
        let s = rng.state();
        let mut ours = s;
        keccak_f(&mut ours);
        assert_eq!(ours, reference(s));
    }
    let mut zero = PADDING_INPUT;
    keccak_f(&mut zero);
    assert_eq!(zero, reference([0; LANES]));
    // FIPS 202's Keccak-f[1600] of the zero state, lane 0.
    assert_eq!(zero[0], 0xF1258F7940E1DDE7);
}

#[test]
fn witness_satisfies_every_row_and_holds_the_ports() {
    let mut rng = Rng(0x5157_4e55);
    let n = 13;
    let inputs: Vec<[u64; LANES]> = (0..n).map(|_| rng.state()).collect();
    let n_blocks_log = min_n_blocks_log(n);
    let (z, a, b, stripes) = generate_witness_with_ab_packed_and_lincheck(&inputs, n_blocks_log);
    let blocks = 1usize << n_blocks_log;
    assert_eq!(z.len(), blocks * WORDS);
    for i in 0..blocks {
        let block = &z[i * WORDS..(i + 1) * WORDS];
        let input = if i < n { inputs[i] } else { PADDING_INPUT };
        assert_eq!(failing_rows(block), Vec::<usize>::new(), "block {i}");
        // a and b are the rows' values, and c = z = a·b.
        let (zb, ab, bb) = (bits_of(block), bits_of(&a[i * WORDS..][..WORDS]), bits_of(&b[i * WORDS..][..WORDS]));
        let (left, right) = row_values_walk(&zb);
        assert!(left == ab && right == bb, "block {i}: the packed A z, B z");
        // The ports (SPEC-FAST §4.5).
        let output = reference(input);
        assert_eq!(block_input(block), input);
        assert_eq!(block_output(block), output);
        for q in 0..QUADS {
            let quad: [u64; 4] = std::array::from_fn(|r| block[port_word(q, r)]);
            let want = if q < LANES {
                [output[q], 1, input[q], output[q]]
            } else if q == X_QUAD {
                [2, 1, 0, 2]
            } else {
                [0, 1, 0, 0]
            };
            assert_eq!(quad, want, "block {i} quad {q}");
        }
        assert!(block[USEFUL_BITS / 64..].iter().all(|&w| w == 0), "the padding suffix is zero");
    }
    // The stripes: byte `g k + i` holds bit `i` of blocks `8 g..8 g + 8`, bit `r` block `8 g + r`.
    assert_eq!(stripes.len(), K * (blocks / 8));
    for g in 0..blocks / 8 {
        for i in (0..K).step_by(7) {
            let want = (0..8).fold(0u8, |acc, r| acc | (((z[(8 * g + r) * WORDS + i / 64] >> (i % 64)) & 1) as u8) << r);
            assert_eq!(stripes[g * K + i], want);
        }
    }
}

#[test]
fn a_flipped_bit_breaks_a_row() {
    let mut rng = Rng(0xf11b);
    let input = rng.state();
    let (z, ..) = generate_witness_with_ab_packed_and_lincheck(&[input], 3);
    let block = &z[..WORDS];
    let slots = [
        64 * port_word(3, ROLE_C) + 17,  // an input bit
        64 * port_word(7, ROLE_X) + 5,   // an output bit
        64 * port_word(7, ROLE_V) + 63,  // its copy
        64 * port_word(9, ROLE_Y),       // a constant 1
        CONST_POS,                       // the constant wire
        64 * port_word(X_QUAD, ROLE_X) + 1,
        64 * port_word(X_QUAD, ROLE_C) + 4,
        64 * port_word(30, ROLE_Y) + 1,  // an empty slot of a Y word
        64 * t_word(0, 0),               // a product
        64 * t_word(11, 24) + 40,
        64 * a_word(0, 12) + 2,          // a state
        64 * a_word(22, 24) + 63,
        64 * t_word(3, 0) + 64 * 25 + 7, // an empty lane of a run
        USEFUL_BITS + 100,               // the padding suffix
        K - 1,
    ];
    for s in slots {
        let mut flipped = block.to_vec();
        flipped[s / 64] ^= 1 << (s % 64);
        assert!(!failing_rows(&flipped).is_empty(), "flipping slot {s} breaks no row");
    }
    // Every bit of one state lane and one product lane.
    for s in (64 * a_word(5, 6)..64 * a_word(5, 6) + 64).chain(64 * t_word(17, 3)..64 * t_word(17, 3) + 64) {
        let mut flipped = block.to_vec();
        flipped[s / 64] ^= 1 << (s % 64);
        assert!(!failing_rows(&flipped).is_empty(), "flipping slot {s} breaks no row");
    }
    // The all-zero block satisfies every row (homogeneous); the lincheck's pin on the constant wire rules it out.
    assert!(failing_rows(&vec![0; WORDS]).is_empty());
    assert_eq!(block[CONST_POS / 64] & 1, 1);
}

#[test]
fn constrained_rows_tile_the_layout() {
    let mut rng = Rng(0x7113D);
    let w: Vec<F192> = (0..K).map(|_| rng.ext()).collect();
    let (va, vb) = row_values_walk(&w);
    let mut expected = vec![false; K];
    for q in 0..QUADS {
        expected[64 * port_word(q, ROLE_Y)] = true;
        if q < LANES {
            for r in [ROLE_X, ROLE_C, ROLE_V] {
                expected[64 * port_word(q, r)..][..64].fill(true);
            }
        }
    }
    expected[64 * port_word(X_QUAD, ROLE_X) + 1] = true;
    expected[64 * port_word(X_QUAD, ROLE_V) + 1] = true;
    for j in 0..ROUNDS {
        for l in 0..LANES {
            expected[64 * t_word(j, l)..][..64].fill(true);
            if j < ROUNDS - 1 {
                expected[64 * a_word(j, l)..][..64].fill(true);
            }
        }
    }
    // 32 Y bits, 25 lanes × (X, C, V), x's two bits; 24 t_j and 23 A_j of 1,600 bits.
    assert_eq!(expected.iter().filter(|&&e| e).count(), 32 + 25 * 3 * 64 + 2 + 47 * 1600);
    for s in 0..K {
        let constrained = va[s] != F192::ZERO || vb[s] != F192::ZERO;
        assert_eq!(constrained, expected[s], "slot {s}");
    }
    // The rows' sizes: products 12 + 11 nonzeros, states 12 (13 with ι's bit) + 1, as the module says. A row's A side
    // at a w with one 1 is 1 or 0; sum A over unit columns by the backward walk at a unit row.
    let unit = |s: usize| {
        let mut u = vec![F192::ZERO; K];
        u[s] = F192::ONE;
        u
    };
    let zero = vec![F192::ZERO; K];
    let count = |m: &[F192]| m.iter().filter(|&&x| x != F192::ZERO).count();
    assert_eq!(count(&marginal_walk_sides(&unit(64 * t_word(4, 7) + 9), &zero)), 12);
    assert_eq!(count(&marginal_walk_sides(&zero, &unit(64 * t_word(4, 7) + 9))), 11);
    assert_eq!(count(&marginal_walk_sides(&unit(64 * a_word(4, 7) + 9), &zero)), 12);
    // RC_0 = 1: lane 0 bit 0 of A_0 also reads the constant.
    assert_eq!(count(&marginal_walk_sides(&unit(64 * a_word(0, 0)), &zero)), 13);
    assert_eq!(count(&marginal_walk_sides(&zero, &unit(64 * a_word(4, 7) + 9))), 1);
}

#[test]
fn the_backward_walk_is_the_transpose() {
    let mut rng = Rng(0xAD10_1234);
    let w: Vec<F192> = (0..K).map(|_| rng.ext()).collect();
    let u: Vec<F192> = (0..K).map(|_| rng.ext()).collect();
    let v: Vec<F192> = (0..K).map(|_| rng.ext()).collect();
    let (a, b) = row_values_walk(&w);
    let m = marginal_walk_sides(&u, &v);
    let dot = |x: &[F192], y: &[F192]| x.iter().zip(y).fold(F192::ZERO, |acc, (&p, &q)| acc + p * q);
    assert_eq!(dot(&u, &a) + dot(&v, &b), dot(&m, &w));
    let alpha = rng.ext();
    let batched = marginal_walk(alpha, &u);
    assert_eq!(dot(&batched, &w), dot(&u, &a) + alpha * dot(&u, &b));
}
