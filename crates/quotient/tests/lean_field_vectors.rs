// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The `F192` test vectors of `formal/Field/Test.lean`: products, inverses and a Frobenius of
//! `primitives::field::F192`, which the Lean field (`Primitives.F192`, CompPoly's `BF64.Ext3`) must
//! reproduce limb for limb. The last four products are the Python reference vectors of
//! `gf2_64x3.rs`'s own tests.

use primitives::field::F192;

const ONES: F192 = F192::new(u64::MAX, u64::MAX, u64::MAX);
const TOPS: F192 = F192::new(1 << 63, 1 << 63, 1 << 63);
const X: F192 = F192::new(2, 0, 0);
const X63: F192 = F192::new(1 << 63, 0, 0);
const A: F192 = F192::new(0x950e87d7f5606615, 0x2c61275c9e6b6cf8, 0x1f00bca0042db923);
const B: F192 = F192::new(0x6dbca290a9eab706, 0x4c10a4fe30cffdda, 0xf26fff4cc4fd394d);

/// `(a, b, a * b)`, as limbs.
type Product = ([u64; 3], [u64; 3], [u64; 3]);

fn limbs(v: F192) -> [u64; 3] {
    [v.c0, v.c1, v.c2]
}

const PRODUCTS: [Product; 13] = [
    ([u64::MAX; 3], [u64::MAX; 3], [0x5555555555555513, 0x5555555555555513, 0]),
    ([1 << 63; 3], [1 << 63; 3], [0xc00000000000005a, 0xc00000000000005a, 0]),
    ([u64::MAX; 3], [1 << 63; 3], [0x65, 0x65, 0]),
    (
        [0x950e87d7f5606615, 0x2c61275c9e6b6cf8, 0x1f00bca0042db923],
        [u64::MAX; 3],
        [0xf732f696ccf14373, 0x4e7f3bdaf2bc8b22, 0xe537c4a915aa5ba0],
    ),
    ([0, 1, 0], [0, 1, 0], [0, 0, 1]),
    ([0, 0, 1], [0, 1, 0], [1, 1, 0]),
    ([1 << 63, 0, 0], [2, 0, 0], [0x1b, 0, 0]),
    ([1 << 63, 0, 0], [1 << 63, 0, 0], [0xc00000000000005a, 0, 0]),
    ([0x800000000000000d, 0, 0], [2, 0, 0], [1, 0, 0]),
    (
        [0x950e87d7f5606615, 0x2c61275c9e6b6cf8, 0x1f00bca0042db923],
        [0x6dbca290a9eab706, 0x4c10a4fe30cffdda, 0xf26fff4cc4fd394d],
        [0x888a0fc35abaf5f6, 0x68a84cbc132b0649, 0x9fdeaf613003cabe],
    ),
    (
        [0x6814a2bc786a6d2d, 0xa26b351e6c8042c5, 0x54760e7fbc051c6c],
        [0xd4c08880a5a4666d, 0x29610ae0eed8f1e7, 0xc34bd8e2fe5213e5],
        [0x2ad322ebf2f9043b, 0x8ac800aa67154c80, 0x6d0f76651d3c4d0c],
    ),
    (
        [0x6c50afb6e9fb123d, 0x6f28d015a2aa0b9d, 0x4e385994ebac94af],
        [0x194f9545adba52ce, 0xc675ce05588f882f, 0x57de8c051d4b7ef2],
        [0xea6b9f9d23d4a1ff, 0xd82aa6058c431457, 0x5fd4d8fda2f1e74a],
    ),
    (
        [0xd998efd82733e933, 0x6df216c33f8f3201, 0x11dc6f3fcb57d5d8],
        [0x8860a84722025e05, 0x33176469aa6ef630, 0x607507ebc5b864d7],
        [0xfa3a0d66cdfbc1b3, 0xbd47bd3343aad307, 0xdaf50186477f6a77],
    ),
];

#[test]
fn products() {
    for (a, b, c) in PRODUCTS {
        let (a, b) = (F192::new(a[0], a[1], a[2]), F192::new(b[0], b[1], b[2]));
        assert_eq!(limbs(a * b), c);
    }
    assert_eq!(ONES * ONES, F192::new(0x5555555555555513, 0x5555555555555513, 0));
    assert_eq!(TOPS * X63, X63 * TOPS);
}

#[test]
fn inverses_and_frobenius() {
    assert_eq!(limbs(A.inv()), [0x54585269244a53bf, 0xe61abf3f20ceabe4, 0x8eb77d6b827e0877]);
    assert_eq!(limbs(X.inv()), [0x800000000000000d, 0, 0]);
    assert_eq!(limbs(F192::Y.inv()), [1, 0, 1]);
    assert_eq!(limbs(A.frobenius()), [0x950e87d7f5606615, 0x1f00bca0042db923, 0x33619bfc9a46d5db]);
    assert_eq!(A * A.inv(), F192::ONE);
    assert_eq!(A * B, B * A);
}
