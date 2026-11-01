// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, crates/flock/src/membership.rs (`Statement`, `Secret`, `halves`),
// with Keccak-256 in place of BLAKE2s. MIT OR Apache-2.0; see NOTICE.md.
//! The statement: `y = H(x | 0x11^32)`, and a Merkle path of depth [`DEPTH`] from `H(x | 0x22^32)` up to
//! `root`, with `H` = Keccak-256 (Ethereum's `keccak256`) of a 64-byte block.

use primitives::field::F192;
use primitives::hash::hash as keccak256;

pub const DEPTH: usize = 32;

/// The domain constants the leaf and `y` are hashed with.
pub const Y_PAD: u8 = 0x11;
pub const LEAF_PAD: u8 = 0x22;

/// `H(left | right)`.
pub fn pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    keccak256(&[*left, *right].concat())
}

/// The public values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Statement {
    pub y: [u8; 32],
    pub root: [u8; 32],
}

impl Statement {
    /// `y` then `root`, each as its two [`halves`].
    pub fn halves(&self) -> [F192; 4] {
        let ([y0, y1], [root0, root1]) = (halves(&self.y), halves(&self.root));
        [y0, y1, root0, root1]
    }
}

/// What the prover knows. Bit `i` of `directions` says the sibling is on the left at level `i`.
#[derive(Clone, Debug)]
pub struct Secret {
    pub x: [u8; 32],
    pub siblings: [[u8; 32]; DEPTH],
    pub directions: u32,
}

impl Secret {
    /// The statement this secret proves, by hashing natively.
    pub fn statement(&self) -> Statement {
        let leaf = pair(&self.x, &[LEAF_PAD; 32]);
        let root = self.siblings.iter().enumerate().fold(leaf, |node, (i, sibling)| {
            if (self.directions >> i) & 1 == 1 {
                pair(sibling, &node)
            } else {
                pair(&node, sibling)
            }
        });
        Statement {
            y: pair(&self.x, &[Y_PAD; 32]),
            root,
        }
    }
}

/// A 32-byte value as two field elements, sixteen bytes each read as a big-endian number in the low two limbs.
pub fn halves(bytes: &[u8; 32]) -> [F192; 2] {
    std::array::from_fn(|h| {
        let v = u128::from_be_bytes(bytes[16 * h..16 * h + 16].try_into().unwrap());
        F192::new(v as u64, (v >> 64) as u64, 0)
    })
}
