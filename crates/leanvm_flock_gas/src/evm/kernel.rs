// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Hand-scheduled code for the ring switch's weight at a point ([`crate::ring_tower::weight_at`]), the one
//! computation of the univariate verifier the graph's generic compilation serves badly.
//!
//! The weight is `Σ_k d_k E_k`, `E_k = Π_n (a_n + p_n^(2^k))` over 64 twists and `n` coordinates, then the map's six
//! stages from the inside. Compiled from the graph, each factor costs about 47 gas: the chain value `p_n^(2^k)` has
//! two readers (the factor and the next squaring) far apart, so it goes to memory and back, and so does `a_n`. Here
//! the twists run in blocks of 13 whose products stay on the stack, the coordinates inner: a coordinate's chain value
//! and `a_n` stay on top for the block's 13 squarings and factors, and each factor multiplies its twist's product in
//! place (`DUP`, `FIELD_MUL`, `SWAP`, `POP`), about 40 gas a factor. The code also takes about half the bytes.
//!
//! **Interface.** The node's operands are `p_0 … p_(n-1)`, `a_0 … a_(n-1)`, `f_0 … f_5`, on the stack in that order;
//! the code leaves the weight. It uses the words `[0, words(n))` of memory as its own: the program's scratch, which
//! the hashing uses only within a node, is at least that big ([`scratch_words`]).

use evm_link::op::{FIELD_MUL, MLOAD, MSTORE, POP, XOR, push_usize};

const TWISTS: usize = 64;
const STAGES: usize = 6;
/// Twists a block: their products, `a_n` and the chain value and a factor must be within `DUP16`.
const BLOCK: usize = 13;

const DUP1: u8 = 0x80;
const SWAP1: u8 = 0x90;

fn dup(k: usize) -> u8 {
    assert!((1..=16).contains(&k));
    DUP1 + (k - 1) as u8
}

fn swap(k: usize) -> u8 {
    assert!((1..=16).contains(&k));
    SWAP1 + (k - 1) as u8
}

/// Memory words the kernel of `n` coordinates uses: the chain values, the `a_n`, the map, the 64 products.
pub fn scratch_words(n: usize) -> usize {
    2 * n + STAGES + TWISTS
}

struct Code(Vec<u8>);

impl Code {
    fn op(&mut self, op: u8) {
        self.0.push(op);
    }
    fn load(&mut self, word: usize) {
        self.0.extend(push_usize(32 * word));
        self.0.push(MLOAD);
    }
    fn store(&mut self, word: usize) {
        self.0.extend(push_usize(32 * word));
        self.0.push(MSTORE);
    }
}

/// The kernel's code for `n` coordinates.
pub fn ring_weight_code(n: usize) -> Vec<u8> {
    let (chain, a, map, products) = (0, n, 2 * n, 2 * n + STAGES);
    let mut code = Code(Vec::new());
    // The operands, top first: f_5 … f_0, then a, then p.
    for j in (0..STAGES).rev() {
        code.store(map + j);
    }
    for i in (0..n).rev() {
        code.store(a + i);
    }
    for i in (0..n).rev() {
        code.store(chain + i);
    }
    // The twisted products, a block of twists at a time. Stack (bottom first): E_k0 … E_(k0+size-1), a_n, P, f.
    let mut k0 = 0;
    while k0 < TWISTS {
        let size = BLOCK.min(TWISTS - k0);
        let last_block = k0 + size == TWISTS;
        for coordinate in 0..n {
            if coordinate == 0 {
                // Placeholders the first coordinate's factors replace.
                for _ in 0..size {
                    code.0.extend(push_usize(0));
                }
            }
            code.load(a + coordinate);
            code.load(chain + coordinate);
            for t in 0..size {
                if k0 + t > 0 {
                    // P <- P^2.
                    code.op(DUP1);
                    code.op(FIELD_MUL);
                }
                // f = a + P.
                code.op(DUP1);
                code.op(dup(3));
                code.op(XOR);
                // E_t at depth 4 + (size - 1 - t) below f.
                let depth = 4 + (size - 1 - t);
                if coordinate == 0 {
                    code.op(swap(depth - 1));
                    code.op(POP);
                } else {
                    code.op(dup(depth));
                    code.op(FIELD_MUL);
                    code.op(swap(depth - 1));
                    code.op(POP);
                }
            }
            if last_block {
                code.op(POP);
            } else {
                code.store(chain + coordinate);
            }
            code.op(POP);
        }
        for t in (0..size).rev() {
            code.store(products + k0 + t);
        }
        k0 += size;
    }
    // The stages from the inside: G_k <- G_k + f_j^(2^k) G_(k + 2^j), k ≡ 0 mod 2^(j+1).
    for j in 0..STAGES {
        let step = 1 << j;
        code.load(map + j);
        let mut k = 0;
        while k < TWISTS {
            if k > 0 {
                for _ in 0..2 * step {
                    code.op(DUP1);
                    code.op(FIELD_MUL);
                }
            }
            code.op(DUP1);
            code.load(products + k + step);
            code.op(FIELD_MUL);
            code.load(products + k);
            code.op(XOR);
            code.store(products + k);
            k += 2 * step;
        }
        code.op(POP);
    }
    code.load(products);
    code.0
}
