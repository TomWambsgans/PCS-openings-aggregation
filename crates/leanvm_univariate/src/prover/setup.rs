// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The setup commitments (SPEC.md §3), computed from what they are fixed by: `F` from the program (leanVM's stacked
//! bytecode) and the shape (the memory's and the bytecode's sizes), `A0` and `B0` from Flock's BLAKE2s R1CS alone.
//! Their roots are what a contract is generated with (review M1's F2): [`roots`].
//!
//! They are committed as every stack is (`opening::commit`: leanVM's WHIR at `c445e3d5`, rate `1/2`, 64 lanes).

use fiat_shamir::merkle::Hash;
use primitives::field::F64;

use super::columns::SetupPolys;
use super::opening::{self, Committed};
use super::stack::{Stack, setup_columns};
use crate::claims::Column;
use crate::stacks::StackLayout;
use crate::verifier::Shape;

/// `F`'s stack: the 16 tuple slots interleaved (word `slot + 16 k`, `k` a basis-`B` coefficient), the addresses.
pub fn f_stack(shape: &Shape, setup: &SetupPolys) -> Stack {
    let mut stack = Stack::new(StackLayout::new(&setup_columns(shape)));
    let n = 1usize << shape.log_bytecode;
    let tuple: Vec<F64> = (0..16 * n).map(|i| setup.slots[i % 16].b[i / 16]).collect();
    stack.put_k(Column::BytecodeTuple, &tuple);
    stack.put_k(Column::Address, &setup.address.b);
    stack
}

/// `A0` and `B0` committed: `2^28` words each.
pub fn matrices() -> [(Vec<F64>, Committed); 2] {
    let (a, b) = super::matrices::setup_matrices();
    [a, b].map(|words| {
        let committed = opening::commit(&words, 28, 1 << 28);
        (words, committed)
    })
}

/// The three setup roots a contract is built with (the contract's type: its IV binds them, SPEC.md §13, F2).
pub use crate::contract::SetupRoots;

/// `F`'s root for `shape` and the program whose setup polynomials are `setup`.
pub fn f_root(shape: &Shape, setup: &SetupPolys) -> Hash {
    let f = f_stack(shape, setup);
    opening::commit(&f.words, f.layout.vars, f.placed()).root
}

/// The setup roots of `shape`'s contract without committing `A0`, `B0` again: `F`'s, and the R1CS's (the same for
/// every shape: `SetupRoots::REFERENCE`'s, which [`roots`] recomputes).
pub fn shape_roots(shape: &Shape, setup: &SetupPolys) -> SetupRoots {
    SetupRoots {
        f: f_root(shape, setup),
        ..SetupRoots::REFERENCE
    }
}

/// The setup roots of `shape`'s contract for the program whose setup polynomials are `setup`.
pub fn roots(shape: &Shape, setup: &SetupPolys) -> SetupRoots {
    let f = f_stack(shape, setup);
    let f = opening::commit(&f.words, f.layout.vars, f.placed()).root;
    let [(_, a0), (_, b0)] = matrices();
    SetupRoots { f, a0: a0.root, b0: b0.root }
}

/// A root as 64 hex digits.
pub fn hex(root: &Hash) -> String {
    root.iter().map(|b| format!("{b:02x}")).collect()
}
