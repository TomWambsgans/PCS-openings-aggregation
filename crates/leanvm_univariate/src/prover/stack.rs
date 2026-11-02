// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The three stacks, filled: every column's words at the block `crate::stacks::StackLayout` gives it (the
//! verifier's `layouts`, rebuilt here from the same column lists), the rest zero. Nothing the verifier checks
//! depends on the words outside the blocks: every weight is zero there, and every claim is on the whole stack's
//! multilinear, whatever the stack holds there.

use leanvm_flock_gas::layout::{OP_BLAKE2S, tables};
use primitives::field::{F64, F192};

use crate::claims::Column;
use crate::stacks::StackLayout;
use crate::verifier::Shape;

/// `C1`'s columns as the verifier lists them (`verifier::layouts`).
pub fn c1_columns(shape: &Shape) -> Vec<(Column, usize, bool)> {
    let heights = shape.heights();
    let mut c1: Vec<(Column, usize, bool)> = vec![(Column::Qflock, heights[OP_BLAKE2S] + 8, false)];
    for table in tables() {
        let h = heights[table.opcode];
        c1.extend((0..table.width()).map(|column| {
            (
                Column::Table {
                    table: table.opcode,
                    column,
                },
                h,
                false,
            )
        }));
        c1.push((Column::Inverse(table.opcode), h, false));
    }
    c1.extend((0..4).map(|k| (Column::Memory(k), shape.log_memory, false)));
    c1.push((Column::BytecodeFinal, shape.log_bytecode, false));
    c1
}

/// The setup's columns.
pub fn setup_columns(shape: &Shape) -> Vec<(Column, usize, bool)> {
    vec![
        (Column::BytecodeTuple, shape.log_bytecode + 4, false),
        (Column::Address, shape.log_memory, false),
    ]
}

/// `C2`'s columns as the verifier lists them: the heap, the tree quotient's two chunks, the constraint quotient's
/// chunks, then each heap block's leaf quotient chunks.
pub fn c2_columns(h: usize, constraint_chunks: &[usize], leaf_chunks: &[(usize, Vec<usize>)]) -> Vec<(Column, usize, bool)> {
    let mut c2 = vec![
        (Column::Heap, h, true),
        (Column::TreeQuotient(0), h, true),
        (Column::TreeQuotient(1), 0, true),
    ];
    c2.extend(constraint_chunks.iter().enumerate().map(|(c, &e)| (Column::ConstraintQuotient(c), e, true)));
    for (block, sizes) in leaf_chunks {
        c2.extend(
            sizes
                .iter()
                .enumerate()
                .map(|(chunk, &e)| (Column::LeafQuotient { block: *block, chunk }, e, true)),
        );
    }
    c2
}

/// What a stack commits: whole lanes of `2^(vars - 6)` words, the stack's words past them zero.
pub struct Stack {
    pub layout: StackLayout,
    pub words: Vec<F64>,
}

impl Stack {
    /// A zero stack of `layout`, as many whole lanes as its blocks need.
    pub fn new(layout: StackLayout) -> Self {
        let lane = 1usize << (layout.vars - super::opening::LANE_FOLD);
        let used = layout.words() as usize;
        let len = used.div_ceil(lane).max(1) * lane;
        Self {
            layout,
            words: vec![F64::ZERO; len],
        }
    }

    /// Words placed (the blocks), as WHIR's verifier is told.
    pub fn placed(&self) -> u64 {
        self.layout.words()
    }

    /// Fill the words past every block (inside the committed lanes) with pseudo-random words: nothing the verifier
    /// checks may depend on them (`PROVER.md`, "the stacks' unused words").
    pub fn fill_unused(&mut self, seed: u64) {
        let placed = self.placed() as usize;
        let mut state = seed | 1;
        for word in &mut self.words[placed..] {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *word = F64(state);
        }
    }

    /// Write a K-column's words into its block.
    pub fn put_k(&mut self, column: Column, data: &[F64]) {
        let limbs = self.layout.limbs(column);
        assert_eq!(limbs.len(), 1, "{column:?} is a K-column");
        let (_, vars, offset) = limbs[0];
        assert_eq!(data.len(), 1 << vars, "{column:?}'s size");
        super::poly::copy(&mut self.words[offset as usize..offset as usize + data.len()], data);
    }

    /// An E-column's limb `limb`, to be written in place.
    pub fn limb_mut(&mut self, column: Column, limb: usize) -> &mut [F64] {
        let (_, vars, offset) = self.layout.limbs(column)[limb];
        &mut self.words[offset as usize..offset as usize + (1 << vars)]
    }

    /// An E-column's three limbs as placed.
    pub fn limbs(&self, column: Column) -> [&[F64]; 3] {
        let limbs = self.layout.limbs(column);
        assert_eq!(limbs.len(), 3, "{column:?} is an E-column");
        let mut out: [&[F64]; 3] = [&[]; 3];
        for (limb, vars, offset) in limbs {
            out[limb] = &self.words[offset as usize..offset as usize + (1 << vars)];
        }
        out
    }

    /// Write an E-column's three limbs.
    pub fn put_e(&mut self, column: Column, data: &[F192]) {
        let limbs = self.layout.limbs(column);
        assert_eq!(limbs.len(), 3, "{column:?} is an E-column");
        for (limb, vars, offset) in limbs {
            assert_eq!(data.len(), 1 << vars, "{column:?}'s size");
            let block = &mut self.words[offset as usize..offset as usize + data.len()];
            parallel::fill(block, |i| {
                let x = data[i];
                F64([x.c0, x.c1, x.c2][limb])
            });
        }
    }
}
