// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The product heap's layout (SPEC.md §5.2): which block of leaves sits where.
//!
//! The heap is one polynomial on `V_H`: position `i` holds node `i` (children `2i`, `2i + 1`, root `1`), the leaves at
//! `[2^(H-1), 2^H)`. The leaves come in aligned blocks, one per table (its rows' push-over-pull ratios), one for the
//! memory and one for the bytecode (their cells' initial-over-final ratios), largest first; the rest of the leaves are
//! covered by aligned unused blocks, each pinned to 1.

use leanvm_flock_gas::N_TABLES;

/// What a block's leaves are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Leaves {
    Memory,
    Bytecode,
    Table(usize),
    Unused,
}

#[derive(Clone, Copy, Debug)]
pub struct Block {
    pub leaves: Leaves,
    /// Its rows' variables: `2^r` leaves.
    pub r: usize,
    /// Its first leaf's heap position: `2^(H-1)` plus its offset among the leaves.
    pub position: u64,
}

#[derive(Clone, Debug)]
pub struct HeapLayout {
    /// The heap's variables: `2^H` positions, `2^(H-1)` leaves.
    pub h: usize,
    pub blocks: Vec<Block>,
}

impl HeapLayout {
    pub fn new(log_memory: usize, log_bytecode: usize, table_log_heights: &[usize; N_TABLES]) -> Self {
        let mut used: Vec<(Leaves, usize)> = vec![(Leaves::Memory, log_memory), (Leaves::Bytecode, log_bytecode)];
        used.extend((0..N_TABLES).map(|t| (Leaves::Table(t), table_log_heights[t])));
        // Largest first, so that every block is aligned.
        used.sort_by_key(|&(leaves, r)| (std::cmp::Reverse(r), leaves_order(leaves)));
        let total: u64 = used.iter().map(|&(_, r)| 1u64 << r).sum();
        let d = 64 - (total - 1).leading_zeros() as usize;
        let base = 1u64 << d;
        let mut blocks = Vec::new();
        let mut offset = 0u64;
        for (leaves, r) in used {
            blocks.push(Block {
                leaves,
                r,
                position: base + offset,
            });
            offset += 1 << r;
        }
        while offset < base {
            let mut r = offset.trailing_zeros() as usize;
            while offset + (1 << r) > base {
                r -= 1;
            }
            blocks.push(Block {
                leaves: Leaves::Unused,
                r,
                position: base + offset,
            });
            offset += 1 << r;
        }
        Self { h: d + 1, blocks }
    }

    pub fn leaves(&self) -> u64 {
        1 << (self.h - 1)
    }
}

fn leaves_order(leaves: Leaves) -> usize {
    match leaves {
        Leaves::Memory => 0,
        Leaves::Bytecode => 1,
        Leaves::Table(t) => 2 + t,
        Leaves::Unused => 99,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// At the reference workload (1,000 signatures): `2^22` leaves, the blocks of SPEC.md §5.2.
    #[test]
    fn reference_layout() {
        let heap = HeapLayout::new(21, 19, &[18, 18, 18, 18, 17, 18]);
        assert_eq!(heap.h, 23);
        let base = 1 << 22;
        assert_eq!(heap.blocks[0].leaves, Leaves::Memory);
        assert_eq!(heap.blocks[0].position, base);
        assert_eq!(heap.blocks[1].position, base + (1 << 21));
        let unused: Vec<_> = heap.blocks.iter().filter(|b| b.leaves == Leaves::Unused).collect();
        assert_eq!(unused.len(), 1);
        assert_eq!(unused[0].r, 17);
        for block in &heap.blocks {
            assert_eq!(block.position % (1 << block.r), 0, "aligned");
        }
    }
}
