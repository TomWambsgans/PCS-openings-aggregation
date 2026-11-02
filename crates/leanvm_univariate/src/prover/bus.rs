// Part of this repository. The tuples and the framework blocks are leanVM 42422001's (crates/verifier/src/{layout,
// bus}.rs there, through `leanvm_flock_gas`). MIT OR Apache-2.0; see NOTICE.md.
//! The bus as a product heap (SPEC.md §5), prover side: every leaf's push-over-pull ratio, and the heap of their
//! products.

use leanvm_flock_gas::N_TABLES;
use leanvm_flock_gas::layout::{SEP_BYTECODE, SEP_MEM, SEP_STATE, gpow, tables};
use primitives::field::{F64, F192, g_powers};

use super::fingerprint::Fingerprint;
use super::poly::{batch_invert, from_v};
use super::trace::Trace;
use crate::heap::{HeapLayout, Leaves};

/// The bus challenges and every table's flush fingerprints, compiled.
pub struct Bus {
    /// `eq(α, s)` for the 16 tuple slots.
    pub weights: Vec<F192>,
    pub beta: F192,
    /// Per table, per flush: the pulled and the pushed tuple's fingerprint.
    pub pull: Vec<Vec<Fingerprint>>,
    pub push: Vec<Vec<Fingerprint>>,
}

impl Bus {
    pub fn new(alphas: &[F192], beta: F192) -> Self {
        let weights = primitives::multilinear::eq_table(alphas);
        let layout = tables();
        let pull = layout
            .iter()
            .map(|t| t.flushes.pull.iter().map(|tuple| Fingerprint::new(tuple, &weights, beta)).collect())
            .collect();
        let push = layout
            .iter()
            .map(|t| t.flushes.push.iter().map(|tuple| Fingerprint::new(tuple, &weights, beta)).collect())
            .collect();
        Self {
            weights,
            beta,
            pull,
            push,
        }
    }

    /// The memory cell's pulled fingerprint (`count` its final count) or pushed one (`count = 1`).
    pub fn memory(&self, address: F64, count: F64, limbs: [F64; 3]) -> F192 {
        let w = &self.weights;
        let mut acc = self.beta + w[0] * from_v(SEP_MEM) + w[1].mul_base(address) + w[2].mul_base(count);
        for (k, &limb) in limbs.iter().enumerate() {
            acc += w[3 + k].mul_base(limb);
        }
        acc
    }

    /// The instruction's fingerprint: its 16 slots (slot 2 the count).
    pub fn bytecode(&self, slots: impl Fn(usize) -> F64) -> F192 {
        (0..16).fold(self.beta, |acc, s| acc + self.weights[s].mul_base(slots(s)))
    }

    /// `β + fp(SEP_STATE, pc, 1)`.
    pub fn state(&self, pc: F192) -> F192 {
        let w = &self.weights;
        self.beta + w[0] * from_v(SEP_STATE) + w[1] * pc + w[2]
    }
}

/// Table `t`'s leaves: `Π_j D'_j / Π_j D_j` on its active rows, 1 on its padding rows. Fails (returns the row) if
/// a pulled fingerprint vanishes.
pub fn table_leaves(trace: &Trace, t: usize, bus: &Bus) -> Result<Vec<F192>, usize> {
    let columns = &trace.tables[t];
    let n = 1usize << trace.heights[t];
    let rows = trace.rows[t] as usize;
    let (pull, push) = (&bus.pull[t], &bus.push[t]);
    let mut den: Vec<F192> = parallel::map_collect(n, |i| {
        if i >= rows {
            return F192::ONE;
        }
        pull.iter().fold(F192::ONE, |acc, f| acc * f.at(|c| columns[c][i]))
    });
    if let Some(i) = den.iter().position(|d| d.is_zero()) {
        return Err(i);
    }
    batch_invert(&mut den);
    parallel::for_each_mut(&mut den, |i, slot| {
        if i < rows {
            *slot *= push.iter().fold(F192::ONE, |acc, f| acc * f.at(|c| columns[c][i]));
        }
    });
    Ok(den)
}

/// The memory's leaves: `D_init / D_fin` of every cell.
pub fn memory_leaves(trace: &Trace, bus: &Bus) -> Vec<F192> {
    let n = 1usize << trace.log_memory;
    let address = g_powers(n);
    let m = &trace.memory;
    let limbs = |i: usize| [m[0][i], m[1][i], m[2][i]];
    let mut den: Vec<F192> = parallel::map_collect(n, |i| bus.memory(address[i], m[3][i], limbs(i)));
    batch_invert(&mut den);
    parallel::for_each_mut(&mut den, |i, slot| *slot *= bus.memory(address[i], F64::ONE, limbs(i)));
    den
}

/// The bytecode's 16 tuple slots at instruction `i`, its count `count`.
pub fn bytecode_slot(trace: &Trace, pc: &[F64], i: usize, s: usize, count: F64) -> F64 {
    let n = 1usize << trace.log_bytecode;
    match s {
        0 => F64(SEP_BYTECODE.c0),
        1 => pc[i],
        2 => count,
        _ => trace.bytecode[s * n + i],
    }
}

/// The bytecode's leaves: `D_init / D_fin` of every instruction.
pub fn bytecode_leaves(trace: &Trace, bus: &Bus) -> Vec<F192> {
    let n = 1usize << trace.log_bytecode;
    let pc = g_powers(n);
    let fp = |i: usize, count: F64| bus.bytecode(|s| bytecode_slot(trace, &pc, i, s, count));
    let mut den: Vec<F192> = parallel::map_collect(n, |i| fp(i, trace.bytecode_final[i]));
    batch_invert(&mut den);
    parallel::for_each_mut(&mut den, |i, slot| *slot *= fp(i, F64::ONE));
    den
}

/// The heap: position `i` holds node `i`, the leaves at `[2^(H-1), 2^H)` in `layout`'s blocks, unused blocks 1,
/// every inner node the product of its children, position 0 zero.
pub fn heap(layout: &HeapLayout, leaves: &[(Leaves, Vec<F192>)]) -> Vec<F192> {
    let size = 1usize << layout.h;
    let mut heap = vec![F192::ONE; size];
    for block in &layout.blocks {
        if block.leaves == Leaves::Unused {
            continue;
        }
        let (_, values) = leaves.iter().find(|(l, _)| *l == block.leaves).expect("the block's leaves");
        assert_eq!(values.len(), 1 << block.r);
        let at = block.position as usize;
        heap[at..at + values.len()].copy_from_slice(values);
    }
    let mut half = size / 2;
    while half > 1 {
        let (upper, lower) = heap.split_at_mut(half);
        let parents = &mut upper[half / 2..];
        parallel::chunks_mut(parents, 1 << 12, |j, chunk| {
            let first = j << 12;
            for (k, p) in chunk.iter_mut().enumerate() {
                let child = 2 * (first + k);
                *p = lower[child] * lower[child + 1];
            }
        });
        half /= 2;
    }
    heap[0] = F192::ZERO;
    heap
}

/// The root the state boundary requires: `fp(final) / fp(initial)`.
pub fn expected_root(bus: &Bus, log_bytecode: usize) -> F192 {
    let last = from_v(gpow((1u64 << log_bytecode) - 1));
    bus.state(last) * bus.state(F192::ONE).inv()
}

/// All leaves, by block kind.
pub fn all_leaves(trace: &Trace, bus: &Bus) -> Result<Vec<(Leaves, Vec<F192>)>, String> {
    let mut out = vec![
        (Leaves::Memory, memory_leaves(trace, bus)),
        (Leaves::Bytecode, bytecode_leaves(trace, bus)),
    ];
    for t in 0..N_TABLES {
        let leaves = table_leaves(trace, t, bus).map_err(|row| format!("table {t}: a pull fingerprint vanishes at row {row}"))?;
        out.push((Leaves::Table(t), leaves));
    }
    Ok(out)
}
