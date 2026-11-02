// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The first commitment's polynomials and the setup's (SPEC.md §3), from a trace: every column's novel
//! coefficients (for the quotients' cosets) and its `B` coefficients (what the stack holds).

use leanvm_flock_gas::N_TABLES;
use leanvm_flock_gas::layout::{SEP_BYTECODE, tables};
use primitives::field::{F64, g_powers};
use quotient::ntt::{coefficients_from, subset_sums};

use super::poly::copy;
use super::trace::Trace;

/// A K-column of `2^r` rows as a polynomial of degree `< 2^r`: its novel and its `B` coefficients.
#[derive(Clone)]
pub struct Column {
    pub novel: Vec<F64>,
    pub b: Vec<F64>,
}

impl Column {
    pub fn from_values(values: &[F64]) -> Self {
        let mut novel = vec![F64::ZERO; values.len()];
        coefficients_from(values, &mut novel, F64::ZERO);
        let mut b = vec![F64::ZERO; values.len()];
        copy(&mut b, &novel);
        subset_sums(&mut b);
        Self { novel, b }
    }

    pub fn vars(&self) -> usize {
        self.novel.len().trailing_zeros() as usize
    }
}

/// `C1`'s polynomials: the tables' columns (BLAKE2S's limbs being the copies), the counter inverses, the memory's
/// four columns and the bytecode's final counts. `q_flock` is the trace's, as values.
pub struct C1Polys {
    pub tables: Vec<Vec<Column>>,
    pub inverses: Vec<Column>,
    /// The inverse columns' values, `1 / Π_j c_j` on every row.
    pub inverse_values: Vec<Vec<F64>>,
    pub memory: [Column; 4],
    pub bytecode_final: Column,
}

/// The setup's polynomials: the bytecode's 16 tuple slots (slot 0 `SEP_BYTECODE`, 1 the pc `g^i`, 2 zero, then
/// leanVM's stacked bytecode's slots 3..16) and the memory's addresses `g^i`.
pub struct SetupPolys {
    pub slots: Vec<Column>,
    pub address: Column,
}

pub fn c1_polys(trace: &Trace) -> C1Polys {
    let layout = tables();
    let mut tables_out = Vec::with_capacity(N_TABLES);
    let mut inverses = Vec::with_capacity(N_TABLES);
    let mut inverse_values = Vec::with_capacity(N_TABLES);
    for (t, table) in layout.iter().enumerate() {
        let columns = &trace.tables[t];
        tables_out.push(columns.iter().map(|c| Column::from_values(c)).collect());
        let n = 1usize << trace.heights[t];
        let counters: Vec<usize> = table.count_columns().collect();
        // Every row's counters are nonzero (the placed trace's padding rows hold 1: SPEC.md §13, F1).
        let mut z: Vec<F64> = parallel::map_collect(n, |i| counters.iter().fold(F64::ONE, |acc, &c| acc * columns[c][i]));
        // One inversion a chunk.
        parallel::chunks_mut(&mut z, 1 << 12, |_, chunk| {
            let mut prefix = Vec::with_capacity(chunk.len());
            let mut acc = F64::ONE;
            for &x in chunk.iter() {
                prefix.push(acc);
                if !x.is_zero() {
                    acc *= x;
                }
            }
            let mut inv = acc.inv();
            for i in (0..chunk.len()).rev() {
                let x = chunk[i];
                if x.is_zero() {
                    continue;
                }
                chunk[i] = inv * prefix[i];
                inv *= x;
            }
        });
        inverses.push(Column::from_values(&z));
        inverse_values.push(z);
    }
    C1Polys {
        tables: tables_out,
        inverses,
        inverse_values,
        memory: std::array::from_fn(|k| Column::from_values(&trace.memory[k])),
        bytecode_final: Column::from_values(&trace.bytecode_final),
    }
}

pub fn setup_polys(trace: &Trace) -> SetupPolys {
    let n = 1usize << trace.log_bytecode;
    let slots = (0..16)
        .map(|s| {
            let values: Vec<F64> = match s {
                0 => vec![F64(SEP_BYTECODE.c0); n],
                1 => g_powers(n),
                2 => vec![F64::ZERO; n],
                _ => trace.bytecode[s * n..(s + 1) * n].to_vec(),
            };
            Column::from_values(&values)
        })
        .collect();
    SetupPolys {
        slots,
        address: Column::from_values(&g_powers(1 << trace.log_memory)),
    }
}
