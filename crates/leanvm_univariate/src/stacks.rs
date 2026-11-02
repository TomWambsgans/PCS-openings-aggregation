// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! Where every column sits in its commitment's stack (SPEC.md §3), and the weight a claim's terms put on the stack:
//! what the batching sumcheck of `PCS_OPEN`'s point-claim ABI evaluates at its end point (SPEC.md §8).
//!
//! A stack is a K-table of `2^vars` words, its MLE over `vars` variables (low first). A column of `2^v` words sits in
//! an aligned block at `offset` (largest first): its word `i` is the stack's `offset + i`. An E-valued column is three
//! such blocks, its limbs (`x = c_0 + c_1 y + c_2 y^2`). `q_flock`'s limb slot `j` is the column `Qflock` with its low
//! 8 coordinates fixed to `j`'s bits.

use std::collections::HashMap;

use leanvm_flock_gas::field::E;
use leanvm_flock_gas::scalar::Scalar;

use crate::claims::Column;

#[derive(Clone, Debug)]
pub struct StackLayout {
    pub vars: usize,
    /// Column, limb (0 for a K-column), its variables, its offset.
    pub blocks: Vec<(Column, usize, usize, u64)>,
}

impl StackLayout {
    /// `columns`: each column, its variables, whether it is E-valued.
    pub fn new(columns: &[(Column, usize, bool)]) -> Self {
        let mut pieces: Vec<(Column, usize, usize)> = Vec::new();
        for &(column, vars, e_valued) in columns {
            for limb in 0..if e_valued { 3 } else { 1 } {
                pieces.push((column, limb, vars));
            }
        }
        pieces.sort_by_key(|&(_, _, vars)| std::cmp::Reverse(vars));
        let mut offset = 0u64;
        let mut blocks = Vec::new();
        for (column, limb, vars) in pieces {
            blocks.push((column, limb, vars, offset));
            offset += 1 << vars;
        }
        let vars = (64 - (offset.max(2) - 1).leading_zeros() as usize).max(15);
        Self { vars, blocks }
    }

    pub fn words(&self) -> u64 {
        self.blocks.iter().map(|&(_, _, vars, _)| 1u64 << vars).sum()
    }

    pub fn limbs(&self, column: Column) -> Vec<(usize, usize, u64)> {
        let limbs: Vec<_> = self
            .blocks
            .iter()
            .filter(|(c, ..)| *c == column)
            .map(|&(_, limb, vars, offset)| (limb, vars, offset))
            .collect();
        assert!(!limbs.is_empty(), "{column:?} is in the layout");
        limbs
    }
}

/// `eq(point, r)` products, shared: by (point, length), and the selector factors by the offset's high bits.
pub struct EqCache<'a, S> {
    r: &'a [S],
    /// `1 + r_k`, so that each eq factor `1 + p_k + r_k` is one sum.
    one_plus_r: Vec<S>,
    rows: HashMap<(usize, usize, u8), S>,
    selectors: HashMap<(usize, u64), S>,
    /// A point's coordinates squared `twist` times, from the previous twist's.
    twisted: HashMap<(usize, u8), Vec<S>>,
}

impl<'a, S: Scalar> EqCache<'a, S> {
    pub fn new(r: &'a [S]) -> Self {
        Self {
            r,
            one_plus_r: r.iter().map(|&x| S::one() + x).collect(),
            rows: HashMap::new(),
            selectors: HashMap::new(),
            twisted: HashMap::new(),
        }
    }

    pub fn one_plus_r(&self) -> &[S] {
        &self.one_plus_r
    }

    /// `Π_{k<len} (1 + p_k^(2^twist) + r_k)` for the point numbered `id`.
    pub fn row(&mut self, id: usize, point: &[S], len: usize, twist: u8) -> S {
        if let Some(&v) = self.rows.get(&(id, len, twist)) {
            return v;
        }
        let coordinates = self.twisted_point(id, point, twist);
        let mut product = S::one();
        for k in 0..len {
            product *= self.one_plus_r[k] + coordinates[k];
        }
        self.rows.insert((id, len, twist), product);
        product
    }

    fn twisted_point(&mut self, id: usize, point: &[S], twist: u8) -> Vec<S> {
        if twist == 0 {
            return point.to_vec();
        }
        if let Some(v) = self.twisted.get(&(id, twist)) {
            return v.clone();
        }
        let previous = self.twisted_point(id, point, twist - 1);
        let v: Vec<S> = previous.iter().map(|x| x.square()).collect();
        self.twisted.insert((id, twist), v.clone());
        v
    }

    /// `Π_{k >= from} eq(bit_k(offset), r_k)` over the stack's variables.
    pub fn selector(&mut self, from: usize, offset: u64) -> S {
        let vars = self.r.len();
        if from >= vars {
            return S::one();
        }
        if let Some(&v) = self.selectors.get(&(from, offset >> from)) {
            return v;
        }
        let rest = self.selector(from + 1, offset);
        let r = self.r[from];
        let factor = if offset >> from & 1 == 1 { r } else { S::one() + r };
        let v = factor * rest;
        self.selectors.insert((from, offset >> from), v);
        v
    }
}

/// The limb basis of `E` over `K`: `(1, y, y^2)`.
pub fn limb_basis<S: Scalar>() -> [S; 3] {
    [E::new(1, 0, 0), E::new(0, 1, 0), E::new(0, 0, 1)].map(S::constant)
}
