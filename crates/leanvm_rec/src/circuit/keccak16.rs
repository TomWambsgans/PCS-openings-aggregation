// Part of this repository. The round constants, rotations and lane permutation are Keccak's (FIPS 202), as in this
// repository's crates/primitives/src/hash.rs (vendored from leanVM) and used by crates/quotient/src/circuit.rs, whose
// Keccak-f wiring (lane `x + 5y`, bit `z` at index `z`, lane `i` rotated by `RHO[i]` to `PI[i]`) this follows. MIT OR
// Apache-2.0; see NOTICE.md.
//! D16v's Keccak-f\[1600\] (SPEC-REC.md §2.4.1): rows of 16 positions, one χ row per `(round, plane y', z')`.
//!
//! A round `j` takes `A_(j−1)` and `D_j`. Its χ row for plane `y'` and slice `z'` pulls, for each `x'`, the source
//! lane `l` with `π(l) = (x', y')` at bit `z = z' − ρ_l`: `A_(j−1)[l][z]` at cell `x'` and `D_j[x(l)][z]` at cell
//! `5 + x'`, so `b_(x') = c_(x') + c_(5+x')`, and `χ_(x') = b_(x') + b_(x'+2) + b_(x'+1)·b_(x'+2)`.
//!
//! | region | rows a round | roles |
//! |---|---:|---|
//! | `k0` (plane 0) | 64 | 0–4: `A_j[x', 0] = χ_(x')` (+`RC` by `κ` at role 0); 5–9: `P_0[x'] = χ_(x')` (+`RC` at 5), the `D_j` cells ending here; 10–15: three D units |
//! | `k1` (planes 1–4) | 256 | 0–4: `A_j[x', y'] = χ_(x')`; 5–9: forwards of `D_j`; 10–14: `P_(y') = P_(y'−1) + χ_(x')`, ending `P_(y'−1)`; 15: a spare slot (a constant, or dead) |
//! | `kd` | 344 a permutation | eight D units |
//! | `kprep` | 160 a permutation | two `C_0` units (5 forwards of the input's column, a slot pushing their sum, its pull a free end); two D units |
//!
//! A **D unit** (2 roles): a slot pulling `C[x−1][z]` (its end) and pushing `D[x][z] = C[x−1][z] + C[x+1][z−1]`, and a
//! forward of `C[x+1][z−1]`. `C_(j+1) = P_4` of round `j`, `C_0` is `kprep`'s. D units come from a pool kept across
//! permutations: the `k0` rows' (all made first), `kprep`'s, then new `kd` rows. Round 23's `P_4` is junk (the
//! framework ends it at free ends). A constant input bit (the first block's padding and capacity) is a fresh constant,
//! in a `k1` row's spare role 15: the round-0 χ slot ends it, a `kprep` forward reads it.
//!
//! The chains balance: `A_(j−1)` ends at its χ row (fan-out 1, the partial sums recompute χ where it is produced);
//! `D_j[x][z]` feeds the 5 lanes `(x, y)`, whose planes `2x + 3y` are distinct, so it is forwarded through four `k1`
//! rows and ends in one `k0` row; `C[x][z]` ends in one D unit and is forwarded through another; the input ends at
//! round 0's χ and is forwarded through `kprep`. Per permutation (steady state) `1,536 + 6,144 + 344 + 160 = 8,184`
//! rows, 130,944 positions.

use std::collections::VecDeque;

use leanvm_flock_gas::field::K;

use super::keccak::{Bit, Constants, PI, Permutation, RC, RHO, spare};
use super::layout::{Builder, PolyBuilder, Value, forwards};
use super::spec::Formula;

/// D16v's Keccak-f.
pub struct D16 {
    k0: u16,
    k1: u16,
    kd: u16,
    kprep: u16,
    /// Free D units: `(row, slot role)`, the forward at the next role.
    pool: VecDeque<(u32, usize)>,
}

/// `χ_(x')` on a χ row's cells: `b_i = c_i + c_(5+i)`.
fn chi(x: usize) -> PolyBuilder {
    let (x1, x2) = ((x + 1) % 5, (x + 2) % 5);
    let mut p = PolyBuilder::new()
        .linear(x, 1)
        .linear(5 + x, 1)
        .linear(x2, 1)
        .linear(5 + x2, 1);
    for a in [x1, 5 + x1] {
        for c in [x2, 5 + x2] {
            p.add_quadratic(a, c, 1);
        }
    }
    p
}

/// A D unit's slot at `s`: `c_s + c_(s+1)`.
fn d_unit(s: usize) -> Formula {
    Formula::Expr(PolyBuilder::new().linear(s, 1).linear(s + 1, 1).build())
}

impl D16 {
    pub fn new(b: &mut Builder) -> Self {
        assert_eq!(b.width(), 16, "D16v's rows are 16 positions");
        let mut k0 = forwards(16);
        for x in 0..5 {
            k0[x] = Formula::Expr(chi(x).build());
            k0[5 + x] = Formula::Expr(chi(x).build());
        }
        for u in 0..3 {
            k0[10 + 2 * u] = d_unit(10 + 2 * u);
        }
        let mut k1 = forwards(16);
        for x in 0..5 {
            k1[x] = Formula::Expr(chi(x).build());
            let mut p = chi(x);
            p.add_linear(10 + x, 1);
            k1[10 + x] = Formula::Expr(p.build());
        }
        k1[15] = spare();
        let mut kd = forwards(16);
        for u in 0..8 {
            kd[2 * u] = d_unit(2 * u);
        }
        let mut kprep = forwards(16);
        for u in 0..2 {
            let base = 6 * u;
            let mut p = PolyBuilder::new();
            for i in 0..5 {
                p.add_linear(base + i, 1);
            }
            kprep[base + 5] = Formula::Expr(p.build());
        }
        kprep[12] = d_unit(12);
        kprep[14] = d_unit(14);
        Self {
            k0: b.region("keccak16/k0", k0),
            k1: b.region("keccak16/k1", k1),
            kd: b.region("keccak16/kd", kd),
            kprep: b.region("keccak16/kprep", kprep),
            pool: VecDeque::new(),
        }
    }

    /// A round's rows: 64 `k0` (their D units to the pool), 4 × 64 `k1` (their spare role to the constants).
    fn round_rows(&mut self, b: &mut Builder, constants: &mut Constants) -> (Vec<u32>, Vec<Vec<u32>>) {
        let k0: Vec<u32> = (0..64).map(|_| b.row(self.k0)).collect();
        let k1: Vec<Vec<u32>> = (1..5).map(|_| (0..64).map(|_| b.row(self.k1)).collect()).collect();
        for &row in &k0 {
            self.pool.extend((0..3).map(|u| (row, 10 + 2 * u)));
        }
        for &row in k1.iter().flatten() {
            constants.offer(row, 15);
        }
        (k0, k1)
    }

    /// `D[x][z] = C[x−1][z] + C[x+1][z−1]` for every `(x, z)`, in units from the pool.
    fn d(&mut self, b: &mut Builder, c: &[[Value; 64]; 5]) -> [[Value; 64]; 5] {
        let mut d = [[0; 64]; 5];
        for x in 0..5 {
            for z in 0..64 {
                let (row, s) = match self.pool.pop_front() {
                    Some(unit) => unit,
                    None => {
                        let row = b.row(self.kd);
                        self.pool.extend((1..8).map(|u| (row, 2 * u)));
                        (row, 0)
                    }
                };
                b.place(row, s, c[(x + 4) % 5][z]);
                b.place(row, s + 1, c[(x + 1) % 5][(z + 63) % 64]);
                d[x][z] = b.produce(row, s);
            }
        }
        d
    }
}

impl Permutation for D16 {
    fn permute(&mut self, b: &mut Builder, constants: &mut Constants, input: &[Bit]) -> Vec<Value> {
        assert_eq!(input.len(), 1600);
        // Every round's rows first: their k1 rows' spare role 15 holds the input's constants, their k0 rows' D units
        // are in the pool from the start.
        let mut rounds: Vec<(Vec<u32>, Vec<Vec<u32>>)> = (0..24).map(|_| self.round_rows(b, constants)).collect();
        rounds.reverse();
        let mut a: Vec<Value> = input
            .iter()
            .map(|&x| match x {
                Bit::V(v) => v,
                Bit::Zero => constants.fresh(b, K(0)),
                Bit::One => constants.fresh(b, K(1)),
            })
            .collect();

        // C_0: two column sums a kprep row, and its two D units into the pool.
        let mut c = [[0; 64]; 5];
        let mut row = 0;
        for u in 0..320 {
            let (x, z) = (u % 5, u / 5);
            if u % 2 == 0 {
                row = b.row(self.kprep);
                self.pool.extend([(row, 12), (row, 14)]);
            }
            let base = 6 * (u % 2);
            for y in 0..5 {
                b.place(row, base + y, a[64 * (x + 5 * y) + z]);
            }
            c[x][z] = b.produce(row, base + 5);
        }
        let mut d = self.d(b, &c);

        // Where lane `l`'s bit `z` is read: plane `π(l) / 5`, cell `π(l) mod 5`, slice `z + ρ_l`.
        for (j, &rc) in RC.iter().enumerate() {
            let (k0, k1) = rounds.pop().expect("a round's rows");
            let row_of = |plane: usize, z: usize| if plane == 0 { k0[z] } else { k1[plane - 1][z] };
            for l in 0..25 {
                let (xp, yp) = (PI[l] % 5, PI[l] / 5);
                for z in 0..64 {
                    let row = row_of(yp, (z + RHO[l]) % 64);
                    b.place(row, xp, a[64 * l + z]);
                    b.place(row, 5 + xp, d[l % 5][z]);
                }
            }
            let mut out = vec![0; 1600];
            let mut p = [[0; 64]; 5];
            for (z, &row) in k0.iter().enumerate() {
                if rc >> z & 1 == 1 {
                    b.set_kappa(row, 0, K(1));
                    b.set_kappa(row, 5, K(1));
                }
                for x in 0..5 {
                    out[64 * x + z] = b.produce(row, x);
                    p[x][z] = b.produce(row, 5 + x);
                }
            }
            for (yp, rows) in k1.iter().enumerate().map(|(i, r)| (i + 1, r)) {
                for (z, &row) in rows.iter().enumerate() {
                    for x in 0..5 {
                        b.place(row, 10 + x, p[x][z]);
                    }
                    for x in 0..5 {
                        out[64 * (x + 5 * yp) + z] = b.produce(row, x);
                        p[x][z] = b.produce(row, 10 + x);
                    }
                }
            }
            a = out;
            if j < 23 {
                c = p;
                d = self.d(b, &c);
            }
        }
        a
    }
}
