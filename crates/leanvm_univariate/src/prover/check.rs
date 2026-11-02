// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! SPEC.md's identities on the domain itself, on a real trace, with no randomness but the bus's challenges: what
//! the quotients exist for. Each check names what it tests and how many rows break it.

use leanvm_flock_gas::layout::{BLAKE2S_SLOTS, OP_BLAKE2S, OP_JUMP, tables};
use primitives::field::{F64, F192};

use super::bus::{Bus, all_leaves, expected_root, heap};
use super::trace::Trace;
use crate::heap::Leaves;

/// One identity: its name and the rows (or cells) where it fails.
#[derive(Debug)]
pub struct Check {
    pub name: String,
    pub failures: usize,
    pub tested: usize,
}

fn check(name: impl Into<String>, tested: usize, failures: usize) -> Check {
    Check {
        name: name.into(),
        failures,
        tested,
    }
}

/// Every identity of SPEC.md on `trace`'s domain, with the bus at `(alphas, beta)`.
pub fn on_domain(trace: &Trace, alphas: &[F192], beta: F192) -> Vec<Check> {
    let mut out = Vec::new();
    let layout = tables();
    // JUMP: b + v_cond w = 0 and v_cond (b + 1) = 0, on every row.
    {
        let t = &layout[OP_JUMP];
        let col = |name: &str| &trace.tables[OP_JUMP][t.columns.iter().position(|&c| c == name).unwrap()];
        let (cond, w, b) = (col("v_cond"), col("w"), col("b"));
        let n = cond.len();
        let bad = (0..n)
            .filter(|&i| !(b[i] + cond[i] * w[i]).is_zero() || !(cond[i] * (b[i] + F64::ONE)).is_zero())
            .count();
        out.push(check("JUMP: b + v_cond w = 0, v_cond (b + 1) = 0 (all rows)", n, bad));
    }
    // Counters: every count column nonzero on active rows.
    for t in &layout {
        let rows = trace.rows[t.opcode] as usize;
        let bad = (0..rows)
            .filter(|&i| t.count_columns().any(|c| trace.tables[t.opcode][c][i].is_zero()))
            .count();
        out.push(check(format!("{}: counters nonzero (active rows)", leanvm_flock_gas::TABLE_NAMES[t.opcode]), rows, bad));
    }
    // Padding rows: what they hold against padRow (not a constraint here: their leaves are 1).
    for t in &layout {
        let rows = trace.rows[t.opcode] as usize;
        let n = 1usize << trace.heights[t.opcode];
        let bad = (rows..n)
            .filter(|&i| (0..t.width()).any(|c| trace.tables[t.opcode][c][i].0 != t.padding[c].c0))
            .count();
        out.push(check(
            format!("{}: padding rows hold padRow (informative)", leanvm_flock_gas::TABLE_NAMES[t.opcode]),
            n - rows,
            bad,
        ));
    }
    // The public input: memory cells 0 and 1 are the public cells.
    {
        let m = &trace.memory;
        let bad = (0..2)
            .filter(|&cell| (0..3).any(|k| m[k][cell].0 != trace.public[cell][k]))
            .count();
        out.push(check("public input: memory cells 0 and 1", 2, bad));
    }
    // The limb copies: BLAKE2S's value limbs are q_flock's slots, on every row (padding rows included).
    {
        let t = &layout[OP_BLAKE2S];
        let n = 1usize << trace.heights[OP_BLAKE2S];
        let mut bad = 0;
        for (c, &name) in t.columns.iter().enumerate() {
            if let Some(slot) = BLAKE2S_SLOTS.iter().position(|&s| s == Some(name)) {
                bad += (0..n)
                    .filter(|&i| trace.tables[OP_BLAKE2S][c][i] != trace.qflock[(i << 8) | slot])
                    .count();
            }
        }
        out.push(check("BLAKE2S: copy_j = q_flock's slot j (all rows, 18 limbs)", 18 * n, bad));
    }
    // The setup's tuple slots 0..2 are the framework's (SEP_BYTECODE, the pc, the count): leanVM's stacked bytecode
    // leaves them zero.
    {
        let n = 1usize << trace.log_bytecode;
        let bad = (0..3 * n).filter(|&i| !trace.bytecode[i].is_zero()).count();
        out.push(check("bytecode: leanVM's stacked slots 0, 1, 2 are zero", 3 * n, bad));
    }
    // The bus: no pull fingerprint vanishes, and the heap's root is the state boundary's ratio.
    let bus = Bus::new(alphas, beta);
    match all_leaves(trace, &bus) {
        Err(e) => out.push(check(format!("bus: pull fingerprints nonzero ({e})"), 1, 1)),
        Ok(leaves) => {
            out.push(check("bus: pull fingerprints nonzero", 1, 0));
            let layout = trace.shape().heap();
            let values = heap(&layout, &leaves);
            let root = expected_root(&bus, trace.log_bytecode);
            out.push(check("bus: Π push = Π pull (root = fp(final)/fp(initial))", 1, (values[1] != root) as usize));
            // The tree identity on V_H \ V_1 by construction; the unused blocks are 1.
            let unused: usize = layout
                .blocks
                .iter()
                .filter(|b| b.leaves == Leaves::Unused)
                .map(|b| (0..1usize << b.r).filter(|&i| values[b.position as usize + i] != F192::ONE).count())
                .sum();
            out.push(check("heap: unused leaves are 1", 1, unused));
            let size = values.len();
            let tree_bad = (2..size / 2).filter(|&p| values[p] != values[2 * p] * values[2 * p + 1]).count();
            out.push(check("heap: T(s(x)) = T(x) T(x + 1) on V_H \\ V_1", size - 2, tree_bad));
        }
    }
    // Counter inverses: z_T Π c_j = 1 on active rows, by construction of z_T (columns.rs); here the counters only.
    out
}
