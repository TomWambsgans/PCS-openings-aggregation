// Part of this repository. The tables, their flushes and constraints, the bus fingerprints, the public input's lines
// and the Flock reduction are leanVM's at commit 42422001 (crates/verifier/src/{layout,bus,lib,flock}.rs there), read
// through `leanvm_flock_gas`'s port; the PIOP that checks them is new (SPEC.md). MIT OR Apache-2.0; see NOTICE.md.
//! The verifier of SPEC.md, generic over the scalar it computes on: from the proof's stream (two roots, Flock's
//! messages, the values at `t`) to one weighted claim per commitment.

use leanvm_flock_gas::field::E;
use leanvm_flock_gas::flock::ring_switch;
use leanvm_flock_gas::layout::{
    BLAKE2S_R1CS_LOG_SIZE, BLAKE2S_SLOTS, Form, N_TABLES, OP_BLAKE2S, OP_DEREF, OP_JUMP, OP_MUL, SEP_MEM,
    SEP_STATE, Table, gpow, tables,
};
use leanvm_flock_gas::matrices::MatrixClaim;
use leanvm_flock_gas::multilinear::{eq_kernel, log2_ceil};
use leanvm_flock_gas::scalar::{Scalar, enter};
use leanvm_flock_gas::transcript::Channel;
use leanvm_flock_gas::{LincheckTerminal, VerifierError, verify_flock};

use crate::claims::{COMMITMENTS, Column, Combined, Commitment, Relations, Term, term};
use crate::domain::{
    coordinate_functionals, coordinates_at, digits, point_e, prefix_vanishing, suffix_vanishing, vanishing_ratio,
};
use crate::heap::{HeapLayout, Leaves};

/// The sizes a contract is built for (SPEC.md §1): one shape per contract, so the proof announces none.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    pub log_memory: usize,
    pub log_bytecode: usize,
    pub table_rows: [u64; N_TABLES],
}

impl Shape {
    pub fn of(shape: &leanvm_flock_gas::Shape) -> Self {
        Self {
            log_memory: shape.log_memory as usize,
            log_bytecode: shape.bytecode_len.trailing_zeros() as usize - leanvm_flock_gas::layout::BUS_BITS,
            table_rows: shape.table_rows,
        }
    }

    pub fn heights(&self) -> [usize; N_TABLES] {
        self.table_rows.map(log2_ceil)
    }

    /// The domain of the constraint quotient: the largest table or the memory.
    pub fn constraint_vars(&self) -> usize {
        self.heights().into_iter().chain([self.log_memory]).max().expect("tables")
    }

    pub fn heap(&self) -> HeapLayout {
        HeapLayout::new(self.log_memory, self.log_bytecode, &self.heights())
    }
}

/// The columns whose values a table's rows send at `t` besides its counters: every factor of a product in its
/// flushes and constraints (SPEC.md §8).
fn factor_columns(opcode: usize) -> &'static [&'static str] {
    match opcode {
        OP_MUL => &["fp", "pc", "va_0", "va_1", "va_2"],
        OP_DEREF => &["fp", "pc", "ptr", "f_pc", "f_fp"],
        OP_JUMP => &["fp", "b", "v_cond"],
        _ => &["fp", "pc"],
    }
}

fn column_index(table: &Table, name: &str) -> usize {
    table.columns.iter().position(|&c| c == name).expect("a column of the table")
}

/// The columns of `table` whose values are sent, in the order they are sent: counters, then factors.
pub fn sent_columns(table: &Table) -> Vec<usize> {
    let mut sent: Vec<usize> = table.count_columns().collect();
    sent.extend(factor_columns(table.opcode).iter().map(|&name| column_index(table, name)));
    sent
}

/// `Σ_s weights[s] · tuple[s]` split into what the sent values give and the terms in the other columns.
fn linearise<S: Scalar>(
    tuple: &[Form],
    weights: &[S],
    sent: &[Option<S>],
) -> (S, Vec<(usize, S)>) {
    let mut known = S::zero();
    let mut terms: Vec<(usize, S)> = Vec::new();
    let mut add = |column: usize, coefficient: S| match terms.iter_mut().find(|(c, _)| *c == column) {
        Some((_, existing)) => *existing += coefficient,
        None => terms.push((column, coefficient)),
    };
    for (form, &weight) in tuple.iter().zip(weights) {
        for (monomial, &coefficient) in form.terms() {
            if coefficient == E::default() {
                continue;
            }
            let c = weight * S::constant(coefficient);
            match *monomial {
                [] => known += c,
                [i] => match sent[i] {
                    Some(value) => known += c * value,
                    None => add(i, c),
                },
                [i, j] => match (sent[i], sent[j]) {
                    (Some(a), Some(b)) => known += c * a * b,
                    (Some(a), None) => add(j, c * a),
                    (None, Some(b)) => add(i, c * b),
                    (None, None) => panic!("a product of two unsent columns in table {}", i),
                },
                _ => unreachable!("forms are of degree 2"),
            }
        }
    }
    (known, terms)
}

/// The degree of a tuple's fingerprint in the columns.
fn tuple_degree(tuple: &[Form]) -> usize {
    tuple
        .iter()
        .flat_map(|form| {
            form.terms()
                .filter(|(_, c)| **c != E::default())
                .map(|(monomial, _)| monomial.len())
        })
        .max()
        .unwrap_or(0)
        .max(1)
}

/// `Σ_k 2^(e_k)`, at most three powers of two, covering `count` coefficients: a quotient's chunks.
pub fn chunks(count: u64) -> Vec<usize> {
    let mut sizes = Vec::new();
    let mut left = count;
    while left > 0 {
        let top = 63 - left.leading_zeros() as usize;
        if sizes.len() == 2 && left != 1 << top {
            sizes.push(top + 1);
            break;
        }
        sizes.push(top);
        left -= 1 << top;
    }
    sizes
}

/// The value at `t` of a quotient in chunks `Q = Q_0 + w_(e_0) (Q_1 + w_(e_1) Q_2 ...)` scaled by `scale`: its terms.
fn quotient_terms<S: Scalar>(
    column: impl Fn(usize) -> Column,
    sizes: &[usize],
    w: &[S],
    scale: S,
) -> Vec<Term<S>> {
    let mut factor = scale;
    let mut out = Vec::new();
    for (chunk, &e) in sizes.iter().enumerate() {
        out.push(term(column(chunk), &w[..e], factor));
        factor *= w[e];
    }
    out
}

/// One table's part of the check: its sent values, the relations that bind them on `C1`, and its leaf's products.
struct TablePart<S> {
    pull: S,
    push: S,
    /// `deg(R P_pull)`, `deg P_push` over `n - 1`.
    pull_degree: usize,
    push_degree: usize,
    sent: Vec<Option<S>>,
}

#[allow(clippy::too_many_arguments)]
fn table_part<S: Scalar + PartialEq, C: Channel<S>>(
    table: &Table,
    log_height: usize,
    weights: &[S],
    beta: S,
    point: &[S],
    channel: &mut C,
    relations: &mut Relations<S>,
) -> Result<TablePart<S>, VerifierError> {
    let width = table.width();
    let mut sent: Vec<Option<S>> = vec![None; width];
    let at = |column| Column::Table {
        table: table.opcode,
        column,
    };
    for column in sent_columns(table) {
        let value = channel.next_scalar()?;
        sent[column] = Some(value);
        relations.equal(at(column), &point[..log_height], value);
    }
    let _phase = enter("bus: fingerprints and leaf products");
    let mut pull = S::one();
    let mut push = S::one();
    let (mut pull_degree, mut push_degree) = (1, 0);
    let flushes = table.flushes.pull.iter().zip(&table.flushes.push);
    for (pulled, pushed) in flushes {
        // The pull fingerprint: computed if every column is sent, else sent and bound.
        let (known, terms) = linearise(pulled, weights, &sent);
        let d_pull = if terms.is_empty() {
            beta + known
        } else {
            let value = channel.next_scalar()?;
            let terms = terms
                .into_iter()
                .map(|(c, coefficient)| term(at(c), &point[..log_height], coefficient))
                .collect();
            relations.push(terms, value + beta + known);
            value
        };
        // The push fingerprint: the pull's plus their difference, when the sent values give it; else sent and bound.
        let difference: Vec<Form> = pushed
            .iter()
            .zip(pulled)
            .map(|(a, b)| {
                let mut d = a.clone();
                d.add_scaled(b, E::new(1, 0, 0));
                d
            })
            .collect();
        let (known_difference, difference_terms) = linearise(&difference, weights, &sent);
        let d_push = if difference_terms.is_empty() {
            d_pull + known_difference
        } else {
            let (known, terms) = linearise(pushed, weights, &sent);
            let value = channel.next_scalar()?;
            let terms = terms
                .into_iter()
                .map(|(c, coefficient)| term(at(c), &point[..log_height], coefficient))
                .collect();
            relations.push(terms, value + beta + known);
            value
        };
        pull *= d_pull;
        push *= d_push;
        pull_degree += tuple_degree(pulled);
        push_degree += tuple_degree(pushed);
    }
    Ok(TablePart {
        pull,
        push,
        pull_degree,
        push_degree,
        sent,
    })
}

/// The padding instance's limbs and the rest of `padRow`: what a table's padding rows hold.
fn padding_row(table: &Table) -> Vec<E> {
    table.padding.clone()
}

/// Where `q_flock` keeps limb column `name` of BLAKE2S: its slot.
fn qflock_slot(name: &str) -> Option<usize> {
    BLAKE2S_SLOTS.iter().position(|&s| s == Some(name))
}

/// What the verifier leaves: the two roots and one weighted claim on each commitment, and Flock's claims on `A0`, `B0`.
pub struct Reduced<S> {
    pub roots: [[S; 2]; 2],
    pub claims: Vec<(Commitment, Combined<S>)>,
    pub matrices: Option<MatrixClaim<S>>,
    /// The relations combined.
    pub relations: usize,
}

/// Which BLAKE2s argument the verifier runs (SPEC.md §7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Blake2s {
    /// leanVM's Flock (zerocheck, lincheck, matrices' reduction), its ring switch as one weighted claim.
    Flock,
    /// None: the rest of the verifier alone, to measure it apart.
    Omitted,
}

/// The verifier (SPEC.md §4–§8): `public_words` are the public input's four 64-bit words, low first.
pub fn reduce<S: Scalar + PartialEq, C: Channel<S>>(
    shape: &Shape,
    public_words: [S; 4],
    channel: &mut C,
    blake2s: Blake2s,
) -> Result<Reduced<S>, VerifierError> {
    let tables = tables();
    let heights = shape.heights();
    let heap = shape.heap();
    let r_w = shape.constraint_vars();
    let h = heap.h;

    // 1. C1, then the bus's and the constraints' challenges.
    let root1 = channel.next_root()?;
    let alphas = channel.samples(4);
    let beta = channel.sample();
    let gamma = channel.sample();
    let weights = {
        let _phase = enter("bus: fingerprints and leaf products");
        eq_kernel(&alphas)
    };

    // 2. Flock, on C1's q_flock: leanVM's zerocheck, lincheck and matrices' reduction; its ring switch as one
    // weighted claim of 64 twisted terms (SPEC.md §7).
    let flock_log_n = BLAKE2S_R1CS_LOG_SIZE + heights[OP_BLAKE2S];
    let flock = match blake2s {
        Blake2s::Flock => {
            let flock = verify_flock(flock_log_n, channel, LincheckTerminal::Matrices)?;
            let (target, weight) = ring_switch(flock.point(), &flock.s, channel);
            Some((flock, target, weight))
        }
        Blake2s::Omitted => None,
    };

    // 3. C2, then the point.
    let root2 = channel.next_root()?;
    let t = channel.sample();
    let digit_count = h.max(r_w + 4) + 2;
    let w = {
        let _phase = enter("digits, vanishing polynomials, coordinates");
        digits(t, digit_count)
    };

    // 4. The values at t, with the relations they take part in.
    let mut relations = Relations::default();
    let mut parts = Vec::with_capacity(N_TABLES);
    for table in &tables {
        parts.push(table_part(
            table,
            heights[table.opcode],
            &weights,
            beta,
            &w,
            channel,
            &mut relations,
        )?);
    }
    let c = S::constant;
    let one = S::one();
    // The memory: pull (SEP_MEM, g^i, final count, limbs) of every cell, push the same with count 1.
    let lm = shape.log_memory;
    let memory_final_count = channel.next_scalar()?;
    let address = channel.next_scalar()?;
    let memory_pull = channel.next_scalar()?;
    let (memory_push, bytecode_pull, bytecode_push, bytecode_final_count);
    {
        let _phase = enter("bus: fingerprints and leaf products");
        relations.equal(Column::Memory(3), &w[..lm], memory_final_count);
        relations.equal(Column::Address, &w[..lm], address);
        let terms = (0..3)
            .map(|k| term(Column::Memory(k), &w[..lm], weights[3 + k]))
            .collect();
        relations.push(
            terms,
            memory_pull
                + beta
                + weights[0] * c(SEP_MEM)
                + weights[1] * address
                + weights[2] * memory_final_count,
        );
        memory_push = memory_pull + weights[2] * (one + memory_final_count);
    }
    // The bytecode: pull (SEP_BYTECODE, g^i, final count, instruction) of every instruction, push the same with 1.
    let lb = shape.log_bytecode;
    bytecode_final_count = channel.next_scalar()?;
    bytecode_pull = channel.next_scalar()?;
    {
        let _phase = enter("bus: fingerprints and leaf products");
        relations.equal(Column::BytecodeFinal, &w[..lb], bytecode_final_count);
        let tuple_point = [&alphas[..], &w[..lb]].concat();
        relations.equal(
            Column::BytecodeTuple,
            &tuple_point,
            bytecode_pull + beta + weights[2] * bytecode_final_count,
        );
        bytecode_push = bytecode_pull + weights[2] * (one + bytecode_final_count);
    }
    let heap_value = channel.next_scalar()?;
    let constraint_value = channel.next_scalar()?;

    // 5. The constraint quotient's identity, on C1 but for Q_W(t), which is sent.
    let mut quotient_degree: u64 = 0;
    {
        let _phase = enter("constraints: Q_W identity (padding, counters, JUMP, copies, public input)");
        let mut known = S::zero();
        let mut terms: Vec<Term<S>> = Vec::new();
        let mut power = S::one();
        let next = |power: &mut S| {
            let current = *power;
            *power *= gamma;
            current
        };
        for (table, part) in tables.iter().zip(&parts) {
            let r = heights[table.opcode];
            let n = 1u64 << r;
            let rows = shape.table_rows[table.opcode];
            let lift = vanishing_ratio(&w, r, r_w);
            let active = prefix_vanishing(&w, rows);
            let padding = suffix_vanishing(&w, rows, r);
            let at = |column| Column::Table {
                table: table.opcode,
                column,
            };
            // JUMP: b + v_cond w, v_cond (b + 1).
            if table.opcode == OP_JUMP {
                let [cond, inverse, flag] = ["v_cond", "w", "b"].map(|name| column_index(table, name));
                let (cond, flag) = (part.sent[cond].expect("sent"), part.sent[flag].expect("sent"));
                let g1 = next(&mut power) * lift;
                known += g1 * flag;
                terms.push(term(at(inverse), &w[..r], g1 * cond));
                let g2 = next(&mut power) * lift;
                known += g2 * cond * (flag + one);
                quotient_degree = quotient_degree.max(n - 2);
            }
            // padRow on the padding rows: (col + pad) Z_act.
            let pad = padding_row(table);
            let lift_active = lift * active;
            for column in 0..table.width() {
                let g = next(&mut power) * lift_active;
                match part.sent[column] {
                    Some(value) => known += g * (value + c(pad[column])),
                    None => {
                        terms.push(term(at(column), &w[..r], g));
                        known += g * c(pad[column]);
                    }
                }
            }
            quotient_degree = quotient_degree.max(rows - 1);
            // Counters nonzero on the active rows: (z Π c + 1) Z_pad.
            let mut counters = one;
            for column in table.count_columns() {
                counters *= part.sent[column].expect("a counter is sent");
            }
            let g = next(&mut power) * lift * padding;
            terms.push(term(Column::Inverse(table.opcode), &w[..r], g * counters));
            known += g;
            let counts = table.count_columns().count() as u64;
            quotient_degree = quotient_degree.max((n - 1) * (1 + counts) + (n - rows) - n);
            // BLAKE2S's limb copies equal q_flock's limbs: copy_j - ℓ_j, ℓ_j read through y(t).
            if table.opcode == OP_BLAKE2S {
                let functionals = coordinate_functionals(r);
                let y = coordinates_at(t, &functionals);
                for (column, &name) in table.columns.iter().enumerate() {
                    if let Some(slot) = qflock_slot(name) {
                        let g = next(&mut power) * lift;
                        terms.push(term(at(column), &w[..r], g));
                        terms.push(term(Column::QflockSlot(slot), &y, g));
                    }
                }
                quotient_degree = quotient_degree.max((r as u64) * (n / 2) - n);
            }
        }
        // The public input: the memory's limbs at cells 0 and 1 are the public lines (leanVM's binding).
        let [w0, w1, w2, w3] = public_words;
        let lines = [(w0, w2), (w1, w3), (S::zero(), S::zero())];
        let lift = vanishing_ratio(&w, 1, r_w);
        for (k, (low, high)) in lines.into_iter().enumerate() {
            let g = next(&mut power) * lift;
            terms.push(term(Column::Memory(k), &w[..lm], g));
            known += g * (low + t * (low + high));
        }
        quotient_degree = quotient_degree.max((1 << lm) - 3);
        relations.push(terms, constraint_value * w[r_w] + known);
    }
    let constraint_chunks = chunks(quotient_degree + 1);

    // 6. C2: the heap's tree, root and leaves, and Q_W's value.
    {
        let _phase = enter("heap: tree, root, leaf identities");
        let at_t = &w[..h];
        relations.equal(Column::Heap, at_t, heap_value);
        // The tree: w_1 (T(s(t)) + T(t) T(t+1)) + w_h Q_tree(t) = 0, Q_tree = Q_0 + w_h q_1.
        let at_s: Vec<S> = w[1..=h].to_vec();
        let mut at_next = at_t.to_vec();
        at_next[0] += one;
        relations.push(
            vec![
                term(Column::Heap, &at_s, w[1]),
                term(Column::Heap, &at_next, w[1] * heap_value),
                term(Column::TreeQuotient(0), at_t, w[h]),
                term(Column::TreeQuotient(1), &[], w[h] * w[h]),
            ],
            S::zero(),
        );
        // The root: T(1) (β + fp(SEP_STATE, 1, 1)) = β + fp(SEP_STATE, g^(2^lb - 1), 1).
        let at_one: Vec<S> = (0..h).map(|l| if l == 0 { one } else { S::zero() }).collect();
        let init = beta + weights[0] * c(SEP_STATE) + weights[1] + weights[2];
        let last = c(gpow((1 << lb) - 1));
        let fin = beta + weights[0] * c(SEP_STATE) + weights[1] * last + weights[2];
        relations.push(vec![term(Column::Heap, &at_one, init)], fin);
        // Each block's leaves: R_b(o_b + t) P_pull + w_r(t) Q_b(t) = P_push, or R_u(o_u + t) = 1.
        for (index, block) in heap.blocks.iter().enumerate() {
            let mixed: Vec<S> = (0..h)
                .map(|l| {
                    let constant = c(point_e(block.position >> l));
                    if l < block.r { w[l] + constant } else { constant }
                })
                .collect();
            let n = 1u64 << block.r;
            let (pull, push, degree) = match block.leaves {
                Leaves::Unused => {
                    relations.push(vec![term(Column::Heap, &mixed, one)], one);
                    continue;
                }
                Leaves::Memory => (memory_pull, memory_push, 2 * (n - 1) - n),
                Leaves::Bytecode => (bytecode_pull, bytecode_push, 2 * (n - 1) - n),
                Leaves::Table(t) => {
                    let part = &parts[t];
                    let d = (part.pull_degree.max(part.push_degree) as u64) * (n - 1) - n;
                    (part.pull, part.push, d)
                }
            };
            let sizes = chunks(degree + 1);
            let mut terms = vec![term(Column::Heap, &mixed, pull)];
            terms.extend(quotient_terms(
                |chunk| Column::LeafQuotient { block: index, chunk },
                &sizes,
                &w,
                w[block.r],
            ));
            relations.push(terms, push);
        }
        let terms = quotient_terms(Column::ConstraintQuotient, &constraint_chunks, &w, one);
        relations.push(terms, constraint_value);
    }

    // 7. Flock's claim on q_flock: the ring switch's 64 twisted terms.
    let mut matrices = None;
    if let Some((flock, ring_target, ring_weight)) = flock {
        relations.push(
            ring_weight
                .coefficients
                .iter()
                .enumerate()
                .map(|(k, &coefficient)| Term {
                    column: Column::Qflock,
                    point: ring_weight.point.clone(),
                    twist: k as u8,
                    coefficient,
                })
                .collect(),
            ring_target,
        );
        matrices = flock.matrices;
    }

    // 8. One claim per commitment.
    let rho = channel.sample();
    let _phase = enter("claims: combination (powers of rho, merging)");
    let claims = COMMITMENTS
        .iter()
        .filter_map(|&commitment| relations.combine(commitment, rho).map(|claim| (commitment, claim)))
        .collect();
    Ok(Reduced {
        roots: [root1, root2],
        claims,
        matrices,
        relations: relations.list.len(),
    })
}
