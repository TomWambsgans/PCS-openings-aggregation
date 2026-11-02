// Part of this repository. The tables, their flushes and constraints, the bus fingerprints, the public input's lines
// and the Flock reduction are leanVM's at commit 42422001 (crates/verifier/src/{layout,bus,lib,flock}.rs there), read
// through `leanvm_flock_gas`'s port; the PIOP that checks them is new (SPEC.md). MIT OR Apache-2.0; see NOTICE.md.
//! The verifier of SPEC.md, generic over the scalar it computes on: from the proof's stream (two roots, Flock's
//! messages, the values at `t`) to one weighted claim per commitment.

use leanvm_flock_gas::field::E;
use leanvm_flock_gas::flock::ring_switch_weight;
use leanvm_flock_gas::ring_tower;
use leanvm_flock_gas::flock_min::{self, End, Slices, Variant};
use leanvm_flock_gas::layout::{
    BLAKE2S_R1CS_LOG_SIZE, BLAKE2S_SLOTS, Form, N_TABLES, OP_BLAKE2S, OP_DEREF, OP_JUMP, OP_MUL, SEP_MEM,
    SEP_STATE, Table, gpow, tables,
};
use leanvm_flock_gas::matrices::MatrixClaim;
use leanvm_flock_gas::multilinear::{eq_kernel, log2_ceil};
use leanvm_flock_gas::scalar::{Scalar, enter};
use leanvm_flock_gas::transcript::{Channel, sumcheck};
use leanvm_flock_gas::VerifierError;

use crate::claims::{COMMITMENTS, Column, Combined, Commitment, Relations, Term, term};
use crate::stacks::{EqCache, StackLayout, limb_basis};
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

/// Where `q_flock` keeps limb column `name` of BLAKE2S: its slot.
fn qflock_slot(name: &str) -> Option<usize> {
    BLAKE2S_SLOTS.iter().position(|&s| s == Some(name))
}

/// What the verifier leaves: the two roots and one weighted claim on each commitment, and Flock's claims on `A0`, `B0`.
pub struct Reduced<S> {
    pub roots: [[S; 2]; 2],
    pub openings: Vec<(Commitment, Opening<S>)>,
    pub matrices: Option<MatrixClaim<S>>,
    /// The relations combined, and each commitment's stack variables.
    pub relations: usize,
    pub stack_vars: Vec<(Commitment, usize)>,
}

/// What a commitment's one `PCS_OPEN` call carries.
#[derive(Clone, Debug)]
pub enum Opening<S> {
    /// One weighted claim (extension W, SPEC.md §8).
    Weighted(Combined<S>),
    /// One point claim, `PCS_OPEN`'s ABI (after the batching sumcheck), and on `C1` with Flock (a) the bit-slice
    /// combination claim (extension B).
    Point {
        point: Vec<S>,
        value: S,
        bit_slice: Option<Combined<S>>,
    },
}

/// How the relations reach `PCS_OPEN` (SPEC.md §8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Claims {
    /// `crates/evm/src/machine.rs`'s ABI: point claims. One batching sumcheck over the stacks (the longest, the
    /// others zero-extended) turns every commitment's relations into one point claim at its end point.
    Point,
    /// Extension W: one weighted claim per commitment, its terms evaluated by the precompile.
    Weighted,
}

/// Flock's variants measured end to end (SPEC-FLOCK.md): (a′) the main line, `PCS_OPEN`'s claims `E`-linear; (a) a
/// bit-slice claim type (a precompile extension); leanVM's own skip with (a′)'s weighted claim.
pub const FLOCK_MAIN: Variant = Variant {
    skip: 3,
    slices: Slices::Tower,
};

/// The twist field of the term that stands for the whole ring-switch weight `Φ(eq(p, ·))` on the main line: the
/// batch's weight evaluates it at its point by [`ring_tower::weight_at`] (64 twisted eq products and the map's stages)
/// rather than as 64 terms with explicit coefficients (SPEC.md §13).
pub const RING_TWIST: u8 = u8::MAX;
pub const FLOCK_BIT_SLICE: Variant = Variant {
    skip: 4,
    slices: Slices::Claim,
};
pub const FLOCK_LEANVM_SKIP: Variant = Variant {
    skip: 6,
    slices: Slices::Weighted,
};

/// Which BLAKE2s argument the verifier runs (SPEC.md §7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Blake2s {
    /// Flock (`leanvm_flock_gas::flock_min`, SPEC-FLOCK.md) as `Variant` has it: its claims on `q_flock` joined
    /// into `C1`'s claim (the ring switch's 64 twisted terms, or one bit-slice combination), and on `A0`, `B0`.
    Flock(Variant),
    /// None: the rest of the verifier alone, to measure it apart.
    Omitted,
}

/// The verifier (SPEC.md §4–§8): `public_words` are the public input's four 64-bit words, low first.
pub fn reduce<S: Scalar + PartialEq, C: Channel<S>>(
    shape: &Shape,
    public_words: [S; 4],
    channel: &mut C,
    blake2s: Blake2s,
    mode: Claims,
) -> Result<Reduced<S>, VerifierError> {
    let tables = tables();
    let mut c2_columns: Vec<(Column, usize, bool)> = vec![
        (Column::Heap, shape.heap().h, true),
        (Column::TreeQuotient(0), shape.heap().h, true),
        (Column::TreeQuotient(1), 0, true),
    ];
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
        Blake2s::Flock(variant) => Some(flock_min::verify(flock_log_n, variant, channel)?),
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
        let _phase = enter("constraints: Q_W identity (counters, JUMP, limb copies, public input)");
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
    c2_columns.extend(
        constraint_chunks
            .iter()
            .enumerate()
            .map(|(c, &e)| (Column::ConstraintQuotient(c), e, true)),
    );

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
                    // Padding rows' leaves are 1, whatever they hold: (R P_pull + P_push) Z_pad + (R + 1) Z_act.
                    let part = &parts[t];
                    let rows = shape.table_rows[t];
                    let active = prefix_vanishing(&w, rows);
                    let padding = suffix_vanishing(&w, rows, block.r);
                    let d = (part.pull_degree.max(part.push_degree) as u64) * (n - 1) + (n - rows) - n;
                    (part.pull * padding + active, part.push * padding + active, d)
                }
            };
            let sizes = chunks(degree + 1);
            c2_columns.extend(
                sizes
                    .iter()
                    .enumerate()
                    .map(|(chunk, &e)| (Column::LeafQuotient { block: index, chunk }, e, true)),
            );
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

    // 7. Flock's claim on q_flock: the ring switch's 64 twisted terms (E-linear), or one bit-slice combination.
    let mut matrices = None;
    let mut bit_slice = Relations::default();
    let mut ring_map: Option<Vec<S>> = None;
    let tower = matches!(blake2s, Blake2s::Flock(Variant { slices: Slices::Tower, .. }));
    if let Some(flock) = flock {
        match flock.end {
            End::Ring { map, target, .. } if tower && mode == Claims::Point => {
                // One term for the whole weight, evaluated at the batch's point (SPEC.md §13).
                relations.push(
                    vec![Term {
                        column: Column::Qflock,
                        point: flock.point.clone(),
                        twist: RING_TWIST,
                        coefficient: S::one(),
                    }],
                    target,
                );
                ring_map = Some(map);
            }
            End::Ring { map, target, .. } if tower => {
                let coefficients = {
                    let _phase = enter("ring switch: map, coefficients, target");
                    ring_tower::coefficients(&map)
                };
                relations.push(
                    coefficients
                        .iter()
                        .enumerate()
                        .map(|(k, &coefficient)| Term {
                            column: Column::Qflock,
                            point: flock.point.clone(),
                            twist: k as u8,
                            coefficient,
                        })
                        .collect(),
                    target,
                );
            }
            End::Ring { map, target, .. } => {
                let weight = {
                    let _phase = enter("ring switch: map, coefficients, target");
                    ring_switch_weight(flock.point.clone(), &map)
                };
                relations.push(
                    weight
                        .coefficients
                        .iter()
                        .enumerate()
                        .map(|(k, &coefficient)| Term {
                            column: Column::Qflock,
                            point: weight.point.clone(),
                            twist: k as u8,
                            coefficient,
                        })
                        .collect(),
                    target,
                );
            }
            End::Combination { weights, value } => bit_slice.push(
                weights
                    .iter()
                    .enumerate()
                    .map(|(i, &coefficient)| Term {
                        column: Column::QflockBits,
                        point: flock.point.clone(),
                        twist: i as u8,
                        coefficient,
                    })
                    .collect(),
                value,
            ),
        }
        matrices = Some(flock.matrices);
    }

    // 8. One claim per commitment.
    let rho = channel.sample();
    let combined: Vec<(Commitment, Combined<S>)> = {
        let _phase = enter("claims: combination (powers of rho, merging)");
        COMMITMENTS
            .iter()
            .filter_map(|&commitment| relations.combine(commitment, rho).map(|claim| (commitment, claim)))
            .collect()
    };
    let bit_slice = bit_slice.combine(Commitment::C1, S::one());
    let layouts = layouts(shape, &c2_columns);
    let stack_vars = layouts.iter().map(|(c, l)| (*c, l.vars)).collect();
    let openings = match mode {
        Claims::Weighted => {
            let mut openings: Vec<(Commitment, Opening<S>)> =
                combined.into_iter().map(|(c, claim)| (c, Opening::Weighted(claim))).collect();
            if let Some(claim) = bit_slice {
                // Without the point ABI, the bit-slice terms join C1's weighted claim.
                let (_, Opening::Weighted(c1)) = &mut openings[0] else { unreachable!() };
                // A fresh power of rho, past the powers C1's relations took.
                let fresh = rho.pow(c1.relations as u64);
                let base = c1.points.len();
                c1.points.extend(claim.points);
                c1.terms
                    .extend(claim.terms.into_iter().map(|(column, p, twist, k)| (column, p + base, twist, fresh * k)));
                c1.value += fresh * claim.value;
            }
            openings
        }
        Claims::Point => batch(channel, &combined, &layouts, bit_slice, ring_map.as_deref())?,
    };
    Ok(Reduced {
        roots: [root1, root2],
        openings,
        matrices,
        relations: relations.list.len(),
        stack_vars,
    })
}

/// The three stacks' layouts (SPEC.md §3).
fn layouts(shape: &Shape, c2_columns: &[(Column, usize, bool)]) -> Vec<(Commitment, StackLayout)> {
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
    let setup = vec![
        (Column::BytecodeTuple, shape.log_bytecode + 4, false),
        (Column::Address, shape.log_memory, false),
    ];
    vec![
        (Commitment::C1, StackLayout::new(&c1)),
        (Commitment::C2, StackLayout::new(c2_columns)),
        (Commitment::Setup, StackLayout::new(&setup)),
    ]
}

/// A combined claim's weight at the stack point `r`: every term's eq weight on its column's blocks; the ring-switch
/// term ([`RING_TWIST`]) by its map.
///
/// Shared work: a column's limbs share its row, so a column's part is `Σ_limb basis_limb · selector_limb` once; terms
/// on one row (point, length, twist) add their `coefficient · part` before the row multiplies them; `q_flock`'s slots
/// at one point share the instance coordinates' eq, and differ only in their 8 slot bits' factors.
fn weight_at<S: Scalar>(
    claim: &Combined<S>,
    layout: &StackLayout,
    r: &[S],
    base_id: usize,
    ring_map: Option<&[S]>,
) -> S {
    let mut cache = EqCache::new(r);
    let basis = limb_basis::<S>();
    let mut parts: Vec<(Column, usize, S)> = Vec::new();
    let mut part = |cache: &mut EqCache<S>, column: Column| -> (usize, S) {
        if let Some(&(_, vars, sum)) = parts.iter().find(|(c, ..)| *c == column) {
            return (vars, sum);
        }
        let limbs = layout.limbs(column);
        let vars = limbs[0].1;
        let mut sum = S::zero();
        for (limb, v, offset) in limbs {
            assert_eq!(v, vars, "a column's limbs are blocks of one size");
            let selector = cache.selector(vars, offset);
            sum += if limb == 0 { selector } else { basis[limb] * selector };
        }
        parts.push((column, vars, sum));
        (vars, sum)
    };
    // Σ coefficient · part, by row: (point, length, twist).
    let mut rows: Vec<((usize, usize, u8), S)> = Vec::new();
    // q_flock's slots, by point: Σ coefficient · eq(slot bits, r_(<8)).
    let mut slots: Vec<(usize, S)> = Vec::new();
    for &(column, p, twist, coefficient) in &claim.terms {
        if let Column::QflockSlot(j) = column {
            // q_flock's word `slot + 256 · instance`: the slot's bits, then the instance's coordinates.
            let bits = (0..8).fold(S::one(), |acc, b| {
                acc * if j >> b & 1 == 1 { r[b] } else { cache.one_plus_r()[b] }
            });
            let c = coefficient * bits;
            match slots.iter_mut().find(|(q, _)| *q == p) {
                Some((_, sum)) => *sum += c,
                None => slots.push((p, c)),
            }
            continue;
        }
        let (vars, sum) = part(&mut cache, column);
        let c = coefficient * sum;
        match rows.iter_mut().find(|(key, _)| *key == (p, vars, twist)) {
            Some((_, total)) => *total += c,
            None => rows.push(((p, vars, twist), c)),
        }
    }
    let mut total = S::zero();
    for ((p, len, twist), sum) in rows {
        let point = &claim.points[p];
        let row = if twist == RING_TWIST {
            let map = ring_map.expect("the ring map of a ring-switch term");
            let _phase = enter("claims: the ring switch's weight at the batch's point");
            ring_tower::weight_at(&point[..len], &cache.one_plus_r()[..len], map)
        } else {
            cache.row(base_id + p, point, len, twist)
        };
        total += row * sum;
    }
    for (p, sum) in slots {
        let point = &claim.points[p];
        let (_, qflock) = part(&mut cache, Column::Qflock);
        let instance = cache.row_from(base_id + 1000 + p, point, 8);
        total += sum * instance * qflock;
    }
    total
}

/// The batching sumcheck (SPEC.md §8): `Σ_k λ^k Σ_u W_k(u) C_k(u)` over the longest stack, the others zero-extended;
/// at its end point `r`, the prover sends each `C_k(r)` and the verifier checks the sum with `W_k(r)`.
fn batch<S: Scalar + PartialEq, C: Channel<S>>(
    channel: &mut C,
    combined: &[(Commitment, Combined<S>)],
    layouts: &[(Commitment, StackLayout)],
    bit_slice: Option<Combined<S>>,
    ring_map: Option<&[S]>,
) -> Result<Vec<(Commitment, Opening<S>)>, VerifierError> {
    let _phase = enter("claims: batching sumcheck to point claims");
    let lambda = channel.sample();
    let vars = layouts.iter().map(|(_, l)| l.vars).max().expect("stacks");
    let mut target = S::zero();
    let mut scale = S::one();
    for (_, claim) in combined {
        target += scale * claim.value;
        scale *= lambda;
    }
    let (r, last) = sumcheck(channel, target, 3, &vec![None; vars])?;
    let values = channel.next_scalars(combined.len())?;
    let _weights = enter("claims: the batch's weights at its point (eq, selectors, twists)");
    let mut sum = S::zero();
    let mut scale = S::one();
    let mut openings = Vec::new();
    let mut bit_slice = bit_slice;
    for (k, ((commitment, claim), &value)) in combined.iter().zip(&values).enumerate() {
        let layout = &layouts.iter().find(|(c, _)| c == commitment).expect("a layout").1;
        let weight = weight_at(claim, layout, &r, 10_000 * k, ring_map);
        let extension = (layout.vars..vars).fold(S::one(), |acc, j| acc * (S::one() + r[j]));
        sum += scale * weight * extension * value;
        scale *= lambda;
        openings.push((
            *commitment,
            Opening::Point {
                point: r[..layout.vars].to_vec(),
                value,
                bit_slice: if *commitment == Commitment::C1 { bit_slice.take() } else { None },
            },
        ));
    }
    channel.require_zero(sum + last, VerifierError::StackBatchTerminal)?;
    Ok(openings)
}
