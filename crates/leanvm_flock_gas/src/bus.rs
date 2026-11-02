// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/bus.rs: the same
// GKR, leaf decomposition and table sumcheck on a generic `Scalar` and `Channel`, the checks stated to the channel, the
// bytecode's value supplied by the caller (evaluated, or read from the proof and left as a claim), and the gas report's
// phase names. MIT OR Apache-2.0; see NOTICE.md.
//! Bus balance and decomposition, then the table sumcheck.

use crate::layout::{
    BUS_BITS, BYTECODE_FINAL_COUNTERS, BusBlock, Form, GLOBAL_COLUMN_BASES, Layout, MEMORY_0, MEMORY_1, MEMORY_2,
    MEMORY_FINAL_COUNTERS, SEP_BYTECODE, SEP_MEM, SEP_STATE, Table, gpow,
};
use crate::multilinear::{
    Placement, dot, eq_eval, eq_kernel, index_mle, multilinear_eval, padding_weight, poly_eval, stack_offsets,
};
use crate::scalar::{Scalar, enter};
use crate::transcript::{Channel, sumcheck};
use crate::{StackClaim, VerifierError};

fn verify_gkr_grand_products<S: Scalar>(
    depth: usize,
    transcript: &mut impl Channel<S>,
) -> Result<(S, Vec<S>, Vec<S>), VerifierError> {
    let _phase = enter("bus GKR: layers");
    let (shared, count) = (transcript.next_scalar()?, transcript.next_scalar()?);
    let mut point: Vec<S> = Vec::new();
    let mut values = vec![shared, shared, count]; // 3 grand product GKR are batched together: push, pull, count

    let mut layer = depth;
    while layer > 0 {
        // Two levels a step. An odd depth starts with one.
        let step = if layer % 2 == 1 { 1 } else { 2 };
        let combiner = transcript.sample();
        let claim = poly_eval(&values, combiner);
        // The product is degree 2^step, so one more coefficient than that per round.
        let equalities: Vec<Option<S>> = point.iter().copied().map(Some).collect();
        let (x, claim) = {
            let _rounds = enter("bus GKR: sumcheck rounds");
            sumcheck(transcript, claim, (1 << step) + 1, &equalities)?
        };

        let children = [
            transcript.next_scalars(1 << step)?,
            transcript.next_scalars(1 << step)?,
            transcript.next_scalars(1 << step)?,
        ];
        let products = children
            .each_ref()
            .map(|child| child.iter().fold(S::one(), |acc, &value| acc * value));
        transcript.require_zero(claim + poly_eval(&products, combiner), VerifierError::GkrLayer(layer))?;

        let y = transcript.samples(step);
        values.clear();
        for child in &children {
            values.push(multilinear_eval(child, &y)?);
        }
        point = [y, x].concat();
        layer -= step;
    }

    Ok((count, point, values))
}

/// Where a side's blocks sit in the stacked leaf cube. Split by kind because framework coordinates are
/// public, so the verifier evaluates their fingerprints outright, while a table's stay symbolic until its sumcheck.
struct BusLayout {
    depth: usize,              // log2 of the padded cube, so how many layers the side's GKR walks
    framework: Vec<Placement>, // the blocks no table owns, stacked first: boundary state, memory, bytecode (none on the count side)
    tables: Vec<Placement>,    // one per block a table owns, in the side's own block order
}

fn bus_layout(framework_log_rows: &[usize], blocks: &[BusBlock]) -> BusLayout {
    let sizes: Vec<usize> = framework_log_rows
        .iter()
        .copied()
        .chain(blocks.iter().map(|block| block.log_rows))
        .collect();
    let (offsets, depth) = stack_offsets(&sizes);
    let mut framework: Vec<Placement> = sizes
        .iter()
        .zip(offsets)
        .map(|(&variables, index)| Placement {
            variables,
            index,
            low: 0,
        })
        .collect();
    let tables = framework.split_off(framework_log_rows.len());
    BusLayout {
        depth,
        framework,
        tables,
    }
}

pub struct ColumnClaim<S> {
    pub column: usize,
    pub point: Vec<S>,
    pub value: S,
}

impl<S: Scalar> ColumnClaim<S> {
    pub fn on_stack<'a>(&self, layout: &Layout) -> StackClaim<'a, S> {
        let point = layout.placements[self.column].stack_point(&self.point, layout.stack_log);
        (Box::new(move |x| eq_eval(&point, x)), self.value)
    }
}

/// One side of the bus: its blocks, their layout, its framework fingerprints, its tuple weights and its beta.
type Side<'a, S> = (&'a [BusBlock], &'a BusLayout, Vec<S>, &'a [S], S);

pub struct BusResult<S> {
    pub claims: Vec<ColumnClaim<S>>,
    pub bytecode_point: Vec<S>, // where the bus reads the stacked bytecode: zeta's low coordinates, then alpha
    pub bytecode_value: S,
    pub point: Vec<S>,            // the GKR point zeta, which the table sumcheck reuses
    pub forms: Vec<Vec<Form<S>>>, // forms[table][side]
    pub totals: Vec<S>,           // what the tables owe each side, derived
}

/// The bus. `bytecode_value` gives the stacked bytecode's value at its point: leanVM evaluates it; the contract reads
/// it from the proof, leaving a claim on the bytecode's commitment.
pub fn verify_bus_balance<S: Scalar, C: Channel<S>>(
    layout: &Layout,
    transcript: &mut C,
    bytecode_value: impl FnOnce(&mut C, &[S]) -> Result<S, VerifierError>,
) -> Result<BusResult<S>, VerifierError> {
    let framework_log_rows = [0, layout.log_memory, layout.log_bytecode]; // state, memory, bytecode
    let push_layout = bus_layout(&framework_log_rows, &layout.push);
    let pull_layout = bus_layout(&framework_log_rows, &layout.pull);
    let count_layout = bus_layout(&[], &layout.count);

    let alphas = transcript.samples(BUS_BITS);
    let weights = {
        let _phase = enter("bus leaves: fingerprints, selectors, padding");
        eq_kernel(&alphas)
    };
    let beta = transcript.sample();
    let (count_root, point, tree_values) = verify_gkr_grand_products(push_layout.depth, transcript)?;
    transcript.require_nonzero(count_root, VerifierError::BusCountZero)?;

    let _phase = enter("bus leaves: fingerprints, selectors, padding");
    // The framework blocks' committed columns, in the order the two sides first
    // name them: the memory image on push, then each array's final count on pull.
    let memory_low = &point[..layout.log_memory];
    let bytecode_low = &point[..layout.log_bytecode];
    let memory = transcript.next_scalars(3)?;
    let memory_final = transcript.next_scalar()?;
    let bytecode_final = transcript.next_scalar()?;
    let claim = |column: usize, point: &[S], value: S| ColumnClaim {
        column,
        point: point.to_vec(),
        value,
    };
    let mut claims: Vec<ColumnClaim<S>> = [MEMORY_0, MEMORY_1, MEMORY_2]
        .map(|column| claim(column, memory_low, memory[column]))
        .into();
    claims.push(claim(MEMORY_FINAL_COUNTERS, memory_low, memory_final));
    claims.push(claim(BYTECODE_FINAL_COUNTERS, bytecode_low, bytecode_final));
    let memory_index = index_mle(memory_low);
    let bytecode_index = index_mle(bytecode_low);
    let bytecode_point = [bytecode_low, &alphas].concat();
    let bytecode_value = bytecode_value(transcript, &bytecode_point)?;

    // The three framework tuples, each its coordinates weighted by eq(alpha, .); slots past the ones
    // named are zero. A side differs only here: push seeds each array at count one, pull finalizes it
    // with the committed final count and ends at the last pc. Both boundaries sit in frame 0.
    let c = S::constant;
    let fingerprints = |pc: S, memory_count: S, bytecode_count: S| {
        vec![
            dot(&weights[..3], &[c(SEP_STATE), pc, c(gpow(0))]),
            dot(
                &weights[..6],
                &[c(SEP_MEM), memory_index, memory_count, memory[0], memory[1], memory[2]],
            ),
            dot(&weights[..3], &[c(SEP_BYTECODE), bytecode_index, bytecode_count]) + bytecode_value,
        ]
    };

    let final_pc = gpow((1 << layout.log_bytecode) - 1); // the execution ends at the bytecode's last instruction
    let one = S::one();
    let count_weights = [one];
    let sides: [Side<S>; 3] = [
        (
            &layout.push,
            &push_layout,
            fingerprints(c(gpow(0)), one, one),
            &weights,
            beta,
        ),
        (
            &layout.pull,
            &pull_layout,
            fingerprints(c(final_pc), memory_final, bytecode_final),
            &weights,
            beta,
        ),
        (&layout.count, &count_layout, vec![], &count_weights, S::zero()), // The count channel owns no framework block and runs at alpha = beta = 0.
    ];
    let mut totals = Vec::new(); // what remains to be proven by the next table sumcheck
    let mut forms = vec![vec![Form::<S>::default(); 3]; layout.tables.len()];
    for (side, (blocks, side_layout, framework_fingerprints, side_weights, side_beta)) in sides.into_iter().enumerate()
    {
        let framework_selectors: Vec<S> = side_layout.framework.iter().map(|p| p.eq_above(&point)).collect();
        let table_selectors: Vec<S> = side_layout.tables.iter().map(|p| p.eq_above(&point)).collect();
        let shifted: Vec<S> = framework_fingerprints.iter().map(|&f| side_beta + f).collect();
        let known = dot(&framework_selectors, &shifted);
        // A table's blocks stay symbolic: they accumulate into the form its sumcheck settles over its own columns.
        // That form is summed over the padding rows too, whose leaves hold 1 instead: the difference is public.
        let mut padding_rows = S::zero();
        for (&selector, block) in table_selectors.iter().zip(blocks) {
            let form = &mut forms[block.owner][side];
            let mut block_form = Form::term(vec![], side_beta);
            for (slot, coordinate) in block.coordinates.iter().enumerate() {
                block_form.add_scaled(coordinate, side_weights[slot]); // the fingerprint, one tuple slot at a time
            }
            form.add_scaled_form(&block_form, selector);
            let padding: Vec<S> = layout.tables[block.owner].padding.iter().map(|&v| c(v)).collect();
            let weight = padding_weight(&point[..block.log_rows], block.rows);
            padding_rows += selector * weight * (block_form.evaluate(&padding) + one);
        }
        // The leaves outside every block hold 1.
        let ones_padding = S::sum(framework_selectors.into_iter().chain(table_selectors)) + one;
        totals.push(tree_values[side] + known + ones_padding + padding_rows); // what the forms owe: the GKR value, less framework and padding
    }

    Ok(BusResult {
        claims,
        bytecode_point,
        bytecode_value,
        point,
        forms,
        totals,
    })
}

pub fn table_sumcheck<S: Scalar>(
    tables: &[Table],
    table_log_heights: &[usize],
    bus_forms: &[Vec<Form<S>>],
    constraint_powers: &[S],
    form_powers: &[S],
    equality_point: &[S],
    target: S,
    transcript: &mut impl Channel<S>,
) -> Result<Vec<ColumnClaim<S>>, VerifierError> {
    let n_rounds = table_log_heights.iter().copied().max().unwrap_or(0);
    let (challenges, claim) = {
        let _phase = enter("table sumcheck: rounds");
        sumcheck(transcript, target, 4, &vec![None; n_rounds])?
    };
    let _phase = enter("table sumcheck: terminal (constraints, bus forms)");
    let point: Vec<S> = challenges.into_iter().rev().collect();
    let mut weights = vec![S::one(); tables.len()];
    for (variable, &challenge) in point.iter().enumerate() {
        let equality = S::one() + equality_point[variable] + challenge;
        for (index, &height) in table_log_heights.iter().enumerate() {
            weights[index] *= if height > variable { equality } else { challenge };
        }
    }

    let mut claims = Vec::new();
    let mut rows = Vec::with_capacity(tables.len());
    for (table, &height) in tables.iter().zip(table_log_heights) {
        let evaluations = transcript.next_scalars(table.width())?;
        let table_point = &point[..height];
        claims.extend(evaluations.iter().enumerate().map(|(local, &value)| ColumnClaim {
            column: GLOBAL_COLUMN_BASES[table.opcode] + local,
            point: table_point.to_vec(),
            value,
        }));
        rows.push(evaluations);
    }
    let mut terminal = S::zero();
    let mut cursor = 0;
    for (((table, evaluations), forms), &weight) in tables.iter().zip(&rows).zip(bus_forms).zip(&weights) {
        let n_constraints = table.n_constraints();
        let summand = dot(
            &constraint_powers[cursor..cursor + n_constraints],
            &table.constraints(evaluations),
        );
        let form_values: Vec<S> = forms.iter().map(|form| form.evaluate(evaluations)).collect();
        terminal += weight * (summand + dot(form_powers, &form_values));
        cursor += n_constraints;
    }
    transcript.require_zero(terminal + claim, VerifierError::TableSumcheckTerminal)?;
    Ok(claims)
}
