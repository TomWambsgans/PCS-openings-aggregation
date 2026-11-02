// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! A program cut into contracts that each fit: a driver and the parts it calls.

use std::collections::HashMap;
use std::ops::Range;

use crate::assemble::{Call, End, Frame, assemble_frame};
use crate::op::{
    CALLVALUE, CODECOPY, CODESIZE, JUMPDEST, JUMPI, MLOAD, OR, PUSH0, RETURN, REVERT, SSTORE, XOR, push_fixed,
    push_usize, stack_effect,
};
use crate::{Assembled, Item, Options, Program, assemble};

/// One contract of a linked program.
#[derive(Clone, Debug)]
pub struct Part {
    pub code: Assembled,
    /// The program's items it runs.
    pub items: Range<usize>,
    /// Values it reads from earlier parts, and values it returns for later ones (besides the stack's).
    pub imports: usize,
    pub exports: usize,
    /// Words on the stack where it starts and where it ends, passed like the values.
    pub stack_in: usize,
    pub stack_out: usize,
}

/// A program as contracts: the driver, then the parts it `DELEGATECALL`s, in order.
#[derive(Clone, Debug)]
pub struct Linked {
    pub driver: Part,
    pub parts: Vec<Part>,
    /// Words of the driver's values region.
    pub values: usize,
}

impl Linked {
    /// The driver's code, calling the parts at these addresses.
    pub fn driver_code(&self, addresses: &[[u8; 20]]) -> Vec<u8> {
        assert_eq!(addresses.len(), self.parts.len(), "an address a part");
        let mut code = self.driver.code.code.clone();
        for (&at, address) in self.driver.code.chunk_patches.iter().zip(addresses) {
            code[at..at + 20].copy_from_slice(address);
        }
        code
    }

    /// Where each part starts in the program's items: the cuts, for [`link_at`].
    pub fn starts(&self) -> Vec<usize> {
        self.parts.iter().map(|part| part.items.start).collect()
    }

    /// Every contract's code bytes.
    pub fn code_bytes(&self) -> usize {
        self.driver.code.code.len() + self.parts.iter().map(|part| part.code.code.len()).sum::<usize>()
    }
}

/// The stack's height before each item, and after the last.
fn heights(items: &[(Item, crate::Tag)]) -> Vec<usize> {
    let mut heights = Vec::with_capacity(items.len() + 1);
    let mut height = 0isize;
    for (item, _) in items {
        heights.push(height as usize);
        let (effect, reads) = match item {
            Item::Code(bytes) => stack_effect(bytes),
            Item::Store(_) => (0, 1),
            Item::Load(_) | Item::Calldata { .. } => (1, 0),
            Item::Output(_) | Item::FailIf | Item::OtherIf => (-1, 1),
            Item::CopyConst { .. } | Item::PcsOpen { .. } | Item::Seam => (0, 0),
        };
        assert!(reads as isize <= height, "an item reads below the stack");
        height += effect;
    }
    assert_eq!(height, 0, "the program leaves the stack empty");
    heights.push(0);
    heights
}

/// A run of items, the frame of one contract once it is placed: where it reads values computed before it, and those it
/// keeps for later.
struct Run {
    range: Range<usize>,
    stack_in: Vec<usize>,
    imports: HashMap<u32, usize>,
    pinned: Vec<u32>,
    stack_out: usize,
    /// The ranges of the call's calldata it reads, in order.
    window: Vec<Range<usize>>,
}

/// What cutting a program needs to know of it.
struct Cutter<'a> {
    program: &'a Program,
    heights: Vec<usize>,
    /// Where each node is kept, and where it is last read.
    stored: HashMap<u32, usize>,
    last_load: HashMap<u32, usize>,
    /// Where the program may be cut.
    cuts: Vec<usize>,
    /// Before each item, the values kept before it and read at or after it.
    live: Vec<usize>,
}

impl<'a> Cutter<'a> {
    fn new(program: &'a Program) -> Self {
        let items = &program.items;
        let n = items.len();
        let ends_run = |item: &Item| matches!(item, Item::Output(_) | Item::CopyConst { .. } | Item::PcsOpen { .. });
        // The outputs region is the last part's, and the other entry the driver's.
        let first_output = items.iter().position(|(item, _)| ends_run(item)).unwrap_or(n);
        let after_other = items
            .iter()
            .rposition(|(item, _)| *item == Item::OtherIf)
            .map_or(0, |at| at + 1);
        let cuts = (after_other.max(1)..first_output)
            .filter(|&at| items[at].0 == Item::Seam)
            .collect();
        let mut stored = HashMap::new();
        let mut last_load = HashMap::new();
        for (at, (item, _)) in items.iter().enumerate() {
            match *item {
                Item::Store(id) => {
                    stored.entry(id).or_insert(at);
                }
                Item::Load(id) => {
                    last_load.insert(id, at);
                }
                _ => {}
            }
        }
        let mut delta = vec![0isize; n + 2];
        for (id, &at) in &stored {
            if let Some(&last) = last_load.get(id) {
                delta[at + 1] += 1;
                delta[last + 1] -= 1;
            }
        }
        let live = delta[..=n]
            .iter()
            .scan(0, |sum, d| {
                *sum += d;
                Some(*sum as usize)
            })
            .collect();
        Self {
            program,
            heights: heights(items),
            stored,
            last_load,
            cuts,
            live,
        }
    }

    /// The run `range`, the values written before it being at `position` (and the stack's from `stack_at`).
    fn run(&self, range: Range<usize>, position: &HashMap<u32, usize>, stack_at: usize, last: bool) -> Run {
        let l = self.program.calldata_len;
        let (a, b) = (range.start, range.end);
        let stack_in = (0..self.heights[a]).map(|t| 32 * (stack_at + t)).collect();
        let mut imports = HashMap::new();
        let mut pinned = Vec::new();
        let mut reads = Vec::new();
        for (item, _) in &self.program.items[range.clone()] {
            match *item {
                Item::Calldata { offset, len } => {
                    reads.push(offset..(offset + len).min(l).max(offset));
                }
                Item::Load(id) if self.stored[&id] < a => {
                    imports.insert(id, 32 * position[&id]);
                }
                Item::Store(id)
                    if !last && self.last_load.get(&id).is_some_and(|&at| at >= b) && !pinned.contains(&id) =>
                {
                    pinned.push(id);
                }
                _ => {}
            }
        }
        Run {
            range,
            stack_in,
            imports,
            pinned,
            stack_out: if last { 0 } else { self.heights[b] },
            window: ranges(reads),
        }
    }

    /// The run's frame, a part's passed `values` words of the values region (the driver's: `None`).
    fn frame(&self, run: &Run, values: Option<usize>, end: End) -> Frame<'a> {
        Frame {
            items: &self.program.items[run.range.clone()],
            stack_in: run.stack_in.clone(),
            imports: run.imports.clone(),
            pinned: run.pinned.clone(),
            window: values.map(|values| {
                let mut at = 32 * values;
                let mut placed = Vec::new();
                for range in &run.window {
                    placed.push((range.clone(), at));
                    at += range.len();
                }
                placed
            }),
            end,
        }
    }

    /// Place run `k`, which ends at item `b`, in `region`: its values and its stack's words, together, at the first
    /// words free once it has run (those of values no later run reads, and of stacks already taken back).
    fn place(&self, region: &mut Region, k: usize, run: &Run) {
        let b = run.range.end;
        let free = |holder: &Holder| match *holder {
            Holder::Free => true,
            Holder::Value(id) => self.last_load.get(&id).is_none_or(|&at| at < b),
            Holder::Stack(j) => j < k,
        };
        let m = run.pinned.len() + run.stack_out;
        let mut at = 0;
        while let Some(taken) = (at..at + m).find(|&w| w < region.words.len() && !free(&region.words[w])) {
            at = taken + 1;
        }
        if region.words.len() < at + m {
            region.words.resize(at + m, Holder::Free);
        }
        for (t, &id) in run.pinned.iter().enumerate() {
            region.words[at + t] = Holder::Value(id);
            region.position.insert(id, at + t);
        }
        for t in 0..run.stack_out {
            region.words[at + run.pinned.len() + t] = Holder::Stack(k);
        }
        region.stack_at = at + run.pinned.len();
        region.blocks.push((at, region.words.len()));
    }

    /// The runs starting at 0 and at each of `starts`, placed in order.
    fn runs(&self, starts: &[usize]) -> (Vec<Run>, Region) {
        let n = self.program.items.len();
        let bounds: Vec<usize> = [&[0][..], starts, &[n]].concat();
        let mut region = Region::default();
        let mut runs = Vec::new();
        for (k, pair) in bounds.windows(2).enumerate() {
            let last = k + 2 == bounds.len();
            let run = self.run(pair[0]..pair[1], &region.position, region.stack_at, last);
            if !last {
                self.place(&mut region, k, &run);
            }
            runs.push(run);
        }
        (runs, region)
    }

    /// Each part's call by the driver: it is passed the words of the values region written to before it, and its
    /// own are kept where they were placed.
    fn calls(runs: &[Run], region: &Region) -> Vec<Call> {
        (1..runs.len())
            .map(|k| {
                let last = k + 1 == runs.len();
                Call {
                    values: region.blocks[k - 1].1,
                    returns: if last {
                        0
                    } else {
                        runs[k].pinned.len() + runs[k].stack_out
                    },
                    at: if last { 0 } else { region.blocks[k].0 },
                    ranges: runs[k].window.clone(),
                }
            })
            .collect()
    }

    /// Bytes an item's code takes, about (a slot's or a value's address in two bytes).
    fn bytes(item: &Item) -> usize {
        match item {
            Item::Code(bytes) => bytes.len(),
            Item::Store(_) => 5,
            Item::Load(_) | Item::Output(_) | Item::FailIf | Item::OtherIf => 4,
            Item::Calldata { .. } => 3,
            Item::Seam => 0,
            Item::CopyConst { .. } | Item::PcsOpen { .. } => 30,
        }
    }

    /// Among the cuts `candidates` (the last the latest that fits), those in the last twelfth of a part of `limit`
    /// bytes, the cheapest: the fewest values live across it and words on the stack (about [`CROSSING_GAS`] a word:
    /// what a cut through short-lived values adds), against the code it leaves unused (a cold call a part,
    /// [`CALL_GAS`], for `limit` bytes).
    fn cheapest(&self, candidates: &[usize], limit: usize) -> usize {
        let items = &self.program.items;
        let latest = *candidates.last().expect("a cut");
        let (mut unused, mut at, mut best) = (0, latest, (u64::MAX, latest));
        for &cut in candidates.iter().rev() {
            while at > cut {
                at -= 1;
                unused += Self::bytes(&items[at].0);
            }
            if 12 * unused > limit {
                break;
            }
            let words = (self.live[cut] + self.heights[cut]) as u64;
            let cost = CROSSING_GAS * words * limit as u64 + CALL_GAS * unused as u64;
            if cost < best.0 {
                best = (cost, cut);
            }
        }
        best.1
    }
}

/// Calldata read, as the ranges copied for it: reads closer than [`GAP`] bytes are one range.
fn ranges(mut reads: Vec<Range<usize>>) -> Vec<Range<usize>> {
    reads.sort_by_key(|range| range.start);
    let mut ranges: Vec<Range<usize>> = Vec::new();
    for read in reads {
        match ranges.last_mut() {
            Some(last) if read.start <= last.end + GAP => last.end = last.end.max(read.end),
            _ => ranges.push(read),
        }
    }
    ranges
}

/// Bytes of calldata between two reads below which one copy takes both (a copy is about 15 gas, a word 3).
const GAP: usize = 128;

/// Gas a word passed between parts costs, about: written to the part's returned region (memory), copied by the driver
/// (`RETURNDATACOPY`, and its memory).
const CROSSING_GAS: u64 = 12;
/// Gas a part costs, about: a cold `DELEGATECALL`.
const CALL_GAS: u64 = 2_600;

/// What a word of the values region holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Holder {
    Free,
    Value(u32),
    /// A word left on the stack by this run, which the next takes back.
    Stack(usize),
}

/// The driver's values region, as runs are placed in it.
#[derive(Clone, Debug, Default)]
struct Region {
    position: HashMap<u32, usize>,
    words: Vec<Holder>,
    /// Where the last run placed left its stack's words.
    stack_at: usize,
    /// Each run placed: where its words start, and the words of the region written to once they are.
    blocks: Vec<(usize, usize)>,
}

/// The program as one contract, all of it in the driver.
fn single(program: &Program, code: Assembled) -> Linked {
    Linked {
        driver: Part {
            code,
            items: 0..program.items.len(),
            imports: 0,
            exports: 0,
            stack_in: 0,
            stack_out: 0,
        },
        parts: Vec::new(),
        values: 0,
    }
}

/// `options`, with jumps wide enough for code of any length: code is no longer with narrower ones.
fn wide<'a>(options: &Options<'a>) -> Options<'a> {
    Options {
        jump_width: options.jump_width.max(3),
        ..*options
    }
}

/// The program as contracts of at most `limit` bytes each: as one ([`assemble`]'s code, no parts) if it fits,
/// else a driver and parts, cut at seams, in order: each part as long as fits, but for a cut a little before that
/// leaving fewer values to pass ([`Cutter::cheapest`]).
pub fn link(program: &Program, options: &Options, limit: usize) -> Linked {
    let n = program.items.len();
    let mut whole = assemble(program, &wide(options));
    if whole.code.len() < 1 << (8 * options.jump_width) {
        whole = assemble(program, options);
    }
    if whole.code.len() <= limit {
        return single(program, whole);
    }
    let cutter = Cutter::new(program);
    let wide = wide(options);
    // A part laid out as if passed many values (offsets of the widest pushes).
    let fits = |run: &Run, end: End| {
        let values = (run.range.start > 0).then_some(1 << 11);
        assemble_frame(&cutter.frame(run, values, end), program, &wide)
            .code
            .len()
            <= limit
    };
    // The driver's calls are laid out for `reserve` parts (values and calldata at offsets of two bytes, each part's
    // calldata one range), until it has that many; `link_at` lays it out as it is.
    let mut reserve = whole.code.len().div_ceil(limit);
    loop {
        let provisional = |stack_out: usize| End::Drive {
            stack_out,
            calls: (0..reserve)
                .map(|_| Call {
                    values: 1 << 8,
                    returns: 1 << 8,
                    at: 1 << 8,
                    ranges: std::iter::once(1 << 8..1 << 9).collect(),
                })
                .collect(),
        };
        let mut starts: Vec<usize> = Vec::new();
        let mut region = Region::default();
        let mut a = 0;
        loop {
            if a > 0 && fits(&cutter.run(a..n, &region.position, region.stack_at, true), End::Program) {
                break;
            }
            let end_of = |run: &Run| {
                if a == 0 {
                    provisional(run.stack_out)
                } else {
                    End::Return {
                        stack_out: run.stack_out,
                    }
                }
            };
            // The longest run that fits, among the cuts after `a`.
            let candidates: Vec<usize> = cutter.cuts.iter().copied().filter(|&at| at > a).collect();
            let (mut lo, mut hi) = (0usize, candidates.len());
            while lo < hi {
                let mid = (lo + hi).div_ceil(2);
                let r = cutter.run(a..candidates[mid - 1], &region.position, region.stack_at, false);
                if fits(&r, end_of(&r)) {
                    lo = mid;
                } else {
                    hi = mid - 1;
                }
            }
            if lo == 0 {
                let first = candidates.first().map(|&b| {
                    let r = cutter.run(a..b, &region.position, region.stack_at, false);
                    let code = assemble_frame(
                        &cutter.frame(&r, (a > 0).then_some(1 << 11), end_of(&r)),
                        program,
                        &wide,
                    );
                    (b, code.code.len(), r.pinned.len(), r.imports.len(), r.stack_out)
                });
                panic!(
                    "no cut after item {a} gives a part of at most {limit} bytes: the first, (cut, bytes, kept, read, stack) {first:?}, of {} cuts",
                    candidates.len()
                );
            }
            let b = cutter.cheapest(&candidates[..lo], limit);
            let run = cutter.run(a..b, &region.position, region.stack_at, false);
            cutter.place(&mut region, starts.len(), &run);
            starts.push(b);
            a = b;
        }
        let linked = link_at(program, options, &starts);
        let fit = std::iter::once(&linked.driver)
            .chain(&linked.parts)
            .all(|part| part.code.code.len() <= limit);
        if fit {
            return linked;
        }
        assert!(
            starts.len() != reserve || reserve < 1 << 10,
            "no driver fits {limit} bytes"
        );
        reserve = if starts.len() > reserve {
            starts.len()
        } else {
            reserve + 1
        };
    }
}

/// The program cut before each of `starts` (items at seams, increasing): the driver runs the items before the first,
/// each part the items from its start to the next. With no starts, the program as one contract.
pub fn link_at(program: &Program, options: &Options, starts: &[usize]) -> Linked {
    if starts.is_empty() {
        return single(program, assemble(program, options));
    }
    let cutter = Cutter::new(program);
    assert!(
        starts.windows(2).all(|pair| pair[0] < pair[1]) && starts.iter().all(|at| cutter.cuts.contains(at)),
        "cuts at seams, in order"
    );
    let (runs, region) = cutter.runs(starts);
    let count = runs.len();
    let driver_end = End::Drive {
        stack_out: runs[0].stack_out,
        calls: Cutter::calls(&runs, &region),
    };
    let part = |r: &Run, code: Assembled| Part {
        code,
        items: r.range.clone(),
        imports: r.imports.len(),
        exports: r.pinned.len(),
        stack_in: r.stack_in.len(),
        stack_out: r.stack_out,
    };
    let driver = assemble_frame(&cutter.frame(&runs[0], None, driver_end), program, options);
    let parts = runs
        .iter()
        .enumerate()
        .skip(1)
        .map(|(k, r)| {
            let end = if k + 1 == count {
                End::Program
            } else {
                End::Return { stack_out: r.stack_out }
            };
            let values = region.blocks[k - 1].1;
            part(r, assemble_frame(&cutter.frame(r, Some(values), end), program, options))
        })
        .collect();
    Linked {
        driver: part(&runs[0], driver),
        parts,
        values: region.words.len(),
    }
}

/// The creation code of `runtime`, which the constructor's arguments follow in the init code: one word for each of
/// `slots`, which it stores there. It reverts on value or on arguments of another length, else returns `runtime`.
pub fn creation_code(runtime: &[u8], slots: &[u8]) -> Vec<u8> {
    let arguments = 32 * slots.len();
    // The revert is the last 4 bytes of the `prefix` bytes before the code.
    let build = |prefix: usize| {
        let length = [
            &[CODESIZE][..],
            &push_fixed(prefix + runtime.len() + arguments, 2),
            &[XOR, CALLVALUE, OR],
        ];
        let mut code = [&length.concat()[..], &push_fixed(prefix - 4, 2), &[JUMPI]].concat();
        // The code and the arguments, to memory at 0.
        let copy = [
            &push_fixed(runtime.len() + arguments, 2)[..],
            &push_fixed(prefix, 2),
            &[PUSH0, CODECOPY],
        ];
        code.extend(copy.concat());
        for (k, &slot) in slots.iter().enumerate() {
            let store = [
                &push_fixed(runtime.len() + 32 * k, 2)[..],
                &[MLOAD],
                &push_usize(slot.into()),
                &[SSTORE],
            ];
            code.extend(store.concat());
        }
        code.extend(
            [
                &push_fixed(runtime.len(), 2)[..],
                &[PUSH0, RETURN, JUMPDEST, PUSH0, PUSH0, REVERT],
            ]
            .concat(),
        );
        code
    };
    let prefix = build(4).len();
    [build(prefix), runtime.to_vec()].concat()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{POP, push_usize};
    use crate::{Ending, Tag};

    const TAG: Tag = "";

    /// A program of `blocks` blocks of `k` values each, every value read by the next block only, then a check.
    fn chain_of_blocks(blocks: usize, k: usize) -> Program {
        let mut items: Vec<(Item, Tag)> = vec![(Item::Code(vec![PUSH0]), TAG), (Item::FailIf, TAG)];
        let id = |b: usize, j: usize| (b * k + j) as u32;
        for b in 0..blocks {
            for j in 0..k {
                // The value: the previous block's j-th, or a constant.
                if b > 0 {
                    items.push((Item::Load(id(b - 1, j)), TAG));
                } else {
                    items.push((Item::Code(push_usize(j + 1)), TAG));
                }
                items.push((Item::Code(vec![crate::op::DUP1, crate::op::XOR]), TAG));
                items.push((Item::Store(id(b, j)), TAG));
                items.push((Item::Code(vec![POP]), TAG));
                items.push((Item::Seam, TAG));
            }
        }
        for j in 0..k {
            items.push((Item::Load(id(blocks - 1, j)), TAG));
            items.push((Item::FailIf, TAG));
        }
        Program {
            items,
            data: Vec::new(),
            scratch: 0,
            outputs: 0,
            ending: Ending::Attest,
            calldata_len: 4,
        }
    }

    #[test]
    fn close_reads_are_one_range() {
        assert_eq!(ranges(vec![300..332, 0..32, 40..64]), vec![0..64, 300..332]);
        assert_eq!(ranges(vec![0..32, 32 + GAP..64 + GAP]), vec![0..64 + GAP]);
        assert_eq!(ranges(vec![]), Vec::<Range<usize>>::new());
    }

    /// A program that fits is the one contract `assemble` makes; one that does not, contracts that each fit, the
    /// values each block passes to the next placed in words the block before freed.
    #[test]
    fn programs_are_linked_into_parts_that_fit() {
        let options = Options::default();
        let program = chain_of_blocks(40, 8);
        let one = assemble(&program, &options);
        let linked = link(&program, &options, one.code.len());
        assert!(linked.parts.is_empty() && linked.driver.code.code == one.code);

        let limit = 1_000;
        let linked = link(&program, &options, limit);
        assert!(linked.parts.len() >= 3, "{} parts", linked.parts.len());
        let sizes = std::iter::once(&linked.driver)
            .chain(&linked.parts)
            .map(|part| part.code.code.len());
        assert!(
            sizes.clone().all(|size| size <= limit),
            "{:?}",
            sizes.collect::<Vec<_>>()
        );
        // Each part passes on at most two blocks' values (and the stack, empty at a seam here): words are reused.
        let exported: usize = std::iter::once(&linked.driver)
            .chain(&linked.parts)
            .map(|part| part.exports)
            .sum();
        assert!(
            linked.values <= 2 * 8 && linked.values < exported,
            "{} words for {exported}",
            linked.values
        );
        // Cut where it was cut, it is the same.
        let again = link_at(&program, &options, &linked.starts());
        assert_eq!(again.driver.code.code, linked.driver.code.code);
        assert!(
            again
                .parts
                .iter()
                .zip(&linked.parts)
                .all(|(a, b)| a.code.code == b.code.code)
        );
    }

    /// The stack's height before every item: a seam may hold words on it, which a cut passes.
    #[test]
    fn heights_follow_the_stack() {
        let items: Vec<(Item, Tag)> = vec![
            (Item::Code(push_usize(1)), TAG),
            (Item::Seam, TAG),
            (Item::Calldata { offset: 0, len: 32 }, TAG),
            (Item::Code(vec![crate::op::CALLDATALOAD, crate::op::XOR]), TAG),
            (Item::Store(0), TAG),
            (Item::FailIf, TAG),
        ];
        assert_eq!(heights(&items), vec![0, 1, 1, 2, 1, 1, 0]);
    }
}
