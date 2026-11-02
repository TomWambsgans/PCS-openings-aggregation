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
            Item::Load(_) => (1, 0),
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
        Self {
            program,
            heights: heights(items),
            stored,
            last_load,
            cuts,
        }
    }

    /// The run `range`, the values written before it being at `position` (and the stack's from `stack_at`).
    fn run(&self, range: Range<usize>, position: &HashMap<u32, usize>, stack_at: usize, last: bool) -> Run {
        let l = self.program.calldata_len;
        let (a, b) = (range.start, range.end);
        let stack_in = (0..self.heights[a]).map(|t| l + 32 * (stack_at + t)).collect();
        let mut imports = HashMap::new();
        let mut pinned = Vec::new();
        for (item, _) in &self.program.items[range.clone()] {
            match *item {
                Item::Load(id) if self.stored[&id] < a => {
                    imports.insert(id, l + 32 * position[&id]);
                }
                Item::Store(id) if !last && self.last_load.get(&id).is_some_and(|&at| at >= b) => {
                    if !pinned.contains(&id) {
                        pinned.push(id);
                    }
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
        }
    }

    fn frame(&self, run: &Run, end: End) -> Frame<'a> {
        Frame {
            items: &self.program.items[run.range.clone()],
            stack_in: run.stack_in.clone(),
            imports: run.imports.clone(),
            pinned: run.pinned.clone(),
            end,
        }
    }

    /// The runs starting at 0 and at each of `starts`, with the values each keeps placed after those before.
    fn runs(&self, starts: &[usize]) -> Vec<Run> {
        let n = self.program.items.len();
        let bounds: Vec<usize> = [&[0][..], starts, &[n]].concat();
        let mut position = HashMap::new();
        let (mut values, mut stack_at) = (0, 0);
        let mut runs = Vec::new();
        for (k, pair) in bounds.windows(2).enumerate() {
            let last = k + 2 == bounds.len();
            let run = self.run(pair[0]..pair[1], &position, stack_at, last);
            for &id in &run.pinned {
                position.insert(id, values);
                values += 1;
            }
            stack_at = values;
            values += run.stack_out;
            runs.push(run);
        }
        runs
    }

    /// Each part's call by the driver: it reads the values written before it, and returns its own.
    fn calls(runs: &[Run]) -> (Vec<Call>, usize) {
        let mut calls = Vec::new();
        let mut written = runs[0].pinned.len() + runs[0].stack_out;
        for (k, r) in runs.iter().enumerate().skip(1) {
            let returns = if k + 1 == runs.len() {
                0
            } else {
                r.pinned.len() + r.stack_out
            };
            calls.push(Call {
                values: written,
                returns,
            });
            written += returns;
        }
        (calls, written)
    }
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
/// else a driver and parts, cut at seams so that each run is as long as fits, in order.
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
    let fits = |run: &Run, end: End| assemble_frame(&cutter.frame(run, end), program, &wide).code.len() <= limit;
    // The driver's calls are laid out for `reserve` parts, values at the widest offsets, until it has that many.
    let mut reserve = whole.code.len().div_ceil(limit);
    loop {
        let provisional = |stack_out: usize| End::Drive {
            stack_out,
            calls: (0..reserve)
                .map(|_| Call {
                    values: 1 << 11,
                    returns: 1 << 11,
                })
                .collect(),
        };
        let mut starts: Vec<usize> = Vec::new();
        let mut a = 0;
        loop {
            // The runs before `a`, placed.
            let runs = cutter.runs(&starts);
            let (position, stack_at) = placed(&runs[..runs.len() - 1]);
            if a > 0 && fits(&cutter.run(a..n, &position, stack_at, true), End::Program) {
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
                let r = cutter.run(a..candidates[mid - 1], &position, stack_at, false);
                if fits(&r, end_of(&r)) {
                    lo = mid;
                } else {
                    hi = mid - 1;
                }
            }
            assert!(lo > 0, "no cut after item {a} gives a part of at most {limit} bytes");
            a = candidates[lo - 1];
            starts.push(a);
        }
        let linked = link_at(program, options, &starts);
        let fit = std::iter::once(&linked.driver)
            .chain(&linked.parts)
            .all(|part| part.code.code.len() <= limit);
        if starts.len() <= reserve && fit {
            return linked;
        }
        reserve = starts.len().max(reserve + 1);
    }
}

/// Where the values the runs keep are, and where the last run leaves the stack's: those a run after them reads.
fn placed(runs: &[Run]) -> (HashMap<u32, usize>, usize) {
    let mut position = HashMap::new();
    let (mut values, mut stack_at) = (0, 0);
    for run in runs {
        for &id in &run.pinned {
            position.insert(id, values);
            values += 1;
        }
        stack_at = values;
        values += run.stack_out;
    }
    (position, stack_at)
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
    let runs = cutter.runs(starts);
    let count = runs.len();
    let (calls, values) = Cutter::calls(&runs);
    let driver_end = End::Drive {
        stack_out: runs[0].stack_out,
        calls,
    };
    let part = |r: &Run, code: Assembled| Part {
        code,
        items: r.range.clone(),
        imports: r.imports.len(),
        exports: r.pinned.len(),
        stack_in: r.stack_in.len(),
        stack_out: r.stack_out,
    };
    let driver = assemble_frame(&cutter.frame(&runs[0], driver_end), program, options);
    let parts = runs
        .iter()
        .enumerate()
        .skip(1)
        .map(|(k, r)| {
            let end = if k + 1 == count {
                End::Program
            } else {
                End::Return {
                    stack_out: r.stack_out,
                }
            };
            part(r, assemble_frame(&cutter.frame(r, end), program, options))
        })
        .collect();
    Linked {
        driver: part(&runs[0], driver),
        parts,
        values,
    }
}

/// The creation code of `runtime`, which the constructor's arguments follow in the init code: one word for each of
/// `slots`, which it stores there. It reverts on value or on arguments of another length, else returns `runtime`.
pub fn creation_code(runtime: &[u8], slots: &[u8]) -> Vec<u8> {
    let arguments = 32 * slots.len();
    // The revert is the last 4 bytes of the `prefix` bytes before the code.
    let build = |prefix: usize| {
        let length = [&[CODESIZE][..], &push_fixed(prefix + runtime.len() + arguments, 2), &[XOR, CALLVALUE, OR]];
        let mut code = [&length.concat()[..], &push_fixed(prefix - 4, 2), &[JUMPI]].concat();
        // The code and the arguments, to memory at 0.
        let copy = [&push_fixed(runtime.len() + arguments, 2)[..], &push_fixed(prefix, 2), &[PUSH0, CODECOPY]];
        code.extend(copy.concat());
        for (k, &slot) in slots.iter().enumerate() {
            let store = [&push_fixed(runtime.len() + 32 * k, 2)[..], &[MLOAD], &push_usize(slot.into()), &[SSTORE]];
            code.extend(store.concat());
        }
        code.extend([&push_fixed(runtime.len(), 2)[..], &[PUSH0, RETURN, JUMPDEST, PUSH0, PUSH0, REVERT]].concat());
        code
    };
    let prefix = build(4).len();
    [build(prefix), runtime.to_vec()].concat()
}
