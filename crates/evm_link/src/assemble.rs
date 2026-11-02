// Part of this repository; the assembly of a straight-line program (values kept in memory slots reused after their
// last read, one revert, constants copied from the code, the calls of `PCS_OPEN`) is moved here from
// crates/evm/src/codegen.rs (adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6) and crates/leanvm_flock_gas/src/evm/codegen.rs, unchanged; new here: a
// contract that runs part of a program (values from and to the other parts, the driver's calls). MIT OR Apache-2.0;
// see NOTICE.md.
//! One contract's code: a run of a program's items, with how it starts and ends.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::ops::Range;

use crate::op::*;
use crate::{Assembled, Ending, Item, Options, Program, Tag};

/// A run of a program's items as one contract's code.
pub(crate) struct Frame<'a> {
    pub items: &'a [(Item, Tag)],
    /// The values the run starts with on the stack: their offsets in calldata, the bottom one first.
    pub stack_in: Vec<usize>,
    /// The nodes another contract computed, which the run reads from calldata: their offsets there.
    pub imports: HashMap<u32, usize>,
    /// The nodes the run computes for the contracts after it: each keeps one word of the region it returns (the
    /// driver: of the values region), in this order, rather than a reused slot.
    pub pinned: Vec<u32>,
    /// Where the call's calldata the run reads is: each range of it at an offset of its own (a part's); or (`None`)
    /// where it is in the call (the driver's, or the one contract's).
    pub window: Option<Vec<(Range<usize>, usize)>>,
    pub end: End,
}

pub(crate) enum End {
    /// The program's ending: the whole program, or its last part.
    Program,
    /// Write the `stack_out` values left on the stack after the pinned ones, and return them all.
    Return { stack_out: usize },
    /// The driver's: write the stack's values after the pinned ones at the start of the values region, then call each
    /// other contract on the values so far and the calldata it reads (copied after them), keep what it returns where
    /// the call says, and return what the last returns.
    Drive { stack_out: usize, calls: Vec<Call> },
}

/// A `DELEGATECALL` of the driver.
pub(crate) struct Call {
    /// Words of the values region it is passed: as many as have been written to before it.
    pub values: usize,
    /// Words it returns (none for the last call: its return is the driver's), and the word of the values region
    /// from which the driver keeps them.
    pub returns: usize,
    pub at: usize,
    /// The ranges of the call's calldata it reads, which it is passed after the values, one after the other.
    pub ranges: Vec<Range<usize>>,
}

/// Where a frame keeps what it computes, once its slots are allocated.
struct Layout {
    /// The slot of each node kept in memory, by id.
    slot: HashMap<u32, usize>,
    slots: usize,
    /// Where the region after the slots starts: the outputs, the returned words, or the copy of calldata.
    region: usize,
}

fn allocate(frame: &Frame, program: &Program) -> Layout {
    let pinned: HashMap<u32, usize> = frame.pinned.iter().enumerate().map(|(k, &id)| (id, k)).collect();
    // A slot is free again after its node's last read.
    let mut reads: HashMap<u32, u32> = HashMap::new();
    for (item, _) in frame.items {
        if let Item::Load(id) = item
            && !frame.imports.contains_key(id)
            && !pinned.contains_key(id)
        {
            *reads.entry(*id).or_default() += 1;
        }
    }
    let mut slot = HashMap::new();
    let (mut free, mut n_slots) = (BinaryHeap::new(), 0);
    for (item, _) in frame.items {
        match item {
            Item::Store(id) if !pinned.contains_key(id) => {
                let s = free.pop().map_or_else(
                    || {
                        n_slots += 1;
                        n_slots - 1
                    },
                    |Reverse(s)| s,
                );
                slot.insert(*id, s);
            }
            Item::Load(id) if !frame.imports.contains_key(id) && !pinned.contains_key(id) => {
                assert!(slot.contains_key(id), "node {id} is read before it is kept");
                let left = reads.get_mut(id).expect("a read");
                *left -= 1;
                if *left == 0 {
                    free.push(Reverse(slot[id]));
                }
            }
            _ => {}
        }
    }
    Layout {
        slot,
        slots: n_slots,
        region: program.scratch + 32 * n_slots,
    }
}

/// The code of `frame`, and the lengths it was laid out with.
pub(crate) fn assemble_frame(frame: &Frame, program: &Program, options: &Options) -> Assembled {
    let layout = allocate(frame, program);
    let w = options.jump_width;
    // The values region of the driver.
    let values_at = layout.region;
    let pinned: HashMap<u32, usize> = frame.pinned.iter().enumerate().map(|(k, &id)| (id, k)).collect();
    let pinned_at = |k: usize| match frame.end {
        End::Drive { .. } => values_at + 32 * k,
        _ => layout.region + 32 * k,
    };
    let address = |id: u32| -> usize {
        match pinned.get(&id) {
            Some(&k) => pinned_at(k),
            None => program.scratch + 32 * layout.slot[&id],
        }
    };
    let returned = layout.region;
    let tags = &options.tags;

    // `other`: the other entry; `fail`: the revert; `data_at`: the constants.
    let lay = |other: usize, fail: usize, data_at: usize| {
        let mut code: Vec<u8> = Vec::new();
        let mut tag_of: Vec<Tag> = Vec::new();
        let mut patches = Vec::new();
        let put = |code: &mut Vec<u8>, tag_of: &mut Vec<Tag>, bytes: &[u8], tag: Tag| {
            code.extend_from_slice(bytes);
            tag_of.resize(code.len(), tag);
        };
        // A check: jump to the revert if the top of the stack is nonzero, or, measuring, to the next instruction.
        let check_at = |code: &mut Vec<u8>, tag_of: &mut Vec<Tag>, tag: Tag| {
            if options.measure {
                let next = code.len() + w + 2;
                code.extend([&push_fixed(next, w)[..], &[JUMPI]].concat());
                tag_of.resize(code.len(), tag);
                code.push(JUMPDEST);
                tag_of.resize(code.len(), tags.measure);
            } else {
                code.extend([&push_fixed(fail, w)[..], &[JUMPI]].concat());
                tag_of.resize(code.len(), tag);
            }
        };
        for &offset in &frame.stack_in {
            put(&mut code, &mut tag_of, &[&push_usize(offset)[..], &[CALLDATALOAD]].concat(), tags.pass);
        }
        for (item, tag) in frame.items {
            let tag = *tag;
            match *item {
                Item::Code(ref bytes) => put(&mut code, &mut tag_of, bytes, tag),
                Item::Store(id) => put(&mut code, &mut tag_of, &[&[DUP1][..], &push_usize(address(id)), &[MSTORE]].concat(), tag),
                Item::Load(id) => {
                    let bytes = match frame.imports.get(&id) {
                        Some(&offset) => [&push_usize(offset)[..], &[CALLDATALOAD]].concat(),
                        None => [&push_usize(address(id))[..], &[MLOAD]].concat(),
                    };
                    put(&mut code, &mut tag_of, &bytes, tag);
                }
                Item::Output(k) => put(&mut code, &mut tag_of, &[&push_usize(returned + 32 * k)[..], &[MSTORE]].concat(), tag),
                Item::Calldata { offset, len } => {
                    let at = match &frame.window {
                        None => offset,
                        Some(ranges) => {
                            let end = (offset + len).min(program.calldata_len).max(offset);
                            let (range, at) = ranges
                                .iter()
                                .find(|(range, _)| range.start <= offset && end <= range.end)
                                .expect("a calldata read within the part's ranges");
                            at + offset - range.start
                        }
                    };
                    put(&mut code, &mut tag_of, &push_usize(at), tag);
                }
                Item::CopyConst { first, words, data } => {
                    let bytes = [
                        &push_usize(32 * words)[..],
                        &push_fixed(data_at + data, w),
                        &push_usize(returned + 32 * first),
                        &[CODECOPY],
                    ];
                    put(&mut code, &mut tag_of, &bytes.concat(), tag);
                }
                // `STATICCALL(gas, PCS_OPEN, input, input length, 0, 32)`: the call attests iff it succeeds and returns
                // exactly one word, the word 1 (then at 0, the hashing scratch, free by now). A failed or reverted
                // call, an absent precompile, the word 0, or more or fewer bytes, revert.
                Item::PcsOpen { first, words } => {
                    let call = [
                        &push_usize(32)[..],
                        &[PUSH0],
                        &push_usize(32 * words),
                        &push_usize(returned + 32 * first),
                        &push(&PCS_OPEN),
                        &[GAS, STATICCALL, ISZERO, RETURNDATASIZE],
                        &push_usize(32),
                        &[XOR, OR, PUSH0, MLOAD],
                        &push_usize(1),
                        &[XOR, OR],
                    ];
                    put(&mut code, &mut tag_of, &call.concat(), tag);
                    check_at(&mut code, &mut tag_of, tag);
                }
                Item::FailIf => check_at(&mut code, &mut tag_of, tag),
                Item::OtherIf => put(&mut code, &mut tag_of, &[&push_fixed(other, w)[..], &[JUMPI]].concat(), tag),
                Item::Seam => {}
            }
        }
        match &frame.end {
            End::Program => {
                let tail = match program.ending {
                    Ending::Return => {
                        [&push_usize(32 * program.outputs)[..], &push_usize(returned), &[RETURN]].concat()
                    }
                    // The word 1, which an account without code does not return.
                    Ending::Attest => {
                        [&push_usize(1)[..], &[PUSH0, MSTORE], &push_usize(32), &[PUSH0, RETURN]].concat()
                    }
                };
                put(&mut code, &mut tag_of, &tail, tags.ending);
            }
            &End::Return { stack_out } => {
                let n = frame.pinned.len();
                for t in (0..stack_out).rev() {
                    put(&mut code, &mut tag_of, &[&push_usize(pinned_at(n + t))[..], &[MSTORE]].concat(), tags.pass);
                }
                let tail = [&push_usize(32 * (n + stack_out))[..], &push_usize(layout.region), &[RETURN]].concat();
                put(&mut code, &mut tag_of, &tail, tags.pass);
            }
            End::Drive { stack_out, calls } => {
                let n = frame.pinned.len();
                for t in (0..*stack_out).rev() {
                    put(&mut code, &mut tag_of, &[&push_usize(pinned_at(n + t))[..], &[MSTORE]].concat(), tags.pass);
                }
                for call in calls {
                    // `CALLDATACOPY(after, lo, len)`: the calldata the part reads, after the values.
                    let mut input = 32 * call.values;
                    for range in &call.ranges {
                        let copy = [
                            &push_usize(range.len())[..],
                            &push_usize(range.start),
                            &push_usize(values_at + input),
                            &[CALLDATACOPY],
                        ];
                        put(&mut code, &mut tag_of, &copy.concat(), tags.pass);
                        input += range.len();
                    }
                    // `DELEGATECALL(gas, part, values, input, 0, 0)`: the part runs on this contract's storage.
                    let head = [&[PUSH0, PUSH0][..], &push_usize(input), &push_usize(values_at), &[PUSH20]].concat();
                    put(&mut code, &mut tag_of, &head, tags.call);
                    patches.push(code.len());
                    put(&mut code, &mut tag_of, &[0; 20], tags.call);
                    put(&mut code, &mut tag_of, &[GAS, DELEGATECALL, ISZERO], tags.call);
                    check_at(&mut code, &mut tag_of, tags.call);
                    if call.returns > 0 {
                        // `RETURNDATACOPY(values + 32 values, 0, 32 returns)`.
                        let keep = [
                            &push_usize(32 * call.returns)[..],
                            &[PUSH0],
                            &push_usize(values_at + 32 * call.at),
                            &[RETURNDATACOPY],
                        ];
                        put(&mut code, &mut tag_of, &keep.concat(), tags.pass);
                    }
                }
                match program.ending {
                    // What the last part returned (the outputs), returned.
                    Ending::Return => {
                        let forward = [RETURNDATASIZE, PUSH0, PUSH0, RETURNDATACOPY, RETURNDATASIZE, PUSH0, RETURN];
                        put(&mut code, &mut tag_of, &forward, tags.ending);
                    }
                    // The word 1, if the last part returned exactly it (an account without code returns nothing,
                    // and copying 32 bytes of less halts), as it does once every call of `PCS_OPEN` attested.
                    Ending::Attest => {
                        let check = [
                            &push_usize(32)[..],
                            &[PUSH0, PUSH0, RETURNDATACOPY, RETURNDATASIZE],
                            &push_usize(32),
                            &[XOR, PUSH0, MLOAD],
                            &push_usize(1),
                            &[XOR, OR],
                        ];
                        put(&mut code, &mut tag_of, &check.concat(), tags.ending);
                        check_at(&mut code, &mut tag_of, tags.ending);
                        put(&mut code, &mut tag_of, &[&push_usize(32)[..], &[PUSH0, RETURN]].concat(), tags.ending);
                    }
                }
            }
        }
        (code, tag_of, patches)
    };
    // The other entry is the contract's that calls are sent to: the one contract, or the driver; not a part's.
    let other_entry = options.other.filter(|_| frame.window.is_none());
    let body = lay(0, 0, 0).0.len();
    let tail_len = other_entry.map_or(0, |other| other(0).0.len());
    let fail = body + tail_len;
    let other = if other_entry.is_some() { body } else { fail };
    let (mut code, mut tag_of, chunk_patches) = lay(other, fail, fail + REVERT_CODE.len());
    let mut other_patch = None;
    if let Some(make) = other_entry {
        let (tail, patch) = make(fail);
        other_patch = patch.map(|at| code.len() + at);
        code.extend(tail);
    }
    code.extend(REVERT_CODE);
    code.extend_from_slice(&program.data_of(frame.items));
    tag_of.resize(code.len(), tags.tail);
    let words = match &frame.end {
        End::Program => (returned + 32 * program.outputs) / 32,
        End::Return { stack_out } => (layout.region + 32 * (frame.pinned.len() + stack_out)) / 32,
        End::Drive { stack_out, calls } => {
            let written = frame.pinned.len() + stack_out;
            let bytes = calls
                .iter()
                .map(|call| {
                    let copied: usize = call.ranges.iter().map(|range| range.len()).sum();
                    (32 * call.values + copied).max(32 * (call.at + call.returns))
                })
                .max()
                .unwrap_or(0)
                .max(32 * written);
            (values_at + bytes).div_ceil(32)
        }
    };
    Assembled {
        code,
        tags: tag_of,
        memory_words: words,
        other_patch,
        chunk_patches,
        slots: layout.slots,
    }
}
