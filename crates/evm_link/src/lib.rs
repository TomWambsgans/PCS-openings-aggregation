// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! A verifier compiled to straight-line EVM code, as one contract, or as contracts each within EIP-170's 24,576 bytes.
//!
//! This repository's contracts are not written by hand: a verifier written on a scalar type is run on a scalar that
//! records every operation, and the recorded graph is compiled (`crates/evm`, `crates/leanvm_flock_gas`). The code
//! is straight-line, the cheapest code to run, so it grows with what the verifier computes: the membership verifier
//! is 6,308 bytes, leanVM's 117 KB. This crate takes the compiled program, a list of [`Item`]s (code, and the values
//! kept in memory slots), and either assembles it into one contract ([`assemble`], as the code generators always
//! did), or **links** it into contracts that each fit ([`link`]), computing exactly the same.
//!
//! # Linking
//!
//! The program is cut at [`Item::Seam`]s, which a code generator puts between two nodes' evaluations, into runs of
//! at most [`Limits::code`] bytes each. The first run is the **driver**, the contract a verifying call is sent to: it
//! starts the program (the entry's checks, then as much of the verifier as fits), then `DELEGATECALL`s each other run,
//! a contract of its own, in order, and returns what the last returns. A run's calldata is the call's calldata, copied
//! once by the driver, followed by the **values region**: every value a run computes that a later run reads (and the
//! words left on the stack at the cut), which each run returns and the driver appends. So:
//!
//! - a value read from another run costs what a value from a slot costs: `CALLDATALOAD` at a constant offset, as
//!   `MLOAD`; a value a later run reads is kept in the returned region rather than a reused slot;
//! - every run sees the call's calldata at the offsets the program reads it at, and the driver's storage
//!   (`DELEGATECALL`): a commitment kept in storage is read as in one contract;
//! - the extra cost is one cold `DELEGATECALL` a run (2,600 gas), the copy of calldata (3 gas a word, and memory), and
//!   3 gas a word of values returned; and each run's memory is its own, which makes the memory's quadratic cost less.
//!
//! A run is a pure function of its calldata: the driver does not trust it with anything but what it computes, its
//! address is in the driver's code, and its code has no `SSTORE` (it may be called by anyone, to no effect). The
//! program's checks revert in the run that makes them, which reverts the driver.
//!
//! Each run is assembled by the same assembler as a whole program, so a program that fits is assembled into the same
//! code whichever function is called.
//!
//! # Using it from a verifier's code generator
//!
//! A code generator turns its graph into items: for each node, its operands' evaluation, its code, a
//! [`Item::Store`] if it is read again, and a [`Item::Seam`]; checks with [`Item::FailIf`]; the outputs with
//! [`Item::Output`] and [`Item::CopyConst`] and the calls of `PCS_OPEN` with [`Item::PcsOpen`], which must come after
//! the last seam (the outputs region is the last run's). [`front`] is such a generator for any graph of nodes whose
//! code works on their operands on the stack ([`front::Dag`]), which `crates/leanvm_flock_gas` uses; its
//! `evm::contract` shows the whole path, from the recorded verifier to deployed contracts and their gas.

mod assemble;
pub mod front;
mod link;
pub mod op;

pub use link::{Linked, Part, creation_code, link, link_at};

use assemble::{End, Frame, assemble_frame};

/// What an item's code computes, for a breakdown of the gas (a protocol's phase).
pub type Tag = &'static str;

/// One step of a straight-line program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    /// Instructions.
    Code(Vec<u8>),
    /// Keep the value on top of the stack in the node's memory slot too (`DUP1`, its address, `MSTORE`).
    Store(u32),
    /// Push the node's value, kept by an earlier [`Item::Store`].
    Load(u32),
    /// Pop the value into output word `k`.
    Output(usize),
    /// Copy `words` constant words, from `data` on in [`Program::data`], to output words `first` on.
    CopyConst { first: usize, words: usize, data: usize },
    /// Call `PCS_OPEN` on `words` output words from `first` on, and revert unless it attests: unless it succeeds,
    /// returning exactly the word 1.
    PcsOpen { first: usize, words: usize },
    /// Push the offset at which bytes `offset..offset + len` of the call's calldata are in this contract's: the same
    /// in one contract or the driver, elsewhere in a part, which is passed only the calldata it reads.
    Calldata { offset: usize, len: usize },
    /// Pop, and revert if it is nonzero.
    FailIf,
    /// Pop, and jump to the other entry ([`Options::other`]; the revert if there is none) if it is nonzero.
    OtherIf,
    /// The program may be cut here: no memory but the slots holds anything read later (the stack may).
    Seam,
}

/// How the program ends, once its outputs are written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ending {
    /// Return the outputs.
    Return,
    /// Return the word 1 (after its calls of `PCS_OPEN` attested).
    Attest,
}

/// A straight-line program: what a code generator hands to [`assemble`] or [`link`].
#[derive(Clone, Debug)]
pub struct Program {
    /// Each item, and what its code computes.
    pub items: Vec<(Item, Tag)>,
    /// The constants [`Item::CopyConst`] copies.
    pub data: Vec<u8>,
    /// Bytes of memory, from 0, that the code uses as scratch (hashing); the slots start there.
    pub scratch: usize,
    /// Words of the outputs region.
    pub outputs: usize,
    pub ending: Ending,
    /// The length of calldata, which the program's entry checks.
    pub calldata_len: usize,
}

impl Program {
    /// The data a run of items needs in its code: all of it if it copies any.
    fn data_of(&self, items: &[(Item, Tag)]) -> Vec<u8> {
        let copies = items.iter().any(|(item, _)| matches!(item, Item::CopyConst { .. }));
        if copies { self.data.clone() } else { Vec::new() }
    }

    /// The program's checks (and calls), each one `JUMPDEST` in a measuring build.
    pub fn checks(&self) -> usize {
        let checks = |item: &Item| matches!(item, Item::FailIf | Item::PcsOpen { .. });
        self.items.iter().filter(|(item, _)| checks(item)).count()
    }
}

/// The tags of the code the assembler adds.
#[derive(Clone, Copy, Debug)]
pub struct Tags {
    /// A measuring build's `JUMPDEST` after each check.
    pub measure: Tag,
    /// The ending, once the outputs are written.
    pub ending: Tag,
    /// The revert and the data after the code.
    pub tail: Tag,
    /// The driver's calls of the other contracts.
    pub call: Tag,
    /// Values passed between contracts: written, copied, read back onto the stack; calldata copied.
    pub pass: Tag,
}

impl Default for Tags {
    fn default() -> Self {
        Self {
            measure: "measurement only (JUMPDEST after each check, subtracted)",
            ending: "ending",
            tail: "revert, data",
            call: LINK_CALL,
            pass: LINK_PASS,
        }
    }
}

/// The default tags of what linking adds.
pub const LINK_CALL: Tag = "linking: DELEGATECALL of each part (cold), its success checked";
pub const LINK_PASS: Tag = "linking: calldata copied, values returned, kept and read back";

/// Code the other entry runs: given the revert's address, its bytes, and where in them a word is to be written at
/// deployment (an owner), if anywhere.
pub type Other<'a> = &'a dyn Fn(usize) -> (Vec<u8>, Option<usize>);

/// How code is laid out.
#[derive(Clone, Copy)]
pub struct Options<'a> {
    /// Bytes of a pushed jump destination or code offset: 2 for code under 64 KB, 3 under 16 MB.
    pub jump_width: usize,
    /// A failed check jumps to the instruction after it instead of the revert (a `JUMPDEST`), so that any calldata
    /// runs the whole code: the gas of a valid proof plus one per check.
    pub measure: bool,
    /// The other entry, placed after the code and before the revert.
    pub other: Option<Other<'a>>,
    pub tags: Tags,
}

impl Default for Options<'_> {
    fn default() -> Self {
        Self {
            jump_width: 2,
            measure: false,
            other: None,
            tags: Tags::default(),
        }
    }
}

/// A contract's code.
#[derive(Clone, Debug)]
pub struct Assembled {
    pub code: Vec<u8>,
    /// The tag of each byte.
    pub tags: Vec<Tag>,
    /// Memory it touches, in words.
    pub memory_words: usize,
    /// Where [`Options::other`]'s word to write at deployment is.
    pub other_patch: Option<usize>,
    /// The driver's: where it holds each other contract's address (the 20 bytes of a `PUSH20`), in order of call.
    pub chunk_patches: Vec<usize>,
    /// Memory slots it reuses.
    pub slots: usize,
}

/// The whole program as one contract (its seams ignored).
pub fn assemble(program: &Program, options: &Options) -> Assembled {
    let frame = Frame {
        items: &program.items,
        stack_in: Vec::new(),
        imports: Default::default(),
        pinned: Vec::new(),
        window: None,
        end: End::Program,
    };
    assemble_frame(&frame, program, options)
}
