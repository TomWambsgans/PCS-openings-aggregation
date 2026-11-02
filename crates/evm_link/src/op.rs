// Part of this repository; the push helpers are moved here from crates/evm/src/codegen.rs (adapted from leanVM
// (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6). MIT OR Apache-2.0; see
// NOTICE.md.
//! The opcodes the generated code uses, `PUSH` of numbers, and the stack effect of straight-line code.

pub const STOP: u8 = 0x00;
/// `FIELD_MUL`, the product in `GF(2^192)` of two words' low 192 bits (unassigned on mainnet).
pub const FIELD_MUL: u8 = 0x0c;
pub const ISZERO: u8 = 0x15;
pub const AND: u8 = 0x16;
pub const OR: u8 = 0x17;
pub const XOR: u8 = 0x18;
pub const NOT: u8 = 0x19;
pub const SHL: u8 = 0x1b;
pub const SHR: u8 = 0x1c;
pub const KECCAK256: u8 = 0x20;
pub const CALLER: u8 = 0x33;
pub const CALLVALUE: u8 = 0x34;
pub const CALLDATALOAD: u8 = 0x35;
pub const CALLDATASIZE: u8 = 0x36;
pub const CALLDATACOPY: u8 = 0x37;
pub const CODESIZE: u8 = 0x38;
pub const CODECOPY: u8 = 0x39;
pub const RETURNDATASIZE: u8 = 0x3d;
pub const RETURNDATACOPY: u8 = 0x3e;
pub const POP: u8 = 0x50;
pub const MLOAD: u8 = 0x51;
pub const MSTORE: u8 = 0x52;
pub const SLOAD: u8 = 0x54;
pub const SSTORE: u8 = 0x55;
pub const JUMPI: u8 = 0x57;
pub const GAS: u8 = 0x5a;
pub const JUMPDEST: u8 = 0x5b;
pub const PUSH0: u8 = 0x5f;
pub const PUSH20: u8 = 0x73;
pub const PUSH32: u8 = 0x7f;
pub const DUP1: u8 = 0x80;
pub const DUP2: u8 = 0x81;
pub const SWAP1: u8 = 0x90;
pub const SWAP2: u8 = 0x91;
pub const RETURN: u8 = 0xf3;
pub const DELEGATECALL: u8 = 0xf4;
pub const STATICCALL: u8 = 0xfa;
pub const REVERT: u8 = 0xfd;

/// The address of `PCS_OPEN`: the first no mainnet precompile takes (Prague's last is `0x11`).
pub const PCS_OPEN: [u8; 20] = {
    let mut address = [0; 20];
    address[19] = 0x12;
    address
};

/// The revert every failed check jumps to.
pub const REVERT_CODE: [u8; 4] = [JUMPDEST, PUSH0, PUSH0, REVERT];

/// `PUSH` of a big-endian number, in as few bytes as it takes.
pub fn push(bytes: &[u8]) -> Vec<u8> {
    let trimmed = &bytes[bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len())..];
    if trimmed.is_empty() {
        return vec![PUSH0];
    }
    let mut code = vec![PUSH0 + trimmed.len() as u8];
    code.extend_from_slice(trimmed);
    code
}

pub fn push_usize(value: usize) -> Vec<u8> {
    push(&value.to_be_bytes())
}

/// `PUSH` of an address in the code in `width` bytes whatever the address, so that code can be laid out in two
/// passes.
pub fn push_fixed(at: usize, width: usize) -> Vec<u8> {
    assert!(
        (1..=4).contains(&width) && at < 1 << (8 * width),
        "an address of {width} bytes"
    );
    let mut code = vec![PUSH0 + width as u8];
    code.extend_from_slice(&at.to_be_bytes()[8 - width..]);
    code
}

/// A field element as a word: limb 0 lowest.
pub fn word(limbs: [u64; 3]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (i, limb) in limbs.iter().enumerate() {
        bytes[24 - 8 * i..32 - 8 * i].copy_from_slice(&limb.to_be_bytes());
    }
    bytes
}

/// Words the instruction takes from the stack, and words it leaves.
pub fn arity(op: u8) -> (usize, usize) {
    match op {
        STOP | JUMPDEST => (0, 0),
        0x01..=0x07 | 0x0a | 0x0b | FIELD_MUL | 0x10..=0x14 | AND | OR | XOR | 0x1a..=0x1d | KECCAK256 => (2, 1),
        0x08 | 0x09 => (3, 1),
        ISZERO | NOT | CALLDATALOAD | MLOAD | SLOAD | 0x31 | 0x3b | 0x3f | 0x40 => (1, 1),
        0x30
        | 0x32
        | CALLER
        | CALLVALUE
        | CALLDATASIZE
        | CODESIZE
        | 0x3a
        | RETURNDATASIZE
        | 0x41..=0x48
        | 0x58
        | 0x59
        | GAS
        | PUSH0..=PUSH32 => (0, 1),
        CALLDATACOPY | CODECOPY | RETURNDATACOPY => (3, 0),
        0x3c => (4, 0),
        POP | 0x56 => (1, 0),
        MSTORE | 0x53 | SSTORE | JUMPI | RETURN | REVERT => (2, 0),
        0x80..=0x8f => {
            let n = (op - 0x7f) as usize;
            (n, n + 1)
        }
        0x90..=0x9f => {
            let n = (op - 0x8f) as usize;
            (n + 1, n + 1)
        }
        0xf1 | 0xf2 => (7, 1),
        DELEGATECALL | STATICCALL => (6, 1),
        _ => panic!("no stack effect known for opcode {op:#04x}"),
    }
}

/// How `code`, straight-line, changes the height of the stack, and the most words below its start it reads.
pub fn stack_effect(code: &[u8]) -> (isize, usize) {
    let (mut height, mut deepest) = (0isize, 0isize);
    let mut pc = 0;
    while pc < code.len() {
        let op = code[pc];
        let (pops, pushes) = arity(op);
        deepest = deepest.min(height - pops as isize);
        height += pushes as isize - pops as isize;
        pc += 1 + if (0x60..=0x7f).contains(&op) {
            (op - 0x5f) as usize
        } else {
            0
        };
    }
    (height, (-deepest) as usize)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pushes_are_as_short_as_the_number() {
        assert_eq!(push_usize(0), [PUSH0]);
        assert_eq!(push_usize(0x80), [0x60, 0x80]);
        assert_eq!(push_usize(0x1234), [0x61, 0x12, 0x34]);
        assert_eq!(push_fixed(0x12, 2), [0x61, 0x00, 0x12]);
        assert_eq!(push_fixed(0x1234, 3), [0x62, 0x00, 0x12, 0x34]);
    }

    #[test]
    fn stack_effects() {
        // `PUSH1 1 PUSH0 MSTORE`: nothing left; `DUP2 DUP2 AND`: reads two below, leaves one more.
        assert_eq!(stack_effect(&[0x60, 1, PUSH0, MSTORE]), (0, 0));
        assert_eq!(stack_effect(&[DUP2, DUP2, AND]), (1, 2));
        assert_eq!(stack_effect(&[XOR]), (-1, 2));
        assert_eq!(stack_effect(&[SWAP2]), (0, 3));
    }
}
