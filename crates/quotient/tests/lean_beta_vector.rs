// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The Cantor basis of `formal/QuotientSecurity/DeployedBasis.lean` (`betaWords`): the first 24
//! words of `quotient::domain::beta()`, one for each bit of a cell's index. The Lean checks, in the
//! kernel, that they are a Cantor basis of `F64` whose vectors after the first have their low bit
//! clear, the rule `beta()` solves by, which determines the basis (`deployedBasis_unique`).

use quotient::domain::beta;

const BETA_WORDS: [u64; 24] = [
    0x0000000000000001,
    0x19c9369f278adc02,
    0xa181e7d66f5ff794,
    0x5db84357ce785d08,
    0xb973d466f5c9d0ca,
    0x521ac889831a075e,
    0x033ce8beddc8a656,
    0xb5846c4e07b91010,
    0x4087b8cbb37a32ec,
    0x00d0d3888c0ae17c,
    0xafd5ac70237f2222,
    0xe3f5af99cc3aaaf8,
    0x5a1db3b16a0b58b8,
    0x09947c54fe7ee248,
    0x0e8eaf0e0068f544,
    0xa2a113500b4b4f5a,
    0xe96f9805d6ce0bb0,
    0x53496f8b5c9edd4c,
    0xad325cb6f4ac2a9e,
    0x4a8dcf8bd7ede826,
    0xa3e9c552b6434210,
    0x5fa92ad9c9bc7ed0,
    0xa389f910cd7734de,
    0xe916f3dfca4609d8,
];

#[test]
fn beta_is_the_lean_basis() {
    for (k, &word) in BETA_WORDS.iter().enumerate() {
        assert_eq!(beta()[k].0, word, "beta()[{k}]");
    }
}
