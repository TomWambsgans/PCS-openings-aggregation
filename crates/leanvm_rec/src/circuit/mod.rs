// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! `π2`'s circuit (SPEC-REC.md §2.3–§2.6, milestone R2): the PIOP-facing description ([`spec`]), the layout framework
//! ([`layout`]), Keccak-f and Keccak-256 ([`keccak`]), the small units ([`units`]).

pub mod keccak;
pub mod layout;
pub mod spec;
pub mod units;

#[cfg(test)]
mod tests;
