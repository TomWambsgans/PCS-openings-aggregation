// Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
//! The contract: [`crate::reduce`] recorded on [`record::Sym`], compiled to straight-line EVM code ([`codegen`]), run
//! on revm with `FIELD_MUL` and a mock `PCS_OPEN` ([`machine`]).

pub mod codegen;
pub mod contract;
pub mod machine;
pub mod record;
