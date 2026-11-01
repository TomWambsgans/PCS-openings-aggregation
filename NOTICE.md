# Notice

The Rust code under `crates/` is derived from [leanVM](https://github.com/leanEthereum/leanVM)
(Copyright (c) 2026 leanEthereum) and is licensed, like leanVM, under the MIT license
([`LICENSE-MIT`](LICENSE-MIT)) or the Apache License 2.0 ([`LICENSE-APACHE`](LICENSE-APACHE)), at your
option. Every file says where it comes from in its first lines.

## What comes from where

- **Vendored from leanVM, commit `c445e3d51a5a85031df47240595698f3b24897bf`** (branch `main`, the commit
  [leanerVM](https://github.com/Verified-zkEVM/leanerVM)'s `mumbai` branch formalizes):
  `crates/primitives`, `crates/fiat_shamir`, `crates/pcs`, `crates/parallel`, `crates/verifier`,
  `crates/bench`, copied unchanged but for a header line, except `crates/verifier/src/lib.rs`, which makes
  the WHIR verifier public, and three prover files of `crates/pcs` (`src/whir.rs`, `src/whir_ntt_ext.rs`,
  `src/ntt/additive_ntt_f64.rs`), which add ways to make the same commitments and proofs in less memory (their
  headers say so). The workspace `Cargo.toml` and `rustfmt.toml` follow leanVM's.
- **Adapted from leanVM's branch `PCS-openings-aggregation`, commit `651453c6`**:
  - `crates/quotient`: the protocol of `flock::quotient` (`doc/quotient/main.tex` there), its Cantor-basis
    domain (copied), its circuit's wiring and public rows, the Keccak-256 transcript chain, and the idea of
    opening a claim on a table whose stack holds only the lanes that can be nonzero. New here: the gate
    (one χ on bits), the Keccak-256 statement, and the tables' layouts for leanVM's WHIR as it is, including
    the hidden layouts of `crates/quotient/HIDING.md` (which adapt the padding of `flock::membership`,
    `crates/flock/membership-zk.md` on the same branch) and their exact checks (`src/hiding.rs`).
  - `crates/evm`: the bytecode generator, the recording scalar and the revm machine with `FIELD_MUL`.
  - `formal/`: the Lean proofs of `formal/quotient` (sorry-free for the original circuit), being ported to
    this circuit; each file names its source. Dependency revisions are those of
    [leanerVM](https://github.com/Verified-zkEVM/leanerVM)'s `mumbai` branch (MIT OR Apache-2.0).
- **Third-party credits carried by the vendored files** (each file names its own):
  [succinctlabs/flock](https://github.com/succinctlabs/flock) (MIT OR Apache-2.0),
  [Plonky3](https://github.com/Plonky3/Plonky3) (MIT OR Apache-2.0),
  [binius-zk/binius64](https://github.com/binius-zk/binius64) (Apache-2.0),
  [bcc-research/bolt-rs](https://github.com/bcc-research/bolt-rs) (MIT).
