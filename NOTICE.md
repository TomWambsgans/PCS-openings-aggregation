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
  `src/ntt/additive_ntt_f64.rs`), which add ways to make the same commitments and proofs in less memory. The
  last of those also fixes an aliasing bug of leanVM's in-place encodes, reported in `UPSTREAM.md`. `src/whir.rs`
  and `src/whir_config.rs` also have comments corrected (no code change), reported there too. Each file's
  header says what changed. `crates/primitives/src/hash.rs` and `crates/fiat_shamir/src/lib.rs` also carry test-only trace hooks behind a
  `trace` feature that no production build enables. The workspace `Cargo.toml` and `rustfmt.toml` follow leanVM's.
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
- **`formal/Statement/`** (new here): the statement of `crates/quotient` in Lean, in the style of leanerVM's
  `Statement/` package (branch `mumbai`, commit `6175f1a0`, MIT OR Apache-2.0), on which it depends (a Lake
  dependency, not vendored) for the fields, Keccak-256, the random-permutation model, the WHIR verifier and
  prover pieces and the extractor's decoder; each file names what it takes from it.
- **Adapted from leanVM, commit `42422001`** (branch `main`, the parent of `4af2cddd` "Replace BLAKE2S by
  KECCAK-256"): `crates/leanvm_flock_gas`, the gas of that leanVM's verifier as a contract. Its `src/field.rs`,
  `src/hash.rs`, `src/merkle.rs`, `src/bytecode.rs` and `src/whir.rs` are leanVM's `crates/verifier` files, unchanged
  but for a header and the small changes each header lists; `src/lib.rs`, `src/bus.rs`, `src/layout.rs`,
  `src/flock.rs`, `src/multilinear.rs` and `src/transcript.rs` adapt the files of the same names (the same protocol,
  generic over the scalar it computes on); `src/matrices.rs` takes `matrix_values` from `deferred.rs`.
  `src/keccak_gkr.rs` adapts `crates/verifier/src/keccak.rs` of leanVM commit `4af2cddd`, for an estimate. New there:
  the Keccak-256 chain (after `crates/quotient/src/transcript.rs`), the stack's batching sumcheck, the matrices'
  reduction, the EVM recorder, code generator and machine (after `crates/evm`), and the `gas-dump` command it adds to
  a leanVM checkout (`dump/`). Each file says where it comes from in its first lines.
- **`crates/evm_link`** (new here): the compilation of a recorded graph and the assembly, moved from
  `crates/leanvm_flock_gas/src/evm/codegen.rs` and `crates/evm/src/codegen.rs` (the latter adapted from leanVM's
  branch `PCS-openings-aggregation`, commit `651453c6`), and the linker into deployable contracts. Each file says so
  in its first lines.
- **`crates/leanvm_univariate`** (new here): a univariate PIOP for leanVM `42422001`'s statement (`SPEC.md`), its
  verifier generic over the scalar and compiled to EVM code through `crates/leanvm_flock_gas`'s port of leanVM
  `42422001`'s tables, flushes, constraints and Flock verifier (each file says what it takes). Its Cantor basis is
  computed as `crates/quotient/src/domain.rs`'s (adapted from leanVM `651453c6`).
- **Built on [leanerVM](https://github.com/Verified-zkEVM/leanerVM) `mumbai`, commit `6175f1a0`** (MIT OR
  Apache-2.0): `formal/WhirBridge` states this repository's WHIR openings in mumbai's verifier language and
  proves their soundness from mumbai's theorems, importing them; `WhirBridge/Variant.lean` adapts mumbai's
  assembly of leanVM's verifier (`lean_vm/LeanVM/Protocol/EndToEnd/Sound/`, `Verifier/Cost.lean`). Each
  file says so in its header.
- **Adapted from [leanerVM](https://github.com/Verified-zkEVM/leanerVM) `mumbai`, commit `f0393df4`** (the last
  before its switch to Keccak, formalizing leanVM `3f7dc219`, whose `crates/verifier`, `crates/flock`,
  `python-verifier` and `doc` are leanVM `42422001`'s; MIT OR Apache-2.0, `Protocol/ToCompPoly/AmbientStacking.lean`
  Apache-2.0 by its own notice): `formal/Lv42`, leanVM `42422001`'s VM (leanISA with `BLAKE2S`), its
  arithmetization, the abstract M3 instance with its Flock region and the leanISA adaptor, from `lean_vm/LeanVM/`
  (`Spec/Isa.lean`, `Spec/IsaWith.lean`, `Spec/Blake2s.lean`, `Parameters/Isa.lean`, `Semantics/Lemmas.lean`,
  `Arithmetization/`, `Protocol/Spine/Instance.lean`, `Protocol/Stack.lean`, `Protocol/FixedColumns.lean`,
  `Protocol/LeanIsa.lean`, `Protocol/LeanIsa/`, `Protocol/Blake2sHash.lean`, `Protocol/Blake2sCircuit.lean`,
  `Protocol/FlockSpec.lean`, `Protocol/ToArkLib/Flock/{BlockR1CS,Circuit,Builder,Words}.lean`,
  `Protocol/ToCompPoly/{Stacking,AmbientStacking}.lean`, and the Flock constants and padding tables of
  `Spec/Verifier.lean`), renamed from `LeanVM` to `Lv42` and otherwise unchanged but for the imports of the
  BLAKE2s-era verifier and GKR bus phase, which are not ported. The field, multilinear and Clean-bridge modules
  those files import are leanerVM `6175f1a0`'s, imported as they are (`formal/EndToEnd` builds against it).
  Each file says so in its header.
- **Lean dependencies** (pinned in `formal/lakefile.toml`, at the revisions leanerVM `mumbai` uses): [CompPoly](https://github.com/Verified-zkEVM/CompPoly) `572f9973` (Apache-2.0), whose `BF64` and `BF64.Ext3` (GF(2^64) and GF(2^192) with their irreducibility proofs) `formal/Field` builds on; [ArkLib](https://github.com/Verified-zkEVM/ArkLib), [VCVio](https://github.com/dtumad/VCV-io), [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache-2.0); leanerVM `mumbai`'s `statement`, `common` and `lean_vm` packages (`formal/QuotientRpm`, `formal/Compose`, `formal/QuotientZk`, `formal/Circuit` import them). Files adapted from any of them say so in their header.
- **Third-party credits carried by the vendored files** (each file names its own):
  [succinctlabs/flock](https://github.com/succinctlabs/flock) (MIT OR Apache-2.0),
  [Plonky3](https://github.com/Plonky3/Plonky3) (MIT OR Apache-2.0),
  [binius-zk/binius64](https://github.com/binius-zk/binius64) (Apache-2.0),
  [bcc-research/bolt-rs](https://github.com/bcc-research/bolt-rs) (MIT).
