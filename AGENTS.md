# AGENTS.md

Part of this repository. Notes for whoever works on the implementation (people and agents): what the
implementation adds to the design note in [`README.md`](README.md), and where things are.

## What the implementation and its reviews add to the design note

- **No OOD answer, so claims on one commitment go together.** leanVM's WHIR, which the implementation uses unchanged,
  takes no out-of-domain sample at its first commitment: a root then binds only to a short (Johnson) list of tables
  (≤ 323 at the code's parameters, ≤ 7,908 at the ones leanerVM certifies). So every claim on one commitment must be in
  one `PCS_OPEN` call and checked by one opening (a precompile that accepted them separately would be forgeable at
  about 2^111 work), and the protocol must union-bound the challenges it draws before its claims over these lists
  (≥ 130 bits remain here).
- **The opening's Fiat–Shamir seed** has leanVM's transcript shape, the form `formal/WhirBridge` proves sound
  (`family_sound`): one hash of a prefix fixed by the verifier (label, version, the layout's hash, `log_n`, the
  rate) and the claims, a zero public digest, and the root as the proof's first two scalars, which the verifier
  checks (`opening::iv`).
- **The Fiat–Shamir states need not be in the header**, given the two points above.
- **The forward-compatibility upgrade by one Schwartz–Zippel point** needs the new commitment to bind one table: an
  OOD answer at commit time, or a root anyone recomputes from the public circuit.
- **ZK without changing the verifier**: true (`crates/quotient/HIDING.md`), but at these sizes it is not leanVM's 4×
  padding (which would exceed WHIR's 2^28 words): a random first piece per lane, 7 random lanes, and a *gadget* (a
  fixed weight on nine first-piece entries, cancelled by the values there, batched as a claim of value zero) that makes
  WHIR's lane rounds uniform for every challenge outside a set below 2^-188. The padding must cover the masks' lane:
  the unpadded version let anyone solve the masks from the opening and find the Merkle path.

## Implementation (`crates/`)

Zero-knowledge Merkle membership with Keccak-256 (depth 32: `y = H(x | 0x11..)`, path from `H(x | 0x22..)` to
`root`), reduced to four PCS claims by five field elements, as in leanVM's `flock::quotient` but on a circuit of
one χ gate on bits, its claims opened by leanVM's WHIR unchanged. See [`NOTICE.md`](NOTICE.md) for what comes
from where.

- `crates/quotient`: circuit, prover, Rust verifier (`protocol::reduce`), and the openings (`opening`), whose
  hidden layouts make the roots and the openings hide the witness ([`HIDING.md`](crates/quotient/HIDING.md)).
- `crates/evm`: the same verifier compiled to EVM bytecode, run on revm with `FIELD_MUL` (10 gas) and a mock
  `PCS_OPEN` precompile (ABI in `machine.rs`), which the contract calls once per commitment: three calls for the
  four claims. The contract's ABI (`verify` with a selector and packed arguments, 252 bytes of calldata) and its
  deployment are in `quotient.rs`: the circuit's commitment is a constructor argument kept in storage (read by one
  cold `SLOAD`), which a fixed owner may change (`setIndexRoot`). About 14,300 gas of execution at a claim price
  of 0, and 1.43 M gas to deploy.
- Vendored from leanVM `c445e3d5`: `primitives`, `fiat_shamir`, `pcs`, `parallel`, `verifier`, `bench`.
- `formal/`: the Lean 4 proofs (knowledge soundness, completeness and zero knowledge of the reduction, sorry-free;
  the layers still to do towards an end-to-end theorem are in [`formal/README.md`](formal/README.md)).
- [`STATUS.md`](STATUS.md): where things stand, the numbers, the reviews and what they changed.

```sh
cargo test --release -p quotient -p evm                               # tests, incl. contract == Rust verifier
cargo bench -p quotient --bench membership                            # prover / verifier timings and sizes
cargo test --release -p evm -- --ignored --nocapture gas_report       # gas of the contract
```
