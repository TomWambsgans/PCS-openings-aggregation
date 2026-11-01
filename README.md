# ZK-STARKS on Ethereum via PCS opening aggregations?

## Naive, simplified, idea:

- We agree on:
  - one base field K, one extension field E (example: K = F_2^64, E = F_2^192)
  - one PCS (example: WHIR in the LDR at rate 1/4)
- We add a new instruction to perform extension field multiplication in E: MUL_FIELD.
- Users can attach to each transaction a list of PCS claims.
- Each PCS claim contains:
  - header:
    - `num_variables` (1 byte)
    - commitment (32 bytes + 1 E field element) -> Merkle hash + OOD_answer (the OOD point being Fiat-Shamir derived derived from the Merkle hash)
    - opening point (`num_variables` E field elements)
    - value (1 E field element)
  - opening_proof (the PCS opening transcript, where Fiat-Shamir is seeded by the header)
- In the mempool, all the opening_proof 'disapear', and instead some STARK attests of their existence.
- Each Ethereum block contains a list of "headers", one STARK proves them all.
- We add a new magic precompile to the EVM: PCS_OPEN that takes as input header and attests that it is contained in the block's list of headers.

## Simplified example for R1CS: A.z ⊙ B.z = C.z in K

- A, B, and C, all of size 2^n x 2^n are interpreted as three multilinear polynomials in 2n variables in K
- All three have hardcoded commitment in the smart contract (storage or bytecode): comA, comB, comC.
- Prover commits to z (n variables): comZ (appears in calldata)
- It seeds some Fiat-Shamir state (not necessarily the same hash function as the one used in WHIR! (this requires future security proofs))
- Runs Spartan's sumchecks (1 zerocheck, 3 linchecks)
- In the end, you get 4 opening claims: pointZ, valueZ, pointA, valueA, ...
- Call PCS_OPEN(n, comZ, pointZ, valueZ), PCS_OPEN(n, comA, pointA, valueA), ...

## Forward compatibility

- The witnesss polynomial of the STARK is easy to change (commitment / opening algorithms are offchain).
- The difficult part is the polynomial representing the circuit whose commitment is hardcoded in a smart contract.

In 2031, when WHIR 2.0 is released, how to upgrade the PCS_OPEN precompile? -> An idea from Justin D:
- add a 'version' parameter to the arguments of the PCS_OPEN precompile. Initially it has version 1, and returns "invalid version" when called with version != 1.
- Hardfork -> version 2 is introduced. Version 1 remains available for a period of time (1 year), and is afterward deleted.
Every smart contract should:
- put the commitment of the circuit in storage (not bytecode)
- have a (trustless) function that lets any users calling it update the commitment (from v1 to v2). To prove that the new commitment is valid, we sample a random point (Fiat-Shamir) and require both PCS openings at version 1 and version 2 to agree on that point (Schwartz–Zippel).

TLDR: The PCS is relatively easy to upgrade, the only thing that cannot be upgraded is the (binary) field.

## Details

- We want a "ZKZK-friendly" PCS -> at a prover overhead of typically 2x or 4x, we can make it ZKZK without changing the verifier *at all* (WHIR is an example)
- I don't think we need to put the Fiat-Shamir states (before + after) in the header (but this requires security analysis)

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

```sh
cargo test --release -p quotient -p evm                               # tests, incl. contract == Rust verifier
cargo bench -p quotient --bench membership                            # prover / verifier timings and sizes
cargo test --release -p evm -- --ignored --nocapture gas_report       # gas of the contract
```
