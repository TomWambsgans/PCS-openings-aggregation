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
- We add a new magic precompile to the EVM: PCS_OPEN that takes as input some header and attests that it is contained in the block's list of headers.

## Simplified example for R1CS: A.z ⊙ B.z = C.z in K

- A, B, and C, all of size 2^n x 2^n are interpreted as three multilinear polynomials in 2n variables in K
- All three have hardcoded commitment in the smart contract (storage or bytecode): comA, comB, comC.
- Prover commits to z (n variables): comZ (appears in calldata)
- It seeds some Fiat-Shamir state (not necessarily the same hash function as the one used in WHIR! (this requires future security proofs))
- Runs Spartan's sumchecks (1 zerocheck, 3 linchecks)
- In the end, you get 4 opening claims: pointZ, valueZ, pointA, valueA, ...
- Call PCS_OPEN(n, comZ, pointZ, valueZ), PCS_OPEN(n, comA, pointA, valueA), ...

## Forward compatibility

- The good: If we change the PCS opening protocol (number of WHIR queries, etc) without changing the PCS commitment protocol, all good. Users simply update their offchain prover, the smart contract still works nicely, no migration needed.
- The bad: If we change the PCS commitment protocol, the hardcoded commitments (comA, comB, comC in our example) no longer work.

TLDR: this would irreversibly enshrines MUL_FIELD (tied to a specific field), and the commitment in PCS_OPEN (tied to a specific field + a specific PCS, like WHIR)

## Details

- We want a "ZKZK-friendly" PCS -> at a prover overhead of typically 2x or 4x, we can make it ZKZK without changing the verifier *at all* (WHIR is an example)
- I don't think we need to put the Fiat-Shamir states (before + after) in the header (but this requires security analysis)
