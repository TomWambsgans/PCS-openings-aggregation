<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Gas of verifying a leanVM proof (Flock + BLAKE2s) with `PCS_OPEN`

**Question.** How much gas does the PIOP of a leanVM proof cost to verify in an EVM contract, for leanVM as it was
before it switched to Keccak (commit `42422001`: the VM hashes with BLAKE2s and proves it with Flock), when the PCS
openings are not paid in the contract but go to the block-level `PCS_OPEN` precompile of this repository's design
(at a price `c` per claim)? Fiat–Shamir is a Keccak-256 chain (EVM-friendly); everything else of the PIOP is
leanVM's.

**Answer, for leanVM's benchmark proof** (one leaf aggregate of 1,290 leanXMSS signatures): about **336,000 gas of
execution**, plus **27 KB of calldata**, which under EIP-7623 makes the transaction **1,077,470 gas** (without the
21,000 base), whatever `c` up to about 77,000 a claim: the calldata floor binds. Four claims, in four `PCS_OPEN`
calls. Verifying the lincheck in the contract the way leanVM's own verifier does instead (a walk of the BLAKE2s
circuit) costs 2.45 M of execution. These are the gas of straight-line code of 117 KB; as **deployable** contracts
(five of at most 24,576 bytes, "Deployable contracts") the execution is 362,228, and the transaction the same
1,077,470.

| 1,290 leanXMSS signatures | execution (`c` = 0) | claims / calls | tx EIP-7623, `c` = 0 / 2,000 / 5,000 / 20,000 | tx EIP-7976, `c` = 0 / 20,000 |
|---|---:|---:|---|---|
| **A**: lincheck terminal left to claims on `A0`, `B0` | **335,627** | 4 / 4 | **1,077,470** / 1,077,470 / 1,077,470 / 1,077,470 | 1,736,960 / 1,736,960 |
| **B**: lincheck terminal walked in the contract (leanVM's verifier) | 2,454,077 | 2 / 2 | 2,875,129 / 2,879,129 / 2,885,129 / 2,915,129 | 2,875,129 / 2,915,129 |
| this repository's Keccak membership (`STATUS.md`) | 14,289 | 4 / 3 | 18,309 / 26,309 / 38,309 / 98,309 | |

Transaction gas is without the 21,000 base, as in `STATUS.md`: EIP-7623 charges the larger of 16 (4) a nonzero
(zero) calldata byte plus execution, and 40 (10) a byte; EIP-7976 is modelled as 64 a byte, as in `crates/evm`.
Execution includes the `PCS_OPEN` calls at `c` = 0, and `c` × claims on top.

## The workload

leanVM `42422001`'s README benchmark, `cargo leanvm aggregate --xmss 1290 --log-inv-rate 1`: the aggregation guest
(`crates/rec_aggregation/guests/lean_ethereum.py`, a stacked bytecode of `2^23` words) verifying 1,290 leanXMSS
signatures in one leaf (no recursion). The proofs were made by leanVM itself (`dump/apply.sh` adds a
`leanvm gas-dump` command to a leanVM checkout; run on h1), for 32, 128, 400, 1,290 and 2,000 signatures (2,600 do not
fit WHIR's `2^28` words). For 1,290: 1,318,125 cycles; tables XOR 236,343, MUL 252,019, SET 287,373, DEREF 177,391,
JUMP 104,394, BLAKE2S 260,605 rows (log-heights 18, 18, 19, 18, 17, 18), memory `2^22`, committed `2^26.68` words
(stack of `2^27`), bus GKR depth 24, 113 claims on the stack (the ring switch's, 5 of the bus, 104 of the table
sumcheck, 3 of the public input). The proof's stream has 1,169 scalars, 1,048 of them the PIOP's (the rest WHIR's).

## What the contract does

leanVM's verifier (`crates/verifier` at `42422001`) is vendored here and made generic over the scalar it computes on
(`scalar.rs`). The contract is that code, run on a scalar that records every operation (`evm/record.rs`), compiled to
straight-line EVM code (`evm/codegen.rs`, adapted from `crates/evm`) and run on revm with `FIELD_MUL` (10 gas) and the
mock `PCS_OPEN` (`evm/machine.rs`). In order:

1. the announced sizes (checked against the shape the contract is built for) and the stack's root;
2. the bus: one batched GKR (push, pull, count; 24 layers, two levels a step), the leaf decomposition (framework
   fingerprints, selectors, padding), **the stacked bytecode's value read from the proof** (leanVM evaluates the
   `2^23`-word bytecode, impossible in a contract: it becomes a claim on the bytecode's fixed commitment);
3. the table sumcheck (19 rounds of degree 3) and its terminal identity (JUMP's constraints, the bus forms);
4. the public input's binding (the verifier evaluates the public lines itself);
5. Flock: the zerocheck (univariate skip over 128 nodes, then 26 rounds) and the lincheck (8 rounds, 64 slices);
   its terminal identity either (**A**) by `matrices.rs`: a 12-round sumcheck reduces the two matrix terms to claims on
   `A0` and `B0` (the BLAKE2s R1CS, fixed, so their commitments are too) at one point, the verifier evaluating only
   the 64-entry Lagrange and slice tables; or (**B**) by leanVM's walk of the circuit (about 48,000 products in the
   contract);
6. ring switching, as leanVM: the 64 slices become one claim on `q_flock` with the weight `Φ(eq(r, ·))`;
7. **the stack's claims batched into one** (`stack.rs`): leanVM hands them to WHIR as one weighted claim; `PCS_OPEN`
   takes evaluation claims, so the contract runs that weighted sumcheck itself (27 rounds of degree 2), the prover
   sends the stack's value at the end point, and the contract evaluates the batched weight there (every claim's eq,
   and the ring switch's 64-term weight), as WHIR's verifier does at its terminal point;
8. `PCS_OPEN`, one call per commitment, one claim each: the stack (root from calldata), the stacked bytecode, and in
   (**A**) `A0` and `B0` (roots in storage slots, one cold `SLOAD` each, as `crates/evm` keeps its circuit's).

Fiat–Shamir is a Keccak-256 chain (`transcript.rs`, like `crates/quotient/src/transcript.rs`): a challenge is one
Keccak-256 of the state and of the calldata bytes read since the last challenge, as they are in calldata (one
`CALLDATACOPY`, one `KECCAK256`); the seed hashes a name, the program's IV (leanVM's BLAKE2s digest of the R1CS and
the bytecode) and the 32-byte public input. Calldata: selector, public input, then the stream, 24 bytes a scalar
(16 a root half): leanVM's PIOP stream, plus the bytecode's value, (**A**) 26 scalars of the matrices' reduction, and
55 of the stack's batching sumcheck.

## Measured and modelled

**Measured** (revm, exactly): every execution number above and below. The contract is compiled from the recorded
verifier for each proof's shape and run on revm; every instruction's gas is read by an inspector and attributed to
the phase of the protocol that emitted it; the phases sum to the execution. The code is straight-line and every
opcode it uses has a fixed cost, so the execution gas does not depend on the proof's values: it is measured on a
stream of the right length with a build in which a failed check jumps to a `JUMPDEST` just after it (1 gas each,
25 checks + 4 calls, subtracted exactly; the test asserts the count) and a mock that attests every call. Transaction
gas is computed from the calldata's bytes by the formula above (the zero bytes of a real stream: the announced sizes;
the rest are taken pseudo-random, as a proof's are).

**Modelled**: the Keccak-VM estimate below (measured parts assembled by hand) and the alternatives in "Caveats". The
straight-line contract is installed in revm directly (it passes EIP-170's limit); the deployable one (next section)
is deployed, each contract by a transaction, and measured the same way.

## Deployable contracts

The straight-line contract is 116,951 bytes (A) or 1.13 MB (B), above EIP-170's 24,576. `crates/evm_link` links the
same compiled program into contracts of at most 24,576 bytes each (`evm::codegen::compile_deployable`): a **driver**,
the contract a verifying call is sent to, which runs the start of the program and `DELEGATECALL`s the **parts** in
order; each part is passed, in its calldata, the values earlier parts computed that it reads (and the stack's words
at its cut) and the ranges of the call's calldata it reads, returns those it computes for later parts, and runs on
the driver's storage (the fixed commitments). The cuts are between two nodes' evaluations, each part as long as fits,
but for a cut among the last twelfth of it where fewest values are live. The code computes exactly what the
straight-line code computes: checked word for word against the Rust verifier, and its calls of `PCS_OPEN` byte for
byte against the straight-line contract's (`deployable_is_the_rust_verifier`).

**Measured** (revm; every contract deployed by a transaction, EIP-170 and EIP-3860 enforced; the execution measured
on a build that cuts at the same places, a `JUMPDEST` after each check subtracted, as for the straight-line code):

| signatures | variant | contracts | code bytes | execution, straight-line | execution, deployable | added | tx EIP-7623 (−21,000), straight / deployable | deployment, all contracts (EIP-7623) |
|---:|---|---:|---:|---:|---:|---:|---|---:|
| 32 | A | 5 | 101,269 | 294,260 | 315,470 | +21,210 (7.2%) | 860,240 / 860,240 | 22,110,482 |
| 128 | A | 5 | 106,377 | 307,751 | 328,075 | +20,324 (6.6%) | 917,510 / 917,510 | 23,209,475 |
| 400 | A | 5 | 113,638 | 326,874 | 350,208 | +23,334 (7.1%) | 1,020,080 / 1,020,080 | 24,784,755 |
| **1,290** | **A** | **5** | 117,139 | **335,627** | **362,228** | **+26,601 (7.9%)** | **1,077,470 / 1,077,470** | 25,533,108 |
| 1,290 | B | 47 | 1,140,640 | 2,454,077 | 2,990,687 | +536,610 (21.9%) | 2,875,129 / 3,411,739 | 247,981,810 |
| 2,000 | A | 5 | 120,497 | 344,193 | 372,376 | +28,183 (8.2%) | 1,133,030 / 1,133,030 | 26,261,507 |

In A, EIP-7623's floor still binds: the deployable verifier's transaction costs exactly the straight-line one's. At
1,290 signatures the 26,601 are: four cold `DELEGATECALL`s and their checks (10,524), the copies (the calldata each
part reads, 3 gas a word; the values returned, 3 a word) and the memory they take in the driver and the parts
(14,949), and about 1,100 of memory expansion charged elsewhere (each part's memory is its own: the quadratic cost of
the straight-line contract's 2,135 words is shared). The five contracts: the driver (24,426 bytes, items 0..9,998:
the entry, the bus's GKR), then parts of 23,499, 23,837, 24,487 and 20,890 bytes; the values region holds at most
1,476 words, mostly the 985 values part 3 (the ring switch's weight) computes for part 4 (the eq and selector weights at
the batch's point). Deploying them all takes 25.5 M gas in five transactions (each under 5.4 M).

B's walk keeps some 800 values live at every cut, and its 47 contracts cost 536,610 more (22%).

Possible improvements, not made: a part calling the next itself when that one reads mostly its values (part 3 to 4
here: about 3,000 gas); the cuts chosen together rather than one after the other; code made shorter to fit four
contracts (one call less: 2,600).

## Breakdown (1,290 signatures, variant A)

| category | execution gas | share |
|---|---:|---:|
| ring switching: the map, its coefficients and target (69,903), its weight at the batch's point (99,389) | 169,292 | 50.4% |
| public polynomials: eq / selector weights at the batch's point (21,429), bus leaves: fingerprints, selectors, padding, index (17,174), table terminal: constraints, bus forms (7,369), public input (50) | 46,022 | 13.7% |
| transcript hashing: 296 `KECCAK256`, 36,600 bytes hashed | 33,680 | 10.0% |
| sumcheck rounds: bus GKR (16,104), stack batch (6,665), Flock zerocheck (1,581), table (1,311), matrices (495), lincheck (428) | 26,584 | 7.9% |
| calldata reads (`CALLDATALOAD`, first use) | 22,725 | 6.8% |
| Flock checks: zerocheck skip round (10,618), matrices' reduction (10,585) | 21,203 | 6.3% |
| `PCS_OPEN`: three fixed roots (cold `SLOAD`, 6,308), claims written, four calls, replies checked (3,417) | 9,725 | 2.9% |
| bus GKR layer checks | 6,198 | 1.8% |
| entry (selector, length, no value), announced sizes | 198 | 0.1% |
| **execution** | **335,627** | |
| calldata, 27,140 bytes (271 zero), at 16 / 4 a byte | 430,988 | |
| **transaction, EIP-7623** (floor: 40 × 26,869 + 10 × 271) | **1,077,470** | |

12,249 `FIELD_MUL`, 7,078 `XOR`, 2,135 words of memory, 116,951 bytes of code. Of the ring switch's ~8,000 products,
most are squarings (`x^(2^k)`, k < 64, of the 26 point coordinates and of the 64 slices), which `FIELD_MUL` pays 10
gas each.

The calldata, by what reads it (scalars of 24 bytes):

| read by | scalars | bytes |
|---|---:|---:|
| bus GKR: sumcheck rounds (4 a round) and children | 528 + 146 | 16,176 |
| table sumcheck: rounds, evaluations | 57 + 104 | 3,864 |
| Flock: skip round (64 + 2), zerocheck rounds, lincheck rounds and slices (16 + 64) | 66 + 52 + 80 | 4,752 |
| matrices' reduction (A only) | 26 | 624 |
| stack batch: rounds and value | 55 | 1,320 |
| announced sizes, root, bus leaves, bytecode value | 8 + root + 6 | 368 |
| selector, public input | | 36 |

Variant B's 2,454,077: the walk is 2,148,978 (the Flock reduction alone has 47,833 products and 111,948 additions
there); the rest as in A, less the matrices' reduction, two calls and two `SLOAD`s.

## Over the proofs

Transaction gas without the 21,000 base. The execution grows with the logarithms of the sizes (GKR depth, stack
variables); the calldata likewise (the GKR's rounds grow quadratically in its depth).

| signatures | cycles | log-heights (XOR MUL SET DEREF JUMP BLAKE2S), memory | committed | stack vars | GKR depth | variant | calldata bytes | execution (`c` = 0) | claims / calls | tx EIP-7623, `c` = 0 / 2,000 / 5,000 / 20,000 | tx EIP-7976, `c` = 0 / 20,000 |
|---:|---:|---|---:|---:|---:|---|---:|---:|---:|---|---|
| 32 | 38,209 | 13 13 14 13 12 13, 16 | 2^21.78 | 22 | 20 | A | 21,692 | 294,260 | 4 / 4 | 860,240 / 860,240 / 860,240 / 860,240 | 1,388,288 / 1,388,288 |
| 32 | | | | | | B | 21,068 | 2,416,053 | 2 / 2 | 2,750,177 / 2,754,177 / 2,760,177 / 2,790,177 | 2,750,177 / 2,790,177 |
| 128 | 135,885 | 15 15 16 15 14 15, 18 | 2^23.61 | 24 | 21 | A | 23,132 | 307,751 | 4 / 4 | 917,510 / 917,510 / 917,510 / 917,510 | 1,480,448 / 1,480,448 |
| 128 | | | | | | B | 22,508 | 2,428,257 | 2 / 2 | 2,785,349 / 2,789,349 / 2,795,349 / 2,825,349 | 2,785,349 / 2,825,349 |
| 400 | 412,695 | 17 17 17 16 15 17, 20 | 2^25.49 | 26 | 23 | A | 25,700 | 326,874 | 4 / 4 | 1,020,080 / 1,020,080 / 1,020,080 / 1,020,080 | 1,644,800 / 1,644,800 |
| 400 | | | | | | B | 25,076 | 2,446,025 | 2 / 2 | 2,844,097 / 2,848,097 / 2,854,097 / 2,884,097 | 2,844,097 / 2,884,097 |
| **1,290** | 1,318,125 | 18 18 19 18 17 18, 22 | 2^26.68 | 27 | 24 | **A** | 27,140 | **335,627** | 4 / 4 | **1,077,470** / 1,077,470 / 1,077,470 / 1,077,470 | 1,736,960 / 1,736,960 |
| 1,290 | | | | | | B | 26,516 | 2,454,077 | 2 / 2 | 2,875,129 / 2,879,129 / 2,885,129 / 2,915,129 | 2,875,129 / 2,915,129 |
| 2,000 | 2,040,429 | 19 19 19 19 18 19, 22 | 2^27.52 | 28 | 25 | A | 28,532 | 344,193 | 4 / 4 | 1,133,030 / 1,133,030 / 1,133,030 / 1,133,030 | 1,826,048 / 1,826,048 |
| 2,000 | | | | | | B | 27,908 | 2,461,921 | 2 / 2 | 2,905,173 / 2,909,173 / 2,915,173 / 2,945,173 | 2,905,173 / 2,945,173 |

In A, EIP-7623's floor binds at every size: the transaction is 40 gas a calldata byte, and execution up to about
24 gas a byte (~640,000 here) is free, so `c` does not show until 4`c` exceeds the slack (`c` ≈ 77,000 at 1,290
signatures). Per signature at 1,290: about 835 gas.

## `PCS_OPEN` claims and calls

| commitment | where the root is | claims | variables | in |
|---|---|---:|---:|---|
| the stack (`2^27` words at 1,290 signatures) | calldata (the proof's) | 1 | 27 | A, B |
| the stacked bytecode (`2^23` words) | storage slot 0 | 1 | 23 | A, B |
| `A0` (`2^28` words) | storage slot 1 | 1 | 28 | A |
| `B0` (`2^28` words) | storage slot 2 | 1 | 28 | A |

One claim per commitment, so every call holds all the claims on its commitment (the requirement of "What the
implementation and its reviews add": no OOD sample at WHIR's first commitment), and the stack's claim is at a point
drawn after the root (the batching sumcheck's), which that list-binding argument needs. Without the batching sumcheck, the stack would carry 113 claims, one of them not an evaluation (the ring
switch's weight is a sum of 64 eq's at Frobenius-twisted points: 64 claims, their values sent): about 176 claims in
one call. Modelled: the contract would save the batch's rounds and its weights at the point (~127,000 of execution),
but write some 5,000 words of `PCS_OPEN` input (~60,000), send 1.5 KB more calldata and pay 176`c`: under EIP-7623 the
floor rises (+61,000) and still binds, so it is worse at any `c`; at the standard rate alone, better only for `c`
below a few hundred gas.

## With Keccak-256 instead of BLAKE2s in the VM (estimate)

leanVM's switch (`4af2cddd`, "Replace BLAKE2S by KECCAK-256") proves Keccak by a GKR over its rounds (a state committed
every 12 rounds, 12 layers each of a 47-coefficient product polynomial, a sumcheck over the pack and segment, and 11
rounds over the 2,048 bit positions, then two openings), not by Flock. Its verifier (`crates/verifier/src/keccak.rs`)
is ported here the same way (`keccak_gkr.rs`) and measured alone; on a table of `2^18` permutations it reads 1,454
scalars, exactly the Keccak reduction of leanVM 4af2cddd's own 1,290-signature proof (made with the same dump: stream
positions 957..2411 of 2,532). Measured alone (`keccak_estimate`): **Keccak GKR 3,583,477 gas** (93,265 products,
149,834 additions, 3,295 words of memory) against **Flock 35,061** (variant A) or 2,169,457 (variant B).

Assembled by hand (modelled): execution ≈ 335,627 − 35,061 + 3,583,477 − ~6,000 (no `A0`/`B0` calls) ≈ **3.88 M**,
two claims in two calls; calldata ≈ 59,200 bytes (the 4af2cddd proof's 2,411 PIOP scalars, plus the bytecode's value
and the stack batch), so ≈ 0.94 M at 16 a byte and a floor of ≈ 2.37 M; the transaction ≈ **4.8 M** under EIP-7623
(execution-bound), against 1.08 M with Flock. Even its calldata floor alone (2.37 M, of which the GKR's 1,454
scalars are 35 KB) is twice the Flock version's whole transaction. Not counted: the KECCAK table is wider than BLAKE2S's (a few dozen more table
evaluations) and the ring switch runs on 24 coordinates instead of 26 (a few thousand gas less).

## Caveats

- **Deployability.** The straight-line code, 116,951 bytes (A) or 1.13 MB (B), is above EIP-170's 24,576 and is
  installed in revm directly; the deployable verifier ("Deployable contracts") is 5 contracts (A) for 26,601 gas more
  at 1,290 signatures, which EIP-7623's floor absorbs. Loops instead of straight-line code would make the code
  smaller but every iteration dearer (about 30 gas of counter, jump and addressing a round of a few instructions):
  linking keeps the straight-line code's per-instruction cost and pays 2,600 gas a contract.
- **One contract per shape.** Like `crates/evm`'s (one per circuit size), the contract is compiled for the announced
  sizes, which it checks. Proofs of other table heights need other code (or a dispatch, or runtime row counts in the
  padding weights, a few hundred gas).
- **No valid proof with the Keccak transcript.** leanVM's prover uses its BLAKE2s chain, so no proof exists for the
  Keccak chain, nor for the two sumchecks added here; that would need leanVM's prover changed. What is checked: the
  port is leanVM's verifier (it accepts the five real proofs with leanVM's transcript and WHIR, and rejects them
  tampered); the contract computes exactly what the Rust verifier on the Keccak chain computes (every claim and every
  checked value, word for word, on random streams, both variants); the two added reductions are complete (honest
  provers on synthetic instances: for the matrices, against leanVM's walk and `matrix_values`) and reject wrong values.
  The gas is the same for a valid proof (straight-line code, fixed-cost opcodes).
- **New pieces' soundness** is the standard sumcheck argument (degree 2: 2/|E| a round, |E| = 2^192), not formalised
  here, and the change of the PIOP's Fiat–Shamir hash from BLAKE2s to Keccak-256 is assumed harmless (random oracle).
- **The lincheck terminal in B** is leanVM's sum, re-associated so that the contract can afford its memory (both
  matrices' sides at once, blocks in the order the walk fills them): the same value (the reference verifier, which
  uses it, accepts leanVM's proofs), 64 more products; compiled in leanVM's own order it needed ~40,000 words of
  memory (quadratic in the EVM) and 5.67 M of execution.
- **`A0` and `B0` as dense `2^28`-word commitments** (variant A) are WHIR's largest tables, opened for every proof by
  the block's aggregated STARK: a builder cost the price `c` must cover. Their roots, and the bytecode's, are
  constructor-time constants kept in storage; in code instead, −6,300 gas (cold `SLOAD`s).
- **Ring switching is half of A's execution.** A `PCS_OPEN` claim type for "64 bit-slices of a committed `K`-column at
  one point" would move it (~170,000 gas, and 1,320 bytes of the batch) into the precompile.
- **The public input** is taken as given (32 bytes): for an aggregate it is leanVM's BLAKE2s digest of the signer set,
  the DA roots and the deferred claims, which a contract that reads the signers would have to recompute (BLAKE2s has
  no EVM precompile; `BLAKE2F` is BLAKE2b). A leaf's deferred claims are at the zero point (constants).

## Reproduce

```sh
cargo test --release -p leanvm_flock_gas --test evm -- --ignored --nocapture gas_report       # all tables above
cargo test --release -p leanvm_flock_gas --test evm -- --ignored --nocapture keccak_estimate  # Flock vs Keccak GKR
cargo test --release -p leanvm_flock_gas --test evm -- --ignored --nocapture deployable_report  # deployable contracts
cargo test --release -p leanvm_flock_gas                      # parity contract == Rust, reductions, stream lengths
LEANVM_DUMP=<dir> cargo test --release -p leanvm_flock_gas --test real_proofs -- --ignored --nocapture
```

The last needs leanVM's proofs: `sh crates/leanvm_flock_gas/dump/apply.sh <leanVM 42422001 checkout>`, then in it
`cargo run --release -p leanvm-cli -- --log-inv-rate 1 gas-dump --xmss 1290 --out <dir>/xmss1290` (15 GB of memory
at 1,290 signatures; the five proofs were made on h1, `/root/pcs-quotient-fv/leanvm-flock-gas/`).

## Files

| file | what | from |
|---|---|---|
| `src/lib.rs` | errors, the walk (generic), `verify_execution` (leanVM's, with WHIR), `reduce` (the contract's) | leanVM `crates/verifier/src/lib.rs` |
| `src/bus.rs`, `src/layout.rs`, `src/flock.rs`, `src/multilinear.rs` | the PIOP, generic | leanVM `crates/verifier/src/` |
| `src/field.rs`, `src/hash.rs`, `src/merkle.rs`, `src/bytecode.rs`, `src/whir.rs` | native, for the reference verifier | leanVM `crates/verifier/src/`, unchanged but headers |
| `src/transcript.rs` | leanVM's BLAKE2s transcript; the Keccak-256 chain | leanVM; `crates/quotient/src/transcript.rs` |
| `src/scalar.rs`, `src/stack.rs`, `src/matrices.rs` | the scalar trait and phases; the stack's batching sumcheck; the matrices' reduction | new (`matrix_values` from leanVM's `deferred.rs`) |
| `src/keccak_gkr.rs` | leanVM 4af2cddd's Keccak GKR verifier, generic, for the estimate | leanVM 4af2cddd `crates/verifier/src/keccak.rs` |
| `src/evm/` | recorder, the nodes' code for `crates/evm_link` (which compiles, assembles and links), revm machine (deploys, and gives each instruction's gas in every contract), contract, deployment and gas report | `crates/evm` |
| `src/shapes.rs` | the five proofs' shapes and the program's IV | new |
| `tests/real_proofs.rs`, `tests/evm.rs` | the port accepts leanVM's proofs; parity; gas | new |
| `dump/` | the `gas-dump` command added to a leanVM checkout | new |
