# SLH-DSA verification: the PIOP part's gas (estimate)

Part of this repository. Estimate, 2026-11-05: what the verifier of a proof of "a valid SLH-DSA signature on `M`
under `pk`" costs on the EVM, the `PCS_OPEN` claims at price 0. This is the same convention as `STATUS.md`'s gas
table: transaction gas without the 21,000 base, under EIP-7623.

## Design

- **The proof system.** The membership one (`crates/quotient`), unchanged:
  - Keccak-f[1600] as χ gates on bits;
  - a gate-and-copy argument on an additive subspace, with no sumcheck;
  - 2 roots + 5 field elements, reduced to 4 claims in 3 `PCS_OPEN` calls.
- **What the verifier depends on.** Only `log_rows` and the circuit's commitment. The SLH-DSA circuit is in the
  committed index, not in the contract.
- **The statement.** `PK.seed ‖ PK.root` (32 bytes) and a 32-byte message `M` (a digest). That is 64 bytes, the
  membership statement's four 128-bit halves.
  - The signature is the witness, so it is not in calldata. Its 7,856 bytes (128s) alone would cost 125,696 gas
    at 16 a byte.
  - SLH-DSA-SHAKE hashes with SHAKE256, which is Keccak-f, so the existing gate and wiring apply.
- **The circuit.** It handles every message, so it is sized for the worst case:
  - every WOTS+ chain at w − 1 = 15 steps, each step passed through or not by a 2-row-a-bit mux;
  - FORS and XMSS paths ordered by muxes.
  - At 113,114 rows a Keccak-f (the membership circuit's), the muxes and the signature's input bits add under
    0.5%.

| parameter set | Keccak-f (worst case) | rows | padded |
|---|---:|---:|---:|
| SLH-DSA-SHAKE-128s | 3,959 (FORS 185, 7 × 539) | 447.8 M = 2^28.74 | 2^29 |
| SLH-DSA-SHAKE-192s | 5,748 | 2^29.28 | 2^30 |
| SLH-DSA-SHAKE-256s | 8,577 | 2^29.85 | 2^30 |
| SLH-DSA-SHAKE-128f / 192f / 256f | 11,963 / 17,421 / 17,802 | 2^30.3–2^30.9 | 2^31 |
| leanSPHINCS (leanVM, Keccak) | 515 | 2^25.80 | 2^26 |

Each SHAKE256 call of SLH-DSA is one Keccak-f for `F`, `H` and `H_msg`, at every `n`. `T_l` is
`⌊(32 + (l+1)n)/136⌋ + 1`.

## Measured (revm, `FIELD_MUL` 10 gas, `PCS_OPEN` at 0, honest claims registered)

| `log_rows` | as deployed (root in storage) | root in code | root in code + inverse hint |
|---|---:|---:|---:|
| 22 (membership, check) | 18,309 (exec 14,289) | 16,071 (12,051) | 15,271 (10,879) |
| 26 | 19,393 | 17,155 | ≈ 16,360 |
| 28 | 19,936 | 17,698 | ≈ 16,910 |
| **29 (SLH-DSA-SHAKE-128s)** | 20,208 (16,188) | **17,970 (13,950)** | **≈ 17,180 (12,775)** |
| 30 (192s, 256s) | 20,480 (16,460) | 18,242 (14,222) | ≈ 17,450 |
| 31 (the f sets, extrapolated +272) | ≈ 20,750 | ≈ 18,510 | ≈ 17,720 |

- The 2^22 row reproduces `STATUS.md`. Each doubling of the circuit adds 8 `FIELD_MUL`s and about 272 gas.
- **Root in code.** A fixed SLH-DSA circuit needs no owner-settable root, so its commitment sits in the code, not
  storage: −2,238 gas (no cold `SLOAD`, no byte reversal).
- **Inverse hint.** The prover sends the one F192 inverse the verifier needs, as a sixth scalar; the verifier
  checks `x · hint = 1` instead of computing it (75 `FIELD_MUL`s). Measured −1,175 execution and +24 calldata
  bytes.
  - The measurement used a stand-in hint with 21 zero bytes. A real inverse has about none, so the table adds
    21 × 12 = 252.
  - It changes the proof format; the check is deterministic, so soundness is unchanged.
  - **Now implemented** as an opt-in mode, `quotient::protocol::Inverse::Hint` (transcript named
    `pcs-quotient-kh1`; `prove_in`, `verify_in`, `evm::quotient::contract_in`), the membership protocol unchanged.
    At 2^22, on honest proofs of each mode (`cargo test --release -p evm -- --ignored --nocapture
    gas_report_hint`), transaction gas without the base under EIP-7623, and execution:

    | 2^22 | root in storage | root in code |
    |---|---:|---:|
    | compute (membership), 252 bytes, 384 `FIELD_MUL`s | 18,309 (14,289) | 16,071 (12,051) |
    | hint, 276 bytes, 309 `FIELD_MUL`s | 17,509 (13,117) | 15,271 (10,879) |

    −1,172 execution, −800 transaction. The 2^22 row of the table above is this measurement; the others are
    still the stand-in's estimate.
- **Where the gas goes** (2^29, with the hint): 365 `FIELD_MUL`s (3,650), the transcript's Keccak, calldata
  loads, and the three calls' claim points written to memory. Calldata is 276 bytes:
  - selector 4;
  - statement 64;
  - roots 64;
  - 6 scalars of 24 bytes.

## Not in the PIOP part, and what blocks it

- **The openings.** At 2^29 rows the witness table is 2^32 words, while leanVM's WHIR takes 2^28. The
  `PCS_OPEN` precompile must take tables 16× larger, or the circuit must be split across several commitments,
  which adds claims and copy constraints between tables.
- **The prover.** About 128× the membership proof (2.2 s, 5.9 GiB on an M4 Max): minutes, and hundreds of GB.
  The lever is a denser Keccak gate (θ folded into χ, about 2× fewer rows). It costs about −272 gas a halving,
  so it matters for the prover, not for gas.
- **The leanVM recursion route** (`crates/leanvm_rec`): 44,804 for any program, so about 2.6× this.

## How it was measured

This was done in a scratch copy on h1, not kept, because the openings' layouts do not support these sizes.

1. Relax the size caps:
   - `quotient::protocol::MAX_LOG_ROWS` to 30;
   - `evm::machine::LOG_ROWS` to `..=30`;
   - `quotient::domain::BASIS` to 36.
2. Run the 2^22 honest proof's nine scalars through `verify(…, log_rows)`, which reads the same nine at every
   size.
3. Register the resulting claims in the `PCS_OPEN` mock, and call:
   - `build(log_rows, entry(true, Some(root)), true)` (root in code);
   - `contract(log_rows)` (root in storage).
4. For the hint, additionally:
   - `reduce` reads a sixth scalar and uses it in place of `inverse(…)`;
   - the prover sends a stand-in;
   - `record::MAX_ABSORBED` goes to 6.
