# SLH-DSA verification on the EVM: the circuit and the PIOP verifier

Part of this repository. This crate proves "a valid SLH-DSA signature on `M` under `pk`" with the quotient
argument of `crates/quotient`, verified on the EVM with the `PCS_OPEN` claims priced at 0. The gas convention is
`STATUS.md`'s: transaction gas without the 21,000 base, under EIP-7623.

## Status (2026-11-05): two designs, work stopped mid-way

There are two designs. The plan, measurements and per-milestone notes are in [`SPEC-FAST.md`](SPEC-FAST.md).
- **Direct** (this crate's bit circuit and its contract): the gas is measured at **≈ 17.2K**, but there is no
  feasible prover.
- **Fast, "C\*"** (`SPEC-FAST.md`): Flock proves the Keccak-f table, the quotient argument proves the lane-level
  glue, and π2 (`crates/leanvm_rec`'s wrap) verifies π1. One signature per transaction; the user accepted
  ≈ 40K gas.

| milestone (`SPEC-FAST.md` §6) | state | result |
|---|---|---|
| M1: the Keccak-f Flock block (`lv42_flock::keccak`) | **done**, on main | 4,096 Keccak-f (2^29 bits) proved in 0.13–0.19 s on h1, 0.18 s on the Mac; checked against RustCrypto's `keccak` |
| M2: the lane-level glue (`src/glue.rs`) | **done**, on main | 182,099 rows (2^18, against 2^29 for the bit circuit); 3 real signatures accepted, 21 tamperings rejected, and the same values as the bit circuit |
| M3: the structured Keccak terminal (`leanvm_flock_gas::keccak_flock`) | **done**, on main | 3,019 `E` ops (the walk: 563K), equal to the walk at every skip; whole Flock-for-Keccak verifier: 148 scalars, 47 Keccak-256 calls |
| M4: π1 (`crates/slh_fast`) | **works, stopped before its checks** | 3 real signatures prove and verify, WHIR openings included; mutations rejected; **prover 0.39 s, 1.27 GB on the Mac**; verifier 90 Keccak-f, 254 scalars, 2,806 products |
| M5: the π2 wrap and the contract | not started | gas modelled ≈ 44.6K (42–48K) |
| M6: review and tuning toward 40K | not started | |

Whole prover, modelled: π1 0.39 s (measured, Mac) plus π2 ≈ 4.5 s (measured for leanVM's π1 on h1), so
**≈ 5 s**.

### What remains to be done

1. **Close M4** (details in `SPEC-FAST.md`, "M4 status (stopped)"):
   - Run the regression list:
     `cargo test --release -p quotient -p evm -p slh_dsa -p slh_fast -p lv42_flock -p leanvm_univariate -p leanvm_flock_gas -p leanvm_rec`.
     M4 changed `leanvm_univariate`: `Column::Extra`, a `SUM_TWIST` term, and `verifier::batch` made public.
     leanVM's π1 must stay byte-identical, so also run `leanvm_univariate`'s pinned vectors and `leanvm_rec`'s
     `pi2_real` (this needs `LEANVM_TRACE`).
   - Re-check soundness. The paired batch uses 160-bit narrow challenges, which give 126.9 bits after the lists,
     below the 128 target. Take 168-bit challenges (§4.8, about +144 gas). Decide on `γ = β²` (one Keccak-f less).
   - Benchmark π1 on one machine with the π2 numbers it is compared to (h1 or the Mac), median of 3.
   - Record the three deviations from the spec in the design section. They are working code now:
     - no inverse hint: the identities at `t` are linear relations, 5 values;
     - the link sends no values;
     - the port coset is `β_19 + V_19`.
2. **M5: the π2 wrap and real gas.**
   - Compile `slh_fast::verifier::reduce::<Sym, _, Keccak>` with `leanvm_rec`'s circuit compiler, as it compiles
     π1-rec3 (`SPEC-REC.md` §1).
   - The new inputs:
     - a 64-byte public input (`PK ‖ M`) in the seed and in the compiler's statement reads;
     - the IV, binding σ's root, the parameters and the three layout words;
     - π1's 3 point claims: C1 and C2 at `r[..24]`, the setup at `r[..20]`.
   - Prove π2 on real π1 proofs, then run the contract on revm with `PCS_OPEN` attesting all 7 claims, and
     reject calldata mutations.
   - Measure the gas (target ≤ 46K) and the total prover time.
   - Expected size: π2 ≈ 13.1M of 2^24 positions (78%).
3. **M6: review and tuning.**
   - An adversarial review of π1 (the link, the K-valued glue's semantics, Flock's Keccak block) and of the wrap.
   - `review/slh_fast_params.py` for sizes, soundness and gas.
   - π2's push side toward 40–42K, using the 22% of π2 that π1 leaves free.
4. **Not planned:**
   - formal (Lean) proofs of the fast design;
   - parameter sets other than `n = 16` (wiring only);
   - several signatures per proof (π2 stays fixed, so the gas per signature falls as 1/k).
5. **Housekeeping on h1:**
   - `/root/pcs-quotient-fv/` holds `m1-keccak`, `m2-glue` and `m3-terminal` (≈ 3 GB); the work in them is
     merged, so they can be deleted.
   - Since 2026-11-05 the work runs on the Mac, at the user's request.

## What is built and tested

| piece | where | tested |
|---|---|---|
| The SLH-DSA-SHAKE verification circuit (FIPS 205, pure, empty context) | `src/lib.rs` | `tests/real.rs`: see below |
| The same verification on `GF(2^64)` lanes, with Keccak-f in a port region of 4,096 blocks (`SPEC-FAST.md`'s glue, M2): 51,027 rows plus 2^17 port rows, 2^18 in all | `src/glue.rs`, on `quotient::circuit`'s lane cells and ports | `tests/glue.rs`, `SPEC-FAST.md` appendix B |
| The inverse-hint mode of the reduction, prover, verifier and contract | `quotient::protocol::Inverse`, `evm::quotient::contract_in` | the `quotient` and `evm` suites; membership proofs and bytecode pinned unchanged |
| The reduction past 2^22 rows (domain basis of 36, so up to 2^31) | `quotient::protocol::verify_reduction_in` | `tests/contract.rs` |
| The SLH-DSA-SHAKE-128s verifier contract (2^29 rows, hint, commitment in code) | `evm::quotient::contract_in(29, Inverse::Hint, Some(root))` | `tests/contract.rs`: see below |

**The circuit, SLH-DSA-SHAKE-128s** (`cargo test --release -p slh_dsa --test real -- --ignored --nocapture`;
14 s, a 25 GB peak):
- 447,137,304 rows of 2^29 (2^28.74), 3,959 Keccak-f, 63,360 free inputs.
- The tests use RustCrypto's `slh-dsa` 0.2.0-rc.5 as the independent reference.
  - Three real signatures, under three keys, are accepted: the public words hold the statement and word 6 is
    zero.
  - 21 tamperings are rejected: a flipped bit of R, of a FORS secret, of a FORS path, of a WOTS+ chain value
    (layer 3) and of an XMSS path (layer 6), plus another message and another `PK.root`. The reference rejects
    each too.
- Also tested, at small sizes: SHAKE256 against `sha3` across block boundaries, and the digit, comparison and
  adder helpers.

**The contract** (`cargo test --release -p slh_dsa --test contract -- --nocapture`):
- It is the quotient argument's contract at 2^29 rows: 6,913 bytes of code (under EIP-170's 24,576) and 365
  `FIELD_MUL`s.
- It returns the Rust verifier's commitments and claims, and it verifies once a `PCS_OPEN` that takes the
  2^32-word tables attests them.
- It rejects today's `PCS_OPEN` (WHIR's 2^28 words), unattested claims, three flipped hint bytes and three flipped
  statement bytes.

| SLH-DSA-SHAKE-128s, 2^29 rows | calldata | execution | EIP-7623 | EIP-7976 |
|---|---:|---:|---:|---:|
| **hint, commitment in code (the contract)** | 276 B | **12,778** | **17,146–17,182** | 17,664 |
| hint, commitment in storage | 276 B | 15,016 | 19,420 | |
| compute (membership's mode), commitment in code | 252 B | 13,950 | 17,970 | |

- The range in the EIP-7623 column comes from calldata zero bytes, which vary from proof to proof. Execution is
  the same for every proof, because the code is straight-line.
- At 2^22 the same contracts reproduce `STATUS.md`: 18,309 for membership, and 15,271 with the hint and the
  commitment in code.
- **Commitment in code:** −2,238 gas, with no cold `SLOAD`. A fixed circuit needs no owner-settable root.
- **Inverse hint:** −1,172 execution. The prover sends the one F192 inverse the verifier needs, as a sixth scalar
  (+24 calldata bytes), and the verifier checks `x · hint = 1`. The check is deterministic, so soundness is
  unchanged. Its transcript is named `pcs-quotient-kh1`, so proofs do not cross modes.
- **Each doubling of the circuit** adds 8 `FIELD_MUL`s and about 272 gas.
  - At 2^30 (the 192s and 256s parameter sets) this gives about 17,450.
  - At 2^31 (the f sets) about 17,720.
  - Those sets need a public key of more than two words, which the circuit does not take yet (`n = 16` only).

## What is not real yet: the proof

The contract's gas is real. The transcripts it ran on are not:
- They are random scalars with the hint that fits them.
- The circuit's commitment is a stand-in for its wiring table's root.

The contract's code and gas depend on neither. This is what blocks a real proof:
- **The openings.** At 2^29 rows the witness table is 2^32 words, while leanVM's WHIR takes at most 2^28.
  - The `PCS_OPEN` precompile must take tables 16× larger (the mock's `PcsOpen::large()` models this; the default
    mock does not take them).
  - Or the circuit must be split across several commitments, which adds claims and copy constraints between
    tables.
- **The prover.** It is about 128× the membership proof (2.2 s and 5.9 GiB on an M4 Max at 2^22): hundreds of GB.
  h1 has 61 GB. The levers:
  - a denser Keccak arithmetization;
  - a streaming prover.
  - Each halving of the rows saves only about 272 gas; their value is in making the prover possible.
- **The leanVM recursion route** (`crates/leanvm_rec`) costs 44,804 for any program, about 2.6× this contract.

## The circuit

Public inputs:
- `PK.seed ‖ PK.root` and a 32-byte message `M`, as the quotient statement's `y` and `root` (64 bytes, four
  128-bit words).
- The signature is the witness. Its 7,856 bytes would cost 125,696 gas as calldata alone.

What it computes: `slh_verify_internal` on `M' = 0x00 ‖ 0x00 ‖ M`.
- `H_msg`, then FORS (14 trees of height 12, then `T_14`), then seven XMSS layers (35 WOTS+ chains, `T_35`, and
  a path of 9).
- Every SHAKE256 is a sponge over the existing χ-gate Keccak-f: `F`, `H` and `H_msg` take one Keccak-f each,
  `T_14` takes 3 and `T_35` takes 5.

How it fixes the wiring, for every message:
- **WOTS+ chains.** Every chain has its 15 hashes. Hash `j` is applied when `j ≥ msg[i]` and passed through
  otherwise, by a two-rows-a-bit mux. The hash's address is the constant `j`.
- **Checksum.** A 12-bit adder over the digits' complements; its nibbles are the three checksum digits.
- **Paths.** The FORS and XMSS paths are ordered by the index bits, three rows a bit.
- **Wiring only.** The digest's indices, the tree addresses and the FORS tree indices.

`PK.root` is a free input, because `H_msg` reads it before the hypertree computes the root it must equal.
- The public words bind it.
- The computed root XOR `PK.root` is public word 6, which the verifier takes to be zero
  (`quotient::circuit::Builder::finish_with_zeros`).

| parameter set | Keccak-f (worst case) | rows |
|---|---:|---:|
| SLH-DSA-SHAKE-128s | 3,959 (FORS 185, 7 × 539) | 447,137,304 = 2^28.74 (built) |
| SLH-DSA-SHAKE-192s / 256s | 5,748 / 8,577 | ≈ 2^29.3 / 2^29.9 |
| SLH-DSA-SHAKE-128f / 192f / 256f | 11,963 / 17,421 / 17,802 | ≈ 2^30.3–2^30.9 |
