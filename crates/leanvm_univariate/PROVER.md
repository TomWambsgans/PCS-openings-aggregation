<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# The prover of the univariate PIOP (milestone 2)

`src/prover/` proves SPEC.md's statement on real leanVM 42422001 traces. It writes the stream that
`verifier::reduce` reads (through the contract's Keccak-256 chain) and one WHIR opening per commitment. It follows
iteration 2's final verifier (leanvm-univariate `ad49e74`; every "Prover:" item of SPEC.md §13 is done).

## Status

**Every configuration that has an opening proves end to end on the real trace** (1,000 leanXMSS signatures,
1,023,109 cycles), on the point-claim ABI: the Rust verifier accepts; every WHIR opening verifies (`C1`, `C2`, the
setup, and with Flock `A0`, `B0`); the straight contract and the deployable one (`evm_link`) accept the real
calldata with `PCS_OPEN` attesting exactly the claims the openings prove; both reject a flipped byte and any call
left unattested.

| configuration | Flock | gas, straight | gas, deployed (contracts) | calldata |
|---|---|---:|---:|---:|
| main line, `Flock(FLOCK_MAIN)` | (a′): skip 3, the ring map in tower order | 182,104 | 192,392 (3) | 7,108 B |
| π1-rec, `Flock(FLOCK_REC)` | (a′) with `FsShape::Rec` (`crates/leanvm_rec/SPEC-REC.md` §1.4) | 181,019 | 191,296 (3) | 7,108 B |
| extension B, `Flock(FLOCK_BIT_SLICE)` | (a): skip 4, the slices' combination a bit-slice claim | 90,996 | 95,955 (2) | 5,716 B |
| `Flock(FLOCK_LEANVM_SKIP)` | leanVM's skip 6, the slices sent | 251,276 | 263,557 (4) | 8,308 B |
| `Blake2s::Omitted` | none | 66,206 | 70,019 (2) | 3,508 B |

Gas is execution at a `PCS_OPEN` claim price of 0, as in SPEC §10: SPEC §13's numbers (measured there on random
streams), here on real proofs. With extension B, `C1`'s call also carries the bit-slice claim
`Σ_i μ_i ẑ(i, p) = κ`, which `PCS_OPEN` would ring-switch. WHIR cannot open it, so the test checks it on the
committed `q_flock` directly. Extension W (weighted claims) has no opening prover.

The same holds at 32 signatures, where the contract binds that shape's own `F` (`4845a2c7…`), and at review M1's tiny
executions (`prove_tiny`), where the stream is the review's independent prover's, byte for byte.

**Rust→EVM test vectors** (milestone 3): `tests/vectors/*.txt` hold the five real proofs' calldata (π1-rec's,
`main_line_rec.txt`, among them), the `PCS_OPEN`
inputs the contract calls with, the verdict and the gas, straight and deployed. `tests/evm_vectors.rs` replays them
on both builds, with no prover and no trace. Both accept at the recorded gas, call `PCS_OPEN` with exactly the
recorded inputs, and revert on 13 to 17 mutations each:

- a row count, a root, Flock's and the batch's scalars, the last byte, or the public input flipped;
- each call left unattested;
- each attested value flipped.

## How it runs

1. **Traces.** `src/prover/dump/apply.sh <leanVM 42422001 checkout>` adds `trace_dump.rs` to leanVM's `leanvm_core`.
   Any leanVM proof made with `LEANVM_TRACE_DUMP=<dir>` then writes, right after leanVM's witness build, every
   column it commits or carries, the stacked bytecode and the sizes, and Flock's prover inputs (`z`, `A z`, `B z`,
   the lincheck's packed bytes). On h1:

   ```sh
   cd /root/pcs-quotient-fv/leanvm-univariate-prover2/leanvm-42422001
   LEANVM_TRACE_DUMP=../traces/xmss1000 ./target/release/leanvm --log-inv-rate 1 gas-dump --xmss 1000 --out ../traces/proof1000
   ```

   `xmss32` (38,209 cycles) and `xmss1000` (1,023,109 cycles) are in
   `/root/pcs-quotient-fv/leanvm-univariate-prover2/traces/`.
2. **Placement** (`Trace::place`, `FlockWitness::place`; SPEC §13, F1b). leanVM puts a table's active rows first;
   the verifier wants them at the fixed cosets of the count's bits (`domain::active_positions`). Rows, and BLAKE2S's
   `q_flock` instances with them, move there; the padding rows' counters become 1 (F1: the counters are nonzero on
   every row). Every instance satisfies the R1CS alone, so the moved Flock witness is still one, and the lincheck's
   stripes are rebuilt from it. In place, only the moved rows are copied: 0.08 s, 0.28 s with Flock's buffers. A
   leanVM that placed its rows itself would not need it.
3. **Proving and checking.** Build with `RUSTFLAGS="-C target-cpu=native"`, as leanVM's own `.cargo/config.toml`
   does (without it the field is 25× slower). `/root/pcs-quotient-fv/leanvm-univariate-prover2/env.sh` has `build`
   and `run` (memory caps, a lock so that timed runs never overlap, a wait for a quiet machine).

   ```sh
   LEANVM_TRACE=<trace dir> RUSTFLAGS="-C target-cpu=native" \
     cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1
   ```

   - `proves_and_verifies_main_line`, `proves_and_verifies_ext_b`, `proves_and_verifies_with_flock`,
     `proves_and_verifies`: the proof, the quotients' degrees, every combined claim against its stack, the Rust
     verifier, the WHIR openings (`A0`, `B0` too), the straight and deployable contracts on the real calldata
     (word-for-word parity with the Rust verifier), the calls' inputs against the proven claims, and mutations.
     With `WRITE_VECTORS=<dir>` each writes its test vector.
   - `identities_hold_on_the_domain`, `unused_words_are_not_relied_on`, `setup_roots`.

   Without a trace: `prove_tiny` (review M1's tiny executions, byte for byte with its prover), `flock_skip` (the skip
   kernels), `evm_vectors` (the committed vectors). `flock_skip`'s `skip_timings_on_a_real_witness`, `opening_profile`,
   `prove_quotients` (the quotients alone on a trace, at fixed challenges) and `prove_kernels` (the transforms)
   are ignored timing tests.

## The prover, phase by phase (`src/prover/prove.rs`)

0. **The seed** is `keccak(name ‖ contract_iv(shape, program IV, roots) ‖ public input)` (F2): the contract's IV
   binds the setup roots, the shape and the five layout words. The prover checks that the contract's `F` root is the
   one it commits (`setup::f_root`; at the reference shape `SetupRoots::REFERENCE.f`). The stream starts with the six
   row counts (F1), then `C1`'s root.
1. **`C1`** (`columns.rs`, `stack.rs`): every column through the inverse additive NTT to its novel coefficients
   (`crates/quotient/src/ntt.rs`: `quotient::domain`'s transform, vectorized), then by subset sums to basis `B`
   straight into the stack (the polynomials keep their novel coefficients only); the counter inverses
   `z_T = 1/Π c_j` on every row; `q_flock` as values; leanVM's WHIR commit.
2. **Setup `F`**: the bytecode's 16 tuple slots interleaved and the addresses (`setup.rs`).
3. **The challenges** `α, β, γ`; with π1-rec (`FsShape::Rec`) `α = (c, c², c⁴, c⁸)`, squared in `E` as the verifier
   squares it, and in Flock the zerocheck's eq coordinates after the seven fixed ones are successive squares of one
   challenge (`lv42_flock::zerocheck::skip::EqPoint::Squares`, the skip module's zerocheck at any skip).
4. **Flock** (`flock.rs`, behind one call): the zerocheck, the lincheck, the 64 slices (sent but with extension B),
   then the ring map's six challenges at once (lever 4a). The matrices' reduction's three tables are kept for the
   batching sumcheck ([`flock::Pending`]).
   - At a skip of 6 the zerocheck and lincheck are leanVM's own, vendored unchanged. Below 6 they are
     `lv42_flock::zerocheck::skip` (below) and the lincheck at the row weights the skip leaves,
     `L(z) ⊗ eq(ρ_(<6-k)) ⊗ eq(x_inner)` (`lincheck::prove_padded_capture_s_hat_v_rows`).
   - leanVM's Flock buffers (2 GB) are freed after Flock.
5. **The heap** (`bus.rs`): a leaf per row, the ratio on active rows (`domain::is_active`) and 1 on padding rows, the
   fingerprints eight rows at a time (`prints.rs`); the heap's novel coefficients limb by limb.
6. **The quotients** (`quotients.rs`, on `crates/quotient/src/ntt.rs`). Each leaf quotient is sized as the verifier
   sizes it, for its height's fewest rows (`Shape::least_rows`, F1); `Q_W`'s counter term has no `Z_pad`.
   - Each numerator is evaluated on the first `T` points of an extension coset `D_M = ω_{2^M} + V_M` (outside the
     domain), `T = Σ 2^{e_j}` the verifier's count rounded up to `2^{r-2}`, in binary: blocks of points
     `ω_{s_j} + V_{e_j}`. BLAKE2S's are 20.5 sub-cosets of `V_18` (not `D_23`'s 32), XOR's, MUL's and DEREF's 8.5
     (not 16). Over the vanishing polynomial, the values give the novel coefficients (`ntt::interpolate_prefix`): with
     `R_j = Q_j + w_{e_j} R_{j+1}` (`R_0 = Q`), `w_{e_j}` is a constant `λ_j` on block `j`, whose inverse NTT is
     `U_j = Q_j + λ_j R_{j+1}`, and `λ_j + 1` on the later blocks, where `R_{j+1} = R_j + U_j`; then
     `Q_j = U_j + λ_j R_{j+1}` from the last block back.
   - The columns a numerator reads, and `R`'s three limbs, are transformed eight at a time (a batch, eight lanes a
     carry-less product; a quotient of few columns or one piece transforms each alone), one transform a piece of at
     most `2^r` points. The numerator is computed eight points at a time (`prints.rs`); `Z_act` and `Z_pad` are their
     cosets' factors' products there.
   - `Q_W` is the sum of each table's part `Σ γ^i W_i / w_r` and the public input's, each on its own points.
     BLAKE2S's 18 copies are combined by their powers first: `Σ g_j copy_j` is one E-column, and `Σ g_j ℓ_j` the
     multilinear of the combined slot table, one shifted cube a piece.
   - A numerator that does not vanish on its domain is caught on one more block of points, where its value over the
     vanishing polynomial's is checked against the interpolant's: the quotient is then reported at full degree, and
     every quotient's degree is checked below the verifier's count.
7. **`C2`**: the heap and every quotient's chunks (`Q = Q_0 + w_{e_0}(Q_1 + w_{e_1} Q_2)`, slices of the novel
   coefficients since `X_{2^e + k} = w_e X_k`), put in basis `B` limb by limb in place in the stack; then **`t`** and
   the values at `t`, in the verifier's order.
8. **`ρ`, and the combined claims** ([`replay`]): the verifier's own `reduce` in weighted mode on the stream so far.
   Weighted mode still reads the matrices' reduction after the slices; [`replay::Replay`] serves it there, an honest
   prover's at fixed challenges outside the chain, so that every other challenge is the point-claim stream's. With
   extension B, the slices' combination (weighted mode's addition to `C1`) leaves `C1`'s claim with its part of the
   value. The verifier's own checks on the stream so far are required to hold.
9. **The batching sumcheck** (`batch.rs`): the stacks' weighted sums, plus `λ^3` times the matrices' product sum
   `Σ G' L̂ ŝ` over the first `k + 6` variables, zero-extended (lever 4a; with extension B the same messages, the
   true slices'), then the stacks' values and `a`, `b`.
10. **The openings** (`opening.rs`): one point claim per commitment, leanVM's WHIR, the IV binding `PCS_OPEN`'s
    32-byte layout word (F2; version 2), whose `vars` and `placed` the verifier reads.

## The skip kernels (`crates/lv42_flock/src/zerocheck/skip.rs`)

leanVM's zerocheck prover hard-codes `K_SKIP = 6` in its round-1 kernel; its bit and table rounds were written for
rows of 8 bytes or more. The skip module proves the zerocheck for any `3 ≤ k ≤ 6`:

- **round 1**: `P(λ) = Σ_x eq(r, x)(â b̂ + ĉ)(λ, x)` on `Λ = φ_8(2^k + i)`. The seven fixed coordinates keep
  leanVM's small/medium structure (`eq(r_small, K) = C_s φ_8(X^K)`, asserted), so the 8 groups of a small run
  combine in `F_8`. At `k = 3` a word's 8 groups extend in one `gf2p8affine` (`round1_bytes`); at 4 and 5 a group's
  bytes are one affine each (`round1_words`); the 16 medium positions are one `BitFold` of 16-byte rows; the C part is
  computed on `S` and extended to `Λ`, as leanVM does;
- **bit rounds**: leanVM's pair kernels at levels `0, 2, ..` on rows of `2^(k + t)` bits, extended to rows of 1, 2,
  4 bytes (`BitFold` GFNI included); at `k = 3`, level 0 reads its products from the table of all 65,536 byte
  products (`multilinear::bit_round_pair_bytes`); the storing pass at the level whose rows are 64 or 128 bytes;
- **table rounds**: leanVM's, copied.

Tested (`tests/flock_skip.rs`):

- at `k = 6`, round 1 equals leanVM's optimized kernel's message, and the whole zerocheck writes leanVM's stream, byte
  for byte (at `m = 14, 16, 18`);
- at `k = 3..6` on honest witnesses: the verifier's checks of the zerocheck hold (the coset values, the rounds through
  `transcript::sumcheck`), and its claims are the witness's evaluations;
- every fast kernel against the generic one: `round1_bytes`, `round1_words`, `round1_folded` against
  `round1_generic`; `bit_round_pair_bytes` against `bit_round_pair`; `BitFold` at every row width against its
  definition;
- Flock end to end on 128 BLAKE2s compressions: `flock_min::verify` accepts at every skip and both ring-map orders,
  and the slices are the witness's; the placement moves the witness to the moved instances'.

On the real witness (2^32 bits), the zerocheck at skip 3 takes about 1.1 s: round 1 0.12, the level-0 pass 0.44, level
2 0.27, level 4 0.10, the storing pass 0.08, the table rounds 0.06. leanVM's at skip 6 (its own kernels): 0.45 s with
the lincheck.

## Measured (h1: AMD Ryzen 7 PRO 8700GE, 8 cores, 16 threads; `RUSTFLAGS="-C target-cpu=native"`; jemalloc)

**Reference workload**: 1,000 signatures, 1,023,109 cycles; tables of 183,266 / 195,439 / 223,851 / 137,591 / 80,937 /
202,025 rows. Each configuration in its own process (`--exact`), at leanvm-univariate-prover2-quot `2d2b862`.
Other agents' Lean jobs shared h1 (four `lean` processes at full load; the runs started at a load average of 3.6 to
3.9): the main line took 5.67, 6.22 and 7.08 s over three runs, and the table gives the middle one.

| phase | main line | extension B | main line before (`d02dcbe`) |
|---|---:|---:|---:|
| placement: the rows (and Flock's instances) | 0.09 | 0.10 | 0.10 |
| `C1` and setup: inverse NTTs to basis `B` | 0.17 | 0.32 | 0.54 |
| `C1` and setup: WHIR commits (`2^27`, `2^24`) | 0.63 | 0.70 | 0.58 |
| Flock: zerocheck, lincheck, slices | 1.25 | 1.35 | 1.09 |
| heap: leaves, products, inverse NTT (`2^23` E) | 0.15 | 0.15 | 0.31 |
| quotient: tree | 0.18 | 0.20 | 0.42 |
| quotients: leaves (8 blocks) | 1.10 | 0.87 | 4.92 |
| quotient: constraints `Q_W` | 0.27 | 0.20 | 3.04 |
| `C2`: chunks in basis `B` | 0.24 | 0.19 | 0.58 |
| `C2`: WHIR commit (`2^27`) | 0.55 | 0.47 | 0.51 |
| values at `t` | 0.02 | 0.02 | 0.02 |
| claims: the verifier's combination, the weights | 0.06 | 0.04 | 0.05 |
| batching sumcheck | 0.57 | 0.29 | 0.54 |
| openings: WHIR (3) | 0.82 | 0.70 | 0.78 |
| **total** (the trace's generation, by leanVM, apart) | **6.22** | **5.63** | **13.62** |
| peak RSS | 10.4 GB | 10.2 GB | 10.7 GB |

- The combined-claims check (a test's, 0.14 s on the main line) is not in the totals.
- "Before" is leanvm-univariate-prover2 `d02dcbe`, the batch's work without the quotients', measured just before in
  the same harness (load 3.4 at its start).
- **Proof.** The main line's stream is 7,108 bytes of calldata with the public input; the contract runs 182,104 gas
  (192,392 deployed in 3 contracts). The stream keccaks: main line `6b03217e…`, extension B `790270fb…`, leanVM's
  skip `68669d93…`, Flock omitted `04568de0…`; unchanged by the quotients' work, and the vectors' calldata,
  `PCS_OPEN` inputs and gas are the committed ones. π1-rec (`leanvm-rec-pi1`): `53c06ada…`, 4.86 s and 10.4 GB, the
  main line's `6b03217e…` and vector unchanged by it.

**leanVM 42422001's own prover, same workload, same machine** (`leanvm --tracing gas-dump --xmss 1000`, jemalloc):
2.13 s for the whole proof, peak RSS 10.1 GB. This prover's main line is about 2.9× that, at about the same memory.

**Where the time goes** (`tests/prove_kernels.rs`, `tests/prove_quotients.rs`):

- **The transforms** (`crates/quotient/src/ntt.rs`). A K-NTT of `2^18` takes 0.32 ms on one column (eight positions
  a row, AVX-512 carry-less products; `quotient::domain`'s: 1.1 ms), 1.4 ms for a batch of eight columns (one row a
  position), 1.8 ms when several batches take turns (memory-bound: 16 MB in and out); `2^23` on one column 10.6 ms
  (`quotient::domain`'s: 59 ms); an E-column is three of them, 32 ms against `quotient::domain`'s E-NTT's 150 ms.
- **The leaf quotients**, about 1 s: BLAKE2S's is 0.42 s, its 40 columns in 5 batches on 20.5 pieces of `2^18`
  points (the transforms 0.22 s, the numerator eight points at a time 0.09 s, the interpolation 0.05 s); XOR's, MUL's
  and DEREF's about 0.1 s each.
- **The tree**, 0.18 s: `T` on the first block (three `2^23` NTTs), `T(s(x))` on a coset of `V_22`, the
  interpolation (three inverse `2^23` NTTs).
- **`Q_W`**, 0.25 s: seven parts on their own points, BLAKE2S's 0.1 s (two batches on 10 pieces, the shifted cubes
  0.02 s).
- **`C1`'s polynomials** are page faults as much as transforms: each column's novel coefficients are a fresh 2 MB
  vector (with jemalloc's `thp:always`, 0.12 s instead of 0.21; heap and chunks slower, so not taken).
- The batching sumcheck's first 6 rounds are memory-bound: each reads the three stacks' words (2 GB) at about 43 ms.
  The ring switch's twisted piece adds about 60, 25 and 10 ms to rounds 0-2 (two GF(2)-linear maps per pair of
  `q_flock`'s words, by GFNI). Writing the folded stacks and weights out at `2^21` takes about 70 ms (two reads
  of `C1`'s and `C2`'s words), and the remaining folds about 40 ms.
- An opening of a `2^27` stack is about 0.3 s: leanVM's WHIR, mostly its level commits (encode and Merkle at rates
  `1/16` and below) and the lane rounds' passes over the stack.

Tried, and not kept: the lane product reduced by two more carry-less products (as the scalar product; 6.0 against
5.4 ms for `2^24` products); the leaves' pieces cut in eighths after their top three layers, each eighth finished and
read in the last-level cache (leaves 0.96 → 1.44 s); a tree whose second block is 2 points (the folds onto it are
`2^23` each, on few workers: 2^13 points cost less).

**Small trace** (32 signatures, 38,209 cycles): the contract binds that shape's own `F`; stream keccaks main line
`cf38e74e…`, extension B `9b40b065…`, leanVM's skip `f815686e…`, omitted `c68b0838…`.

## Notes for the verifier and SPEC (from building the prover)

Nothing in iteration 2's verifier blocks proving: every configuration with an opening is proven against it
unchanged. What its interface leaves to the prover, and how this one copes:

- **The combined claims are not exposed in point mode.** The prover needs each commitment's combined claim (terms,
  points, value) to write the batching sumcheck's weights; `reduce` returns them only in weighted mode, whose stream
  differs from point mode's since lever 4a (weighted mode reads the matrices' reduction after the slices). The
  prover replays point mode's stream through weighted mode with that reduction served outside the chain
  (`replay.rs`), which relies on the two modes stating the same relations in the same order. A `reduce` that
  returned its `combined` in point mode too (before `batch`) would remove the replay.
- **The setup roots**: `rust_verifier`, `record_verifier` and `parity` bind `SetupRoots::REFERENCE` whatever the
  shape. Added here, for the transcriber's item: `rust_verifier_with`, `record_verifier_with`, `parity_with`, which
  take the shape's roots; the old ones call them with `REFERENCE`. The prover's tests verify every shape against the
  contract that binds its own `F`.
- `contract_iv` and the layout words come from `layouts(shape)`, which validates the shape without Flock: a Flock shape
  with BLAKE2S below height 7 still gets an IV. Harmless, since `reduce` then rejects the shape before it reads
  anything; left as it is. The shape's bytes are hashed twice into the IV (directly and in every layout word):
  harmless, left.
- **Extension B's bit-slice claim** has no WHIR opening: `PCS_OPEN` must ring-switch it. The test checks it on the
  committed `q_flock`; the vectors' `C1` call carries it.
- **`A0`, `B0` are opened per proof** (two `2^28` openings, about 1.7 s each with leanVM's WHIR, a fifth of the
  words nonzero). They are fixed: a prover that kept their L0 codewords (8 GB, or on disk) would skip each opening's
  re-encode of its queried rows (0.55 s of it).
