<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# SLH-DSA-SHAKE-128s with a fast prover, verified for about 40–45K gas: design

**Status: design, not built.** Every number is tagged **[M]** (measured: on h1, by this repository's tests or by the
probes in appendix A) or **[E]** (modelled from measured numbers; the derivation is given). The gas convention is
`STATUS.md`'s: EIP-7623 transaction gas without the 21,000 base, `PCS_OPEN` claims at price 0, one signature a
transaction.

**The statement** is `src/lib.rs`'s, unchanged: public `PK.seed ‖ PK.root` (32 B) and a 32-byte `M`; secret the
7,856-byte signature; `slh_verify_internal(M', SIG, PK)` with `M' = 0x00 ‖ 0x00 ‖ M`; worst-case wiring (every
WOTS+ chain has its 15 hashes, muxed by the digits; paths ordered by the index bits): **3,959 Keccak-f**.

## 0. Recommendation (in 10 lines)

1. **π1 = "C\*": the quotient argument of `crates/quotient` proves the glue, Flock proves the Keccak-f table, and
   a polynomial identity links them.** π2 = `crates/leanvm_rec`'s D16v wrap, compiled from π1's recorded verifier.
2. The glue is a quotient circuit whose cells are **`K = GF(2^64)` lanes, not bits**: the same gate `V = X + C + Y·C`
   is a lane mux when `Y` is a bit, an XOR when `Y = 0`, a copy when `Y = 1`. Bits are cells only where SLH-DSA reads
   bits (digest, digits, checksum, index bits: 1,280 bits). The glue is **≈ 2^18 rows** (today: 2^29).
3. Keccak-f is one Flock block (`k_log = 17`, `C = I`, every round's state materialised): 4,096 blocks, `2^29` bits,
   `2^23` packed words. Its 25 input and 25 output lanes are K-words of `q_flock`, laid out as the glue's **port
   quads**, so W's port coset and `q_flock`'s port region hold the same 2^19 words.
4. The link is **one identity at the quotient's `t`**, `W_R − ℓ_q = Q_link · Z`, `ℓ_q` the composition of `q_flock`'s
   port values (leanvm_univariate's `copy_j − ℓ_j` technique): no extra sumcheck, two values.
5. Commitments: C1 = `q_flock ‖ W ‖ Q_link` (2^24), C2 = the quotient table (2^24), setup (σ). One batching sumcheck
   (π1-rec3's narrow pairs) leaves **3 point claims at one point** (12 challenges + 3 values), as π1-rec3 does.
6. π1's verifier: **≈ 91 Keccak-f** (Flock ≈ 59 of them [M-based]), ≈ 15–20K `E` ops → π2 ≈ 13.2M of 2^24 positions
   (79%; π1-rec3 needs 94.9% today) [E].
7. **Prover ≈ 6 s on h1, ≈ 10 GB** [E from M]: π1 ≈ 1.4 s (Flock 0.18 s, quotient 0.45 s, rest commits/batch/openings),
   π2 3.2 s + 1.3 s openings (measured at 2^24). Today's circuit needs ≈ 750 GB.
8. **Gas ≈ 44.6K (42–48K)** [E from leanvm_rec's measured 44,804]: ≈ 964 B of calldata, ≈ 29.8K execution. ≈ 40–42K
   needs π2's push side tuned with the 21% slack π1 leaves (§4.7); the calldata floor is 38.6K.
9. Rejected: Keccak-GKR (π1's verifier ≥ 300 Keccak-f [M]: π2 does not fit WHIR's 2^28), bit-level hybrid (I/O bits
   ×64), no wrap (Flock on chain ≥ 92K at the floor), π2 = the quotient gate (fits only ≈ 37 Keccak-f).
10. Plan: 6 milestones, ≈ 17–20 agent-days; **M1 proves 4,096 Keccak-f with Flock on h1, expected ≤ 0.3 s** (§6).

## 1. Measured anchors

| # | what | number | source |
|---|---|---|---|
| a | Flock prover (`leanvm_univariate::prover::flock::prove`, skip 3 / 6, `FsShape::Rec`, slices sent), synthetic BLAKE2s blocks | **2^28 bits: 0.094 / 0.063 s; 2^30 bits: 0.328 / 0.198 s**; witness 0.01 / 0.04 s | [M] h1, probe `flock_scale.rs` |
| b | Flock verifier, π1-rec3 shape (skip 3, slices sent, walked terminal, eq point by squares) | log_n 28 / 29 / 30: 43 / 44 / 45 Keccak-256 calls, 140 / 142 / 144 scalars, ≈ 56 Keccak-f (the 64 slices take 12 blocks, the skip's 8 values 2), 48,163 `FIELD_MUL` (≈ 45K of them BLAKE2s's walk) | [M] probe `verifier_fragments.rs` |
| c | Keccak GKR verifier (leanVM 4af2cddd, `leanvm_flock_gas::keccak_gkr`), 2^12 permutations | depth 12: 287 calls, 1,347 scalars (32 KB), 92,905 `FIELD_MUL`, 3.56M gas; depth 6: 164 calls, 757 scalars, 57,183; depth 24: 519 calls, 2,495 scalars | [M] probe |
| d | Keccak GKR prover (leanVM checkout `5ae9d4299`, `keccak_gkr` `hash_batch`) | 4,096 perms: **66 ms** (depth 12), **40 ms** (depth 6); 8,192: 167 ms; ± 35–110% (shared machine) | [M] h1 |
| e | `crates/quotient` membership prover, 2^22 rows | reduction 5.27 s, openings 1.49 s, **6.78 s**, 5.81 GiB (2.2 s on an M4 Max, `STATUS.md`) | [M] h1 |
| f | π2 (D16v) at N = 2^24 | prove **3.2 s**, open **1.3 s**, 9.5 GB; a Keccak-f = 130,736 positions; π1-rec3's 107 Keccak-f = 15.93M positions (94.9%) | [M] `leanvm_rec/PI2.md`, `SPEC-REC.md` §12 |
| g | π2's contract (π1-rec3) | **44,804** gas: 980 B (59 zero), 29,832 execution (push side 14.8K) | [M] `leanvm_rec/README.md` |
| h | π1 phases at 2^27 stacks (leanvm_univariate) | WHIR commits 2^27 + 2^24: 0.63 s; C2 (2^27) 0.55 s; batch 0.57 s; 3 openings 0.82 s | [M] `leanvm_univariate/PROVER.md` |
| i | the quotient gate's capacity | 2^22 rows (Q = 63 words a row = 2^27.98) ≈ 37 Keccak-f | [M] `SPEC-REC.md` §2.1 |
| j | Flock on chain (SPEC-FLOCK) | floor `2(log_n + 14) + 4` = 96 scalars ≈ 92K at 40 B; ABI variant (a′) skip 3: 87,516 execution, 168 scalars | [M] |

## 2. Why every option wraps

- **The hash argument cannot be verified in the contract for ~40K.** Flock's two sumchecks read ≥ 96 scalars [j]:
  92K at EIP-7623's floor before anything else. Keccak GKR is 3.56M [c]. The current circuit's contract (17.2K)
  has no feasible prover.
- **π2 = the quotient gate (a ~17K contract) cannot wrap a sumcheck π1.** It fits ≈ 37 Keccak-f in π1's transcript
  [i]; Flock alone needs ≈ 56–59 [b].
- **So the contract is π2's (D16v): ≈ 45K for any π1 whose verifier fits 2^24 positions**, that is ≤ ≈ 110 Keccak-f
  in its transcript plus ≈ 2M positions of `E` arithmetic and stream [f]. π2's verifier cost hardly depends on π1;
  the calldata does through π1's claims (§4.7). The designs differ in prover time, fit and risk.

## 3. Architectures compared

Prover times are h1 (8 cores, 16 threads), π1 + π2. π2 is 4.5 s [f] whenever it fits 2^24.

| | A: Flock-Keccak + univariate glue tables + heap bus (leanvm_univariate template) | B: Keccak-GKR + glue | C: bit-level hybrid (as posed) | **C\*: lane-level hybrid (recommended)** | E: all in Flock (glue in the blocks, block-shift lincheck) | F: Flock-Keccak only; glue inside π2 |
|---|---|---|---|---|---|---|
| π1 commitments | C1 `q_flock` 2^23 + tables ≈ 2^21; C2 heap + leaf quotients ≈ 2^23 | GKR states 2^17.6 + glue | `q_flock` 2^23; W 2^23.3 (2^21 rows, live I/O lanes only); Q 2^27 | C1 2^24 (`q_flock` 2^23, W 2^20.3, Q_link 2^22.1); C2 2^24 (Q, 2^18 rows); setup σ 2^20 | `q_flock` ≈ 2^24 + setup selectors | `q_flock` 2^23 |
| π1 prover | 1.5–2.5 s [E, h] | **0.04–0.07 s** [M, d] + glue 0.5 s | 3.5–4 s [E, e] | **≈ 1.4 s** [E, §4.9] | 0.3–0.5 s [E, a] | 0.5 s [E] |
| π1 verifier: Keccak-f / scalars / `E` ops | ≈ 100 / ≈ 300 / ≈ 20K | **≥ 300** / 757–1,347 / 57–93K [M, c] | ≈ 95 / ≈ 200 / ≈ 25K (+ a second ring switch) | **≈ 91 / ≈ 190 / 15–20K** | ≈ 75 / ≈ 170 / ≈ 15K | ≈ 70 / ≈ 160 / ≈ 15K |
| π2 positions (of 2^24) | ≈ 14.5M (86%) | ≥ 43M: **does not fit** (2^26 → Q ≥ 2^29.9 > WHIR's 2^28) | ≈ 14M | **≈ 13.2M (79%)** | ≈ 11M | ≈ 10M + glue ≈ 0.5M |
| gas (EIP-7623, c = 0) | ≈ 45K | — (π3 chain ≈ 53K+) | ≈ 45K | **≈ 44.6K; 40–42K with π2 tuning** | ≈ 45K | ≈ 46K (an extra link claim on π1's C1) |
| total prover | 6–7 s | ≥ 18 s and ≈ 38 GB at a 2^26 π2, or π3 | 8–9 s | **≈ 6 s, ≈ 10 GB** | ≈ 5 s | ≈ 5 s |
| new design | SLH tables, heap bus for fixed wiring, 84-value-style verifier | GKR in π2 does not fit | ring switch for the link, constant-lane pins in Flock (non-uniform) | lane cells in the quotient Builder, Keccak block R1CS, port quads, `Q_link` | **new lincheck** (block shift, preprocessed selectors): new soundness | π2's statement and compiler change (external witness region, link claim) |
| risk | medium | prohibitive | high (sizes) | **medium** | high | high (touches the most-reviewed layer) |

Notes on the table:
- **A** is leanvm_univariate's architecture with BLAKE2s replaced by Keccak and the VM tables by SLH tables. It works,
  but the glue needs hand-designed tables, a heap and ~40–80 values at `t`; C\* gets a general circuit for free from
  `quotient::circuit::Builder` and a 6-scalar verifier.
- **B**: the fastest Keccak prover [d], but its verifier is ≥ 164 Keccak-256 calls and 18–32 KB of stream [c]: ≥ 300
  Keccak-f in π1, 3× π2's capacity. Not reusable without a third layer (SPEC-REC §6 models the chain π1 → π2 → π3
  at +8K gas over a two-layer wrap).
- **C as posed** (bits as cells, each call's I/O bits an aligned subcube): the I/O is 4,096 × 3,200 = 13.1M bit
  cells (2^23 rows with the glue, Q 2^29 > 2^28); restricted to live lanes it fits (2^21 rows) but the link between
  bit cells and `q_flock`'s packed words needs a ring switch (64 slices a point), and the constant lanes need
  non-uniform pins on Flock's side. Also, W is committed as univariate (novel-basis) **coefficients**, so an "aligned
  subcube MLE claim" on W is not a point claim on its values: the link must be a univariate identity anyway (§4.5).
  C\* is C at lane granularity, which removes all three problems.
- **Wrap or not, and which parts** (asked under C): the quotient part alone would cost the contract ≈ 12K, but Flock's
  ≥ 92K floor keeps the whole π1 on chain at ≈ 240K [E: quotient 12K + Flock (a′) 87.5K + batch 7K execution, ≈ 6 KB
  at 40 B]. Wrapping only Flock leaves 12K + 45K on chain: worse than wrapping everything (≈ 45K). **Wrap all of π1.**

## 4. The recommended design, C\*

### 4.1 π1's protocol

Transcript: leanvm_flock_gas's `KeccakChannel` (Keccak-256 chain), so π2's compiler records it as it records π1-rec3.

1. Seed = `keccak(name ‖ IV ‖ PK.seed ‖ PK.root ‖ M)` (IV binds the setup roots and the shape).
2. **C1** = stack of `q_flock` (Flock's packed witness, 2^23 words), `W` (the glue's cells, the quotient's witness
   table, 2^18 rows) and `Q_link` (§4.5, in chunks 2^22 + 2^19). Root → `α, β` (the quotient's copy challenges).
3. **Flock** on `q_flock`: zerocheck (skip 3, eq point by squares), lincheck (11 rounds), 64 slices, ring map
   `f_0..f_5` (π1-rec3's `Slices::TowerWalk` with the Keccak terminal of §4.2 in place of BLAKE2s's walk).
4. **C2** = the quotient table (`h` and `q`, `crates/quotient`'s layout, non-hiding). Root → `t`.
5. Values at `t`: the quotient's 5 + inverse hint (`Inverse::Hint`), and the link's 2 (`W_R(t)`, `Q_link(t)`).
   → `ρ` (combines each commitment's relations).
6. `λ`, then the **batching sumcheck** of π1-rec3 (`FsShape::Rec3`: two variables a round, narrow challenges) over
   the three 2^24 stacks: 12 pairs, then the three values `C1(r)`, `C2(r)`, `S(r)`.
7. `PCS_OPEN`: 3 point claims at one point, 3 calls (machine.rs ABI).

### 4.2 Keccak-f as a Flock block

Flock (`crates/lv42_flock`) proves `A z ∘ B z = z` (`C = I`, baked into zerocheck and lincheck) per block, the blocks
batched; every z slot is the output of one row (constant wire, free input, lin-id `(form)·1`, product).

- **Rows of round j** (24 rounds): `b = πρθ(A_{j-1})` is linear (each bit 11 bits of `A_{j-1}`).
  - Product rows: `t_j[X,Y,Z] = (1 + b[X+1]) · b[X+2]`.
  - Lin-id rows: `A_j = (b[X] + t_j + RC_j)·1`.
  - With `C = I`, `A_j` must be its own slot. Otherwise the cascade makes `A_j`'s forms dense and the verifier's
    terminal unaffordable (§4.2, terminal).
  - So a round is 3,200 slots.
- **Block layout** (`k_log = 17`): the port region (32 quads × 4 words = 8,192 bits, §4.5), then `t_0..t_23` and
  `A_0..A_22` (75,200 bits), the constant wire; `A_{-1}` and `A_23` sit in the port quads. 83,393 of 131,072 bits
  (64%); padding slots are forced to 0 by empty rows (`PaddingSpec`). 4,096 blocks (3,959 used, the rest
  Keccak-f(0)): **log_n = 29, 2^23 K-words**.
- **Why not `k_log = 16`**: 40,000 bits would fit if `C` were a general matrix (`c = A_j + b[X] + RC` with 12
  nonzeros). That needs lv42_flock's zerocheck and lincheck to carry `Cz` (a third fold, `v_c` sent): a stretch
  optimisation (half the bits, −0.1 s), not on the critical path.
- **The prover's lincheck fold** (`LincheckCircuit::fold_alpha_batched`): a backward walk of the block circuit,
  ≈ 2.5M nonzeros, once (the z fold over blocks comes first). ≈ 20 ms [E].
- **The verifier's terminal**: `Σ_rows eq(r, row) (A + αB)(row, (ρ, i))` for the 64 packing positions `i`. A walk
  of the circuit would cost ≈ 1.3M additions, about 10M of π2's positions, so do not walk. Use the structure:
  - rows and columns factor into (round, kind, lane, z); the 64 packing bits are Keccak's `z`;
  - the round factor is a shift MLE (`O(5)`);
  - the lane factor is `eq` over 25 lanes;
  - each ρ rotation is a cyclic shift of the 64-entry `eq(r_z, ·)` table;
  - group the (lane, lane′) pairs by rotation offset (≤ 50 distinct, θ's `z − 1` included), then do 64 multiply-adds
    per offset;
  - rounds 0 and 23 (the port quads) and the ι constants are corrections.
  
  Estimate: ≈ 10K `E` ops [E]; built (M3): 3,019 [M], equal to the walk (M3 notes, after §4.5).

### 4.3 The glue circuit (quotient Builder over K)

The gate `V = X + C + Y·C` is a K-identity. Its existing proof machinery does not depend on cells being bits; only
the circuit semantics do. Cell kinds:

- **lane cells** (K-words), whose bit `i` ↔ `x^i` (Flock's packing, `q_flock(u) = Σ z(i,u) x^i`);
- **bit cells**, Boolean by the existing free-input self-loop (`v = v + v + v² ⇒ v² = v`);
- **free-K rows**: `X` = own `V`, `Y = 1`, `C` anything, so `V = X` with any value. This is the signature's 982
  lanes and every Keccak output.

Gadgets (rows):

| gadget | rows | count | rows total [E] |
|---|---|---:|---:|
| port quads (§4.5) | 1 a quad (an input and an output lane) | 4,096 × 32 | 131,072 |
| WOTS step mux `tmp + s·(F(tmp) + tmp)`, 2 lanes, `Y = ¬s` | 5 | 3,675 | 18,375 |
| `at_most(digit, j)` → `s` | ≤ 4 | 3,675 | 14,700 |
| checksum (12-bit adder of complements) | ≈ 2,048 a layer | 7 | 14,336 |
| packed ADRS lanes from bits (`acc + b·x^i`, NOT + gate) | ≈ 64 | 268 | 17,200 |
| unpacking (digest 256, 7 layer messages 896, final root 128 bits) | 3 a bit | 1,280 | 3,840 |
| auth-path swap (2 lanes), `Y = ¬bit` | 7 | 231 | 1,617 |
| constant lanes (XOR of powers `x^i`) and `x^i` | ≈ 4 | ≈ 540 | 2,200 |
| sponge continuation XORs (rate lanes) | 1 | 30 × 17 | 510 |
| public bits → seed, root, `M` lanes; root comparison; public rows; signature | | | ≈ 3,000 |
| **total** | | | **≈ 207K ≤ 2^18 (79%)** |

The only K-constant needed, `x`, comes from a constant port quad (Flock pins the word's bit 1 by one lin-id row);
`0` and `1` are the quotient's existing anchors.

### 4.4 How the SLH-DSA dataflow is enforced

| element | where | how |
|---|---|---|
| Keccak-f correctness | Flock | each block's R1CS; padding blocks are Keccak-f(0) |
| a call's input / output lanes | link (§4.5) | port quads: W's port cells = `q_flock`'s port words |
| hash chaining (F chain, H path, sponge blocks) | quotient σ | the consumer's input-port `C` cell is wired to the producer's output `V` (through the mux or swap rows) |
| WOTS chain muxes | glue | lane mux with `s = at_most(digit_i, j)`; the digits are `base_2b` wiring of the unpacked layer message; the checksum is the 12-bit adder, its nibbles wiring; hash index `j` and chain `i` are a constant ADRS lane 5 (525 constants) |
| auth-path ordering | glue | swap rows `l = node + bit·(node + auth)`, `r = l + node + auth`; the bit is a digest bit (layer 0, FORS) or a tree bit (layers > 0): wiring |
| ADRS fields | glue | lane 2 constant per layer; lane 3 = `tree_L` (54 − 9L digest bits, big-endian bytes) packed; lane 4 = type ‖ keypair (leaf bits) packed; lane 5 constant (WOTS), `height ‖ leaf >> (k+1)` (TREE) or `t ‖ (i·2^12 + idx_i) >> t` (FORS) packed: 268 packed lanes in all |
| T_35 (5 blocks) / T_14 (3 blocks) | glue + σ | 608 / 272 bytes, lane-aligned: node `k` is lanes `6 + 2k`, `7 + 2k`. In a block after the first, input rate lane = previous output ⊕ message lane (XOR row), capacity lanes are wired copies, padding lanes are constants |
| `H_msg` | glue | lanes 0–1 R (signature), 2–3 seed, 4–5 `PK.root` (packed public bits), 6–10 `0x0000 ‖ M ‖ 0x1F` (packed public bits and constants); output lanes 0–3 unpacked to 256 bits (md 168, tree 54, leaf 9) |
| `PK.seed` in every call | σ | the two packed seed lanes, fan-out 3,959 |
| final root = `PK.root` | glue | last root unpacked; XOR with `PK.root`'s public bits → public word 6 = 0 (`finish_with_zeros`, as today) |
| statement | quotient public words | words 0–3 = `PK`, `M` (as today) |

Every Keccak input and output of SLH-DSA-SHAKE is whole lanes; only `M` (at byte 50) needs a shifted packing.

### 4.5 The link

**Port quad** `q` of block `b`: W row `R0 + 32b + q` with cells

`(X, Y, C, V) = (O_q, 1, I_q, O_q)`,

with `O_q` output lane `q` (X wired to its own V: free), and `I_q` input lane `q` (C wired to its source). The gate
holds (`V = X + C + C = X`).

`q_flock`'s block `b` holds the same four words at words `4q..4q+3`. Flock places `A_23[q]` twice (one lin-id
copy) and a `1` word, and `A_{-1}[q]` at `4q + 2`. Quad 25 is `(x, 1, 0, x)`; quads 26–31 are `(0, 1, 0, 0)`.

So W's cells on the aligned coset `o + V_19` (2^17 rows × 4) equal `q_flock`'s port region
(`(word < 128, block)`, 19 variables), word for word.

**Identity**: `W_R(z) + ℓ_q(z) = Q_link(z) · Z_19(z)`, where:
- `W_R` is the restriction of W's polynomial to the coset. It is one claim at a mixed point (`SPEC.md` §2, in
  `crates/quotient`'s novel basis).
- `ℓ_q(z) = q̂_port(y_0(z), …, y_18(z))`, with `y_l` the coordinate functionals (`domain::coordinate_functionals`).
  It is one claim on `q_flock`'s values, for 19² products.
- `deg ℓ_q ≤ 19 · 2^18`, so `Q_link` has ≈ 4.46M words.
- No challenge precedes it, so `Q_link` goes in C1.
- It is checked at the quotient's `t` with 2 sent values.

Prover: `ℓ_q` on 10 cosets of 2^19 by shifted-cube folds (`O(19 · 2^19)` each, leanvm_univariate's `copy_j`
code) and one inverse NTT, ≈ 0.1 s [E].

### M1 notes (as built: `lv42_flock::keccak`)

The port quads are as above; two things inside the block differ from §4.2, neither visible to the glue.

**Block layout** (64-bit words `w < 2048`; bit `z` of a lane is bit `z` of its word, the packing position; lanes
`x + 5y`):

| words | content | rows |
|---|---|---|
| `4q + 0`, `q < 25` | `A_23[q]` (X = output lane `q`) | lin-id: round 23's form `b[X] + t_23 + RC_23` |
| `4q + 1`, all `q < 32` | the K-word `1` (Y): bit 0 = 1, bits 1..63 = 0 | bit 0 constant (`A = B = [1]`); others empty |
| `4q + 2`, `q < 25` | `A_{-1}[q]` (C = input lane `q`) | free input |
| `4q + 3`, `q < 25` | `A_23[q]` (V) | lin-id copy of word `4q` |
| `100, 101, 102, 103` (quad 25) | `(x, 1, 0, x)`, `x` = bit 1 | bit 1 of 100 and 103 constant rows |
| `4q..4q+3`, `26 ≤ q < 32` | `(0, 1, 0, 0)` | |
| `64(j + 2) + l`, `j < 24`, `l < 25` | `t_j[l]` | product `(1 + b[x+1]) · b[x+2]` |
| `64(j + 2) + 32 + l`, `j < 23` | `A_j[l]` | lin-id `b[x] + t_j + RC_j` (`RC` on lane 0 only) |
| words 25..31 of each 32-word run; bits `[104,000, 131,072)` | 0 | empty (the suffix is Flock's `PaddingSpec`, 104,000 useful bits) |

**Changes from §4.2, and why**:
1. *The rounds' runs are aligned* (`t_j` at `64(j+2) + l`, `A_j` at `64(j+2) + 32 + l`) instead of packed
   (`t_0..t_23, A_0..A_22` contiguous, 83,393 bits). §4.2's structured terminal needs the slot index to factor as
   `(z: 6, lane: 5, kind: 1, round + 2: 5)` bit fields, so that the round factor is a shift between consecutive
   values of a 5-bit field; a packed layout (`128 + 25(2j + kind) + l`) does not factor and would cost the terminal
   a sum per round (≈ 20K more `E` products). Cost: the useful prefix is 104,000 bits (79%) instead of 83,393
   (64%), which the zerocheck's bit passes and the lincheck's fold pay (measured below).
2. *The constant wire is quad 0's Y bit* (slot 64) instead of a slot after `A_22`: every Y word needs its bit 0
   pinned to 1 anyway; quad 0's is the wire (lincheck's `const_pin_col`), the others are constant rows from it.
3. Quad 25's `x` words are both constant rows (not a copy of each other); empty bits are empty rows.

80,034 slots are constrained; ≈ 1.39M nonzeros a block.

**Measured** [M] (h1, `RUSTFLAGS="-C target-cpu=native"`, `FsShape::Rec`, walked terminal; `cargo test --release -p
leanvm_univariate --test flock_keccak -- --ignored --nocapture`): 4,096 blocks (3,959 random states, Keccak-f(0)
padding), `log_n = 29`, median of 3:

| skip | witness | prove | runs | stream |
|---|---:|---:|---|---:|
| 3 | 0.023 s | **0.189 s** | 0.181 / 0.189 / 0.192 | 3,552 B |
| 6 | 0.023 s | **0.132 s** | 0.132 / 0.120 / 0.148 | 4,752 B |

At skip 3 the zerocheck is ≈ 0.17 s of it (round 1 0.021, bit passes 0.073 / 0.039 / 0.016, storing 0.013, table
rounds 0.012), the lincheck (walk, fold, 11 rounds) ≈ 0.015 s. Within §4.9's 0.18 s and M1's 0.3 s target. The verifier's reference walk (generic `Scalar`) is
`leanvm_flock_gas::keccak_flock` (`flock_min::verify_walked_with::<_, Keccak>`); the prover's entry is
`leanvm_univariate::prover::flock::prove_keccak` (walked terminal only).

**For M3 (the structured terminal)**: the terminal is `Σ_rows e(row) (Â0 + α B̂0)(row, col) w(col)` with
`e = L(z_skip) ⊗ eq(row_low) ⊗ eq(chi_in)` (6 + 11 bits) and `w = s ⊗ eq(chi_in')`, plus `α² eq(chi_in, chi_in')
Σ e_i s_i` and the pin `α³ eq(word(64) = 1, chi_in') s_0`. Every round `j` reads only `A_{j-1}` (round 0 the C
words `4q + 2`) and writes `t_j` and `A_j` (round 23 the X words `4q`); rounds 1..22 are identical but for `RC_j`.
Corrections beyond the shifted rounds: round 0's reads (port C words), round 23's writes (X words) and the V copies
(`A = [word 4q, same z]`), the constant rows (34 slots: Y bits, quad 25's two `x` bits), the free inputs
(`A = [slot]`), the constant's column (every lin-id and free row's `B`, every product row's `A` has it, ι's bits),
and the empty lanes 25..31 of each run. The forward walk to check against is `keccak_flock::row_values`.

### M3 notes (as built: `leanvm_flock_gas::keccak_flock::structured_terminal`)

`Keccak`'s `WalkedCircuit::terminal` is now the structured one (`verify_walked_with::<_, Keccak>`); `KeccakWalked` keeps
M1's walk as the reference (the trait's default terminal, `walked_terminal_with`). The algorithm:

1. **Packing weights.** `E = L(z_skip) ⊗ eq(row_low)` is split at bit `p = max(k, 3)` into `E_low ⊗ E_high`
   (`8 + 8` entries at skip 3).
2. **The 40 correlations** `Corr[off] = Σ_z E_z s_(z − off)`, `off` ∈ ρ's rotations ∪ (rotations + 1), the offsets
   θ's `z − 1` adds. They go through 8 partial correlations of length 8, `Q[ol][m] = Σ_zl E_low[zl] s_(8m + zl − ol)`
   (512 products), then `Corr[off] = Σ_zh E_high[zh] Q[off mod 8][zh − off/8]` (320). `Corr[0]` is also the
   `C = I` claim's `Σ e_i s_i`.
3. **Eq factors.** `eq(chi, word) = Lr[lane] · Kd[kind] · Rd[round + 2]`, on both sides (four 5-variable tables).
   A port word `4q + r` is lane field `4(q & 7) + r` in group `q >> 3`.
4. **b's terms.** For each of the 25 lanes `i` of `b`, a row weight `U_i = Kd0 (Lr[x−1] + α Lr[x−2]) + Kd1 Lr[i]`
   covers the t rows' left and right and the A row. It is scaled by the round factor
   `Σ_(j=1..22) Rd[j+2] Rh[j+1]` (rounds 1..22), plus round 23's (its A row is a port X word) and round 0's (its
   columns are the port C words). It is spread over `b[i]`'s two offsets by θ's column sums of `Lh` (or of the C
   words' column weights): 50 coefficients `G[off]`, then `Σ G[off] Corr[off]`.
5. **Corrections**:
   - the constant column, `s_0 eq(word 1, chi')`, times the t rows' `1`, ι's bits (`E` at `z = 2^m − 1`), the 34
     constant rows and every `B = [1]` (using `Σ_z E_z = 1`), plus the pin's `α³`;
   - the free inputs, the V copies and the A rows' `t` term, times `Corr[0]`.

   Lanes 25..31 and the suffix have no term.

**Tests** [M]: `crates/leanvm_flock_gas/tests/keccak_terminal.rs` (run on h1 and on a Mac).
- It is equal to `walked_terminal_with::<_, KeccakWalked>` at random points, challenges and slices at every skip
  0..6, with 24 trials at skips 3 and 6.
- It is equal for each of the 64 packing positions alone (`s = e_i`, unit and random weight) at skips 3 and 6.
- The eq points of `FsShape::Rec`/`Rec3` do not enter the terminal's inputs, which are the zerocheck's and lincheck's
  round challenges.
- The end-to-end test (`leanvm_univariate/tests/flock_keccak.rs`) now checks every verdict with both terminals and
  asserts they agree. On a Mac (M-series):
  - at 128 blocks, skips 3 and 6, `Rec` and `Main`, the proofs are accepted and a changed slice and a flipped state
    bit are rejected;
  - at 4,096 blocks (ignored test), the proofs at skips 3 and 6 are accepted and a flipped output bit is rejected;
    prove 0.181 s at skip 3 and 0.125 s at skip 6 (not comparable to h1's).

**Op count** [M] (the recorder's `Mul` and `Add` nodes, `structured_terminal_ops`):

| skip | products (by a constant) | sums | **`E` ops** | where they go |
|---|---:|---:|---:|---|
| 3 | 1,510 (8) | 1,509 | **3,019** | partial correlations ≈ 960, correlations 600, eq tables ≈ 250, lane loop ≈ 575 |
| 6 | 3,449 (64) | 3,350 | 6,799 | correlations `40 · 64` ≈ 5.1K, 64 Lagrange weights |

Target ≤ 15K. The walk it replaces records 563,462 ops at skip 3 (255,704 products, 307,758 sums; the recorder
shares common subterms).

**Flock for 4,096 Keccak-f, structured terminal** [M] (`flock_keccak_verifier_fragment`: recorded, compiled, run on
revm; log_n 29):

| shape | scalars (B) | Keccak-256 | Keccak-f | `FIELD_MUL` (live) | recorded products / sums | execution (of it the terminal) |
|---|---:|---:|---:|---:|---:|---:|
| **skip 3, `Rec3`** (= `Rec` for Flock) | **148 (3,552)** | **47** | **59** | **2,239** | 2,266 / 2,622 | 74,374 (42,145) |
| skip 6, `Rec3` | 198 (4,752) | 44 | 66 | 4,446 | 4,641 / 4,563 | 129,704 (87,926) |

Keccak-f counts each hash's `⌈(32 + absorbed bytes + 1) / 136⌉` blocks.

**π2 positions** (§4.7's accounting):
- Flock: 59 Keccak-f × 130,736 = 7.71M, plus ≈ 4.9K `E` ops at ≈ 10 positions an op (SPEC-REC §10.4 measured
  114,704 positions for 11.7K ops) ≈ 0.05M: **≈ 7.76M**.
- The whole π1 of §4.7: 91 Keccak-f = 11.9M. Its `E` ops are ≈ 10.7K (this terminal 3.0K instead of the modelled
  10K, plus the ring kernel 5.3K, the quotient 0.4K and the batch weights 2K), and with the stream bits that part is
  ≈ 1.23M. Total **≈ 13.1M of 2^24 (78%)**, against the modelled 13.2M.

### 4.6 Claims and sizes

| commitment | content | words [E] | stack | claim |
|---|---|---:|---|---|
| C1 (proof) | `q_flock` 2^23, `Q_link` 2^22 + 2^19, W 2^21 block | 15.2M | 2^24 (90%) | 1 at `r` |
| C2 (proof) | the quotient table at 2^18 rows (55 words a row non-hiding; 63 hiding) | 14.4M | 2^24 (86%) | 1 at `r` |
| setup | σ (4 words a row) | 1M | 2^24 | 1 at `r` |

The relations batched: quotient (W at its digits, Q at two novel-basis points, σ), Flock's ring-switch weight
(`ring_tower::weight_at`), the link (three claims), `ρ`-combined; then one point `r` (24 coordinates from 12 narrow
challenges).

### 4.7 π2 and the gas

π1's verifier, recorded generically (`leanvm_flock_gas::evm::record`), is compiled by leanvm_rec's circuit
compiler exactly as π1-rec3's.

**Size** [E]:
- Keccak-f in π1's transcript: seed 1, C1 → `α, β` 2, Flock 59, `t` 1, values 2, `λ` 1, batch ≈ 25: **≈ 91**.
  - Flock = [b]'s 56 at log_n 29, plus 3 lincheck rounds (`k_log` 17 − 6 = 11 against 8).
- Positions: 91 × 130,736 = 11.9M. `E` ops (Keccak terminal 10K, ring kernel 5.3K, quotient 0.4K, batch weights
  2K) and stream bits ≈ 1.3M.
- **≈ 13.2M of 2^24 (79%)**.
- D8v (−192 B of calldata) would need ≤ ≈ 60 Keccak-f: not reachable while Flock alone takes 59.

**Gas** [E, against [g]]:

| | π1-rec3 (measured) | SLH C\* (modelled) |
|---|---:|---:|
| calldata | 980 B (59 zero) | ≈ 964 B (≈ 55 zero): selector 4, `PK ‖ M` 64, π1's roots 64, 12 challenges + 3 values 360, π2's roots 64, π2's 17 values 408 |
| execution | 29,832 | ≈ 29.8K ± 3K: +1 statement port, −2 challenge ports, push groups re-derived from the new graph |
| **EIP-7623, c = 0** | **44,804** | **≈ 44.6K (42–48K)**; floor 38.6K |
| claims / calls | 7 / 6 | 7 / 6 (π1's 3, π2's 4) |

**Toward 40K** [E]:
1. The push side (14.8K in π1-rec3) is its largest part. PI2.md dropped hand-scheduled kernels for lack of slack
   in 2^24; here 21% is free: −2K to −5K.
2. 20-byte reads of the narrow coordinates: −432.
3. 40–42K looks reachable. Below the 38.6K floor it is not, short of smaller π2 values.

**Other parameter sets**: the gas is about the same. 192s, 256s and the f sets have 5.7K–17.8K Keccak-f, which add
1–3 Flock rounds and a bigger `q_flock` (2^24–2^26 words, a 2^25–2^26 C1). π2 stays at 2^24.

### 4.8 Soundness sketch (target ≈ 128 bits, as the repository)

Lists: WHIR's certified level-0 lists at 2^24, 9,952 = 2^13.3 per commitment
(`review/leanvm_univariate_params.py`). A challenge drawn after C2 pays both proof lists (2^26.6).

| term | error before lists | after lists [E] |
|---|---|---:|
| Flock (leanerVM's `flockErrorsOf_bounded` form; eq point by squares, degree 2^19; skip 3; ring switch) | ≈ 2^-161 | ≈ 147.7 bits (C1) |
| quotient copy argument (`α, β`, ≈ 4·2^20/\|E\|) | 2^-170 | ≈ 156 (C1) |
| quotient identity at `t` (degree ≈ 2^24) | 2^-168 | ≈ 141 (C1·C2) |
| link identity at `t` (degree ≈ 2^22.3; polynomial, no prior challenge) | 2^-169.7 | ≈ 143 |
| `ρ`, `λ` (a few hundred relations) | ≈ 2^-183 | ≈ 156 |
| **batch, narrow 160-bit pairs** (12 pairs of degree 8, as π1-rec3) | 2^-153.4 | **126.9**: below 128, so take **168-bit** challenges (3 zero bytes; +144 gas): 134.9 |
| WHIR openings (3 of π1, 4 of π2) | | ≈ 129 each (query-bounded), 126.4 by a plain union of six, as leanvm_rec |
| π2 (leanvm_rec's) | | `t` 140.6, copy 152.7 |

Statement-level: the Keccak block R1CS is Keccak-f (tested against `sha3`, plus the const pin); the lane glue is
`lib.rs`'s logic (tested against `lib.rs`'s bit circuit and RustCrypto). Fiat–Shamir is in the random-permutation
model as elsewhere. No zero knowledge is claimed or needed: the signature is not secret, so the quotient's hiding
layout can be dropped (−13% of C2).

### 4.9 Prover, modelled from the anchors

| phase | time on h1 [E] | from |
|---|---:|---|
| witness: 3,959 Keccak-f, glue evaluation over K | 0.05 s | [a] (witness 0.01–0.04 s) |
| Flock, 2^29 bits, skip 3 | 0.18 s | [a]: 0.094 s at 2^28, 0.328 s at 2^30 |
| quotient reduction, 2^18 rows | 0.45 s | [e] 5.27 s / 16, rounded up for small-size inefficiency |
| `Q_link` | 0.1 s | NTT 2^23 10.6 ms a column [h, PROVER.md] |
| WHIR commits C1, C2 (2^24 each) | 0.2 s | [h] |
| batching sumcheck (three 2^24 stacks) | 0.1 s | [h] 0.57 s at 2^27 |
| 3 openings (2^24) | 0.3 s | [h] |
| **π1** | **≈ 1.4 s, ≈ 3 GB** | |
| π2: evaluate π1's graph, prove, open | **4.5 s, 9.5 GB** | [f] |
| **total** | **≈ 6 s, ≈ 10 GB peak** | |

## 5. Reuse and new code

**Reused** (file level):
- `crates/lv42_flock`:
  - `zerocheck/skip.rs` (any skip), `zerocheck.rs`;
  - `lincheck.rs` (`prove_padded_capture_s_hat_v_rows`, the `LincheckCircuit` seam);
  - `witness.rs`'s packing drivers.
- `crates/leanvm_univariate`:
  - `prover/flock.rs` (`prove`, `FlockWitness`);
  - `stacks.rs`, `prover/batch.rs` (the batching sumcheck, Rec3 pairs);
  - `domain.rs` (coordinate functionals, mixed points);
  - the `copy_j`/`ℓ_j` prover code (shifted cubes);
  - `verifier.rs`'s `FLOCK_REC3` plumbing.
- `crates/leanvm_flock_gas`:
  - `flock_min.rs` (`verify_walked`: make the terminal a trait);
  - `transcript.rs` (`KeccakChannel`, `FsShape::Rec3`, `sumcheck_pairs_drawn`);
  - `ring_tower.rs`, `stack.rs`, `scalar.rs`;
  - `evm/` (recorder, compile, link, revm).
- `crates/quotient`:
  - `circuit.rs` (Builder, σ, public words, `finish_with_zeros`);
  - `protocol.rs` (`reduce_in`/`prove_in`, `Inverse::Hint`, `verify_reduction_in`);
  - `domain.rs`, `ntt.rs`, `transcript.rs`.
- `crates/leanvm_rec`: the circuit compiler (`circuit/`), `pi2/` (prover, verifier, contract), `fs.rs`, `eval.rs`.
- `crates/slh_dsa`:
  - `lib.rs` (parameters, ADRS, `base_2b`, `to_int`: the reference logic);
  - `tests/real.rs` (RustCrypto signatures and the 21 tamperings).
- `crates/evm/src/machine.rs` (the `PCS_OPEN` ABI).

**New**:
1. `lv42_flock::keccak`: the Keccak-f block R1CS, witness, port quads and walk. It is a vendored-crate addition, so it
   takes a header per `NOTICE.md`'s conventions.
2. The Keccak structured terminal (verifier, generic `Scalar`), in `leanvm_flock_gas`.
3. Builder extensions in `quotient::circuit`: free-K rows, K-valued evaluation (`cells_k`), the port-quad region.
4. `slh_dsa::glue`: the lane-level SLH-DSA circuit.
5. π1 (`crates/slh_dsa/src/pi1/` or a new crate `slh_fast`):
   - stacks;
   - the quotient reduction in the host transcript, leaving claims instead of opening;
   - the link (`Q_link`);
   - prover and verifier.
6. π2 glue: π1's IV, ports (the 64-byte statement), contract entry.
7. `review/slh_fast_params.py`: sizes, soundness, gas.

leanVM's `keccak_gkr` is not needed (B rejected), so nothing more is vendored.

## 6. Milestones (agent time; each with a testable deliverable)

| | deliverable | test / benchmark | estimate |
|---|---|---|---|
| **M1** | Keccak-f block R1CS for Flock (`k_log` 17, `C = I`, port quads), witness generator, prover-side walk; Flock end to end on 4,096 blocks with the walked terminal (Rust verifier, cost irrelevant here) | `keccak_f` of the block = `sha3`'s on random states; `flock_min::verify_walked` accepts, the slices are the witness's, a flipped bit is rejected; **bench: Flock proves 4,096 Keccak-f (2^29 bits) in ≤ 0.3 s on h1** (expected ≈ 0.2 s from [a]) | 2 days |
| M2 | lane-level glue (Builder extensions, `slh_dsa::glue`), K-valued evaluation | with real Keccak outputs in the ports, word 6 is zero on 3 RustCrypto signatures and not on the 21 tamperings (the `tests/real.rs` set); rows ≤ 2^18; agrees with `lib.rs`'s bit circuit on the same inputs | 2–3 days |
| M3 | the Keccak structured terminal | equals M1's walk at random points for all 64 packing positions; ≤ 15K `E` ops recorded | 2 days |
| M4 | π1: commitments, quotient reduction in π1's transcript, Flock, link, batch, openings | Rust verifier accepts real proofs, rejects mutations (stream bytes, roots, port words); h1 prover ≤ 2 s, ≤ 4 GB; recorded graph ≤ 100 Keccak-f | 5–6 days |
| M5 | π2 from π1's graph; contract | end to end on revm with `PCS_OPEN` attesting 7 claims; 18-style calldata mutations rejected; **gas measured** (target ≤ 46K) | 3–4 days |
| M6 | review and tuning | adversarial review; `review/slh_fast_params.py`; push-side tuning toward 40K | 3 days |

Total ≈ 17–20 agent-days. M1's benchmark is the earliest confirmation of the prover claim. If it holds, the only
other large term is π2, which is already measured.

## 7. Risks and open questions (ranked)

1. **Gas lands at 44–47K, not 40K.** The model is anchored on the measured 44,804; 40K depends on π2 push-side work
   not yet done (§4.7). *Question for the user: is ≈ 45K acceptable, or is 40K a requirement?*
2. **The link's layout details**:
   - `W`'s committed basis (novel) and the restriction formula for its cell order (`4r + role`);
   - `Q_link`'s degree (2^22.3), which puts C1 at 90% of 2^24 (fallback: a 2^25 C1, +0.1 s, better lists).
   - The port quads force an output lane into `X`/`V` and an input lane into `C`, which σ must respect.
3. **Keccak terminal cost**: a naive walk would overflow π2 (≈ 10M positions). The structured form is built (M3):
   3,019 ops at skip 3, equal to the walk [M].
4. **C2 near capacity** if the quotient keeps its hiding layout (63 words a row = 98% of 2^24). Use the non-hiding
   layout (86%) or a 2^25 C2.
5. **π1 transcript count** (≈ 91 Keccak-f [E]): the batch pairs' message size sets ≈ 12–25 of it. Up to ≈ 110 still
   fits π2.
6. **Narrow batch challenges**: 126.9 bits at 160 bits with 2^24 lists. Take 168 bits (§4.8) or 2^26 stacks.
7. **The quotient over K-valued cells**: the PIOP is unchanged, but its Lean development covers bit circuits only.
   K semantics (free-K rows, Booleanity only where bits are unpacked) need their own argument and tests. No formal
   proofs are planned (as for leanvm_rec).
8. **`C = I`** doubles Flock's bits (2^29 instead of 2^28). Harmless for time (≈ +0.1 s); general `C` is optional.
9. **Memory**: π2's 9.5 GB dominates; h1 (61 GB) is fine.
10. Open:
    - Batching several signatures in one proof: π2 stays fixed, so the gas per signature drops roughly as 1/k.
      Out of scope here.
    - Parameter sets beyond `n = 16` need 3–4-lane nodes in the glue: wiring only.

## Appendix A: probes (in the working tree, not built by the workspace)

- `crates/slh_dsa/probe/verifier_fragments.rs` measures the verifier fragments: Flock 42422001 and the π1-rec3
  shape at log_n 26–32, and Keccak GKR at 2^12 and 2^18. Copy it to `crates/leanvm_flock_gas/tests/` and run
  `cargo test --release -p leanvm_flock_gas --test verifier_fragments -- --ignored --nocapture`.
- `crates/slh_dsa/probe/flock_scale.rs` measures Flock's prover at 2^28 and 2^30 bits. Copy it to
  `crates/leanvm_univariate/tests/` and run
  `cargo test --release -p leanvm_univariate --test flock_scale -- --ignored --nocapture`.
- Also run on h1, without changes:
  - `cargo bench -p quotient --bench membership` (anchor e);
  - in a leanVM checkout (`5ae9d4299`), `KECCAK_N_LOG=12 KECCAK_DEPTH=12|6 cargo bench -p keccak_gkr --bench hash_batch`
    (anchor d).

Raw outputs (h1, `RUSTFLAGS="-C target-cpu=native"`, 2026-11-05):

```text
Flock, 2^14 BLAKE2s blocks (2^28 bits), skip 3: witness 0.01 s, prove 0.094 s, stream 3840 B
Flock, 2^14 BLAKE2s blocks (2^28 bits), skip 6: witness 0.01 s, prove 0.063 s, stream 5184 B
Flock, 2^16 BLAKE2s blocks (2^30 bits), skip 3: witness 0.04 s, prove 0.328 s, stream 3936 B
Flock, 2^16 BLAKE2s blocks (2^30 bits), skip 6: witness 0.04 s, prove 0.198 s, stream 5280 B
Flock rec3 shape, log_n 28: stream 3360 B (140 scalars), KECCAK256 43, FIELD_MUL 48159
Flock rec3 shape, log_n 29: stream 3408 B (142 scalars), KECCAK256 44, FIELD_MUL 48163
Flock rec3 shape, log_n 30: stream 3456 B (144 scalars), KECCAK256 45, FIELD_MUL 48167
Keccak GKR 4af2cddd, 2^12 permutations, depth 12: stream 32328 B (1347 scalars), KECCAK256 287, FIELD_MUL 92905, execution 3563625
Keccak GKR 4af2cddd, 2^12 permutations, depth 24: stream 59880 B (2495 scalars), KECCAK256 519, FIELD_MUL 172430
Keccak GKR 4af2cddd, 2^12 permutations, depth 6: stream 18168 B (757 scalars), KECCAK256 164, FIELD_MUL 57183
Keccak GKR batch proving, 4,096 permutations, depth 12: prove TOTAL 66.4 ms; depth 6: 40.0 ms; 8,192 (depth 12): 167.2 ms
membership (quotient, 2^22 rows): reduction 5.269 s, openings 1.494 s, prover total 6.778 s, peak 5.81 GiB
```

The probes' "~Keccak-f" column spreads the stream evenly over the calls, so it undercounts. The Keccak-f figures in
the text count the large absorptions (the 64 slices and the skip's values) block by block.

## Appendix B: M2 notes, the glue as built

**Built** [M]: `quotient::circuit`'s lane extensions and `slh_dsa::glue` (`src/glue.rs`, `tests/glue.rs`).

**`quotient::circuit` additions.** Existing circuits are unchanged: the membership tests, the pinned proofs and
digests, and the bytecode all pass.
- `Builder::free_k`: the row `(own V, 1, 0)`.
- `Builder::mul(a, b)`: the row `(b, a, b)`, so `V = a·b`.
- `Builder::with_ports(rows, start, len)` and `Builder::port(index, out, input)`: the row `(out or own V, 1, input)`
  at `start + index`.
- `Circuit::{port_region, ports}`: the placed ports, and the point of the build where each was placed.
- `Circuit::outputs_k(free)`: evaluates over `K` in build order. Every free row (`X` reads itself) takes
  `free(row, outputs so far)`.
- `Circuit::cells_k`, `Circuit::check_k`: every gate and every cycle of σ, over `K`.
- `read_k`, `gate_k`, `CheckError`.
- `Src` now derives `Hash`.

**The port layout as implemented.**
- The region is rows `[2^17, 2^18)`, that is cells `[2^19, 2^20)`.
- Quad `q` of block `b` is at row `2^17 + 32 b + q` (`glue::port_index`).
- Block `b` is the `b`-th Keccak-f call in build order. There are 3,959 calls, then 137 Keccak-f(0) blocks.
- `q < 25`: `(X, Y, C, V) = (O_q, 1, I_q, O_q)`.
  - `C` is wired to the input lane's source, or to the constant 0.
  - `X` is free, except for an **unpacked** output (the digest's lanes 0–3, each layer message's and the final
    root's lanes 0–1). There `X` reads the row `Σ b_i x^i` of 64 free bits, so `V = X` = that packing.
  - The four values are the same either way.
- `q = 25`: `(x, 1, 0, x)`, `x` free (prover value `F64::G`). Block 0's is the glue's `x`; `x^2..x^63` are
  `mul` rows.
- `26 ≤ q < 32`: `(0, 1, 0, 0)`: `X` reads the constant 0 (not free).
- `glue::Glue::check_ports` states what Flock and the link must establish: every quad has its form, and each
  block's 25 `V`s are Keccak-f of its 25 `C`s.

**Rows** (SLH-DSA-SHAKE-128s, `tests/glue.rs`) [M]: 51,027 below the region, plus 131,072 port rows = 182,099 of 2^18
(69%). Built in 0.02 s; one honest witness is evaluated and checked in about 0.02 s.

| gadget | rows [M] | §4.3 [E] |
|---|---:|---:|
| public rows | 512 | |
| inputs: 512 public bits, 982 signature lanes | 1,494 | |
| `x` powers and constant lanes (cached by value, split by bytes) | 944 | 2,200 |
| public bits → seed, `PK.root`, `M` lanes | 512 | |
| ADRS packing (shared packings, 1 row a variable bit) | 1,668 | 17,200 |
| unpacking: 1,280 bits, 2 rows a bit | 2,560 | 3,840 |
| WOTS+ `at_most(digit, j)` | 12,005 | 14,700 |
| WOTS+ step mux (`select` on 2 lanes) | 18,375 | 18,375 |
| WOTS+ checksum (`lib.rs`'s 12-bit adder) | 10,766 | 14,336 |
| auth-path swap (`ordered` on 2 lanes) | 1,617 | 1,617 |
| sponge continuation XORs | 446 | 510 |
| root comparison (word 6) | 128 | |
| **below the region** | **51,027** | ≈ 76K |

**Deviations from §4.3–4.5.**
- **Unpacking.** The port's `X` reads the packing of the free bits, so no equality gadget is needed. It costs 2 rows a
  bit (the free bit, then `(acc, b_i, x^i)`, which gives `acc + x^i + b_i x^i`), not 3.
- **Packing.** It starts from the cached constant `Σ_{b_i = 1 or variable} x^i`, so each variable bit is one row.
  There is no NOT.
- **Constants.** `x^0` is the 1 anchor and `x^i` a `mul` chain. A constant lane is the XOR of a smaller cached
  constant and a power or a byte.
- **Reuse of `lib.rs`.** The glue reuses `Adrs::bits`, `base_2b`, `to_int`, `at_most`, `add`, `select` and
  `ordered`. Over `K` these are correct whenever their control is a bit, so the statement code is shared.
- **Bits stay bits.** The muxes, swaps and comparisons read only free bits, or bits computed from them.

**Tests** [M]:
- `tests/glue.rs::glue_verifies_real_signatures`, 3.7 s:
  - three RustCrypto signatures: the gates, σ and the ports hold, the public words are the statement and word 6 is
    0;
  - the digest is `sha3`'s SHAKE256, and the last root is `PK.root`;
  - the 21 tamperings of `tests/real.rs` give word 6 ≠ 0.
- `glue_agrees_with_the_bit_circuit` (ignored; 4 s, 6.3 GB):
  - on a toy set (`h 6, d 2, h′ 3, a 3, k 14, m 8`: 1,126 Keccak-f, a 127M-row bit circuit), with random inputs;
  - the glue's digest, FORS key, both layer roots and word 6 equal those of `lib.rs`'s bit circuit.
- Unit tests in `glue::tests`:
  - constants and packing;
  - mux and swap;
  - ADRS lanes against their bytes, for each address type;
  - the sponge against `sha3` at 0–76 lanes (1–5 blocks), with unpacking;
  - the ports bind: a wrong output or unpacked bit fails `check_ports`, and a non-bit fails its gate.
- `quotient::circuit::tests::lane_cells_and_ports`.
