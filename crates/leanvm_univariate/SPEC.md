<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# A univariate PIOP for leanVM 42422001, for the EVM

**Status: milestone 1 (spec, soundness script, verifier-only gas prototype).** Option A: Flock's sumcheck kept
for BLAKE2s, everything else univariate. The Flock section (§7) is owned by the Flock agent; this file fixes its
interface. Numbers marked *measured* come from `tests/gas.rs` on revm; *modelled* ones are computed.

## 0. Summary

Same statement as leanVM 42422001 (same VM, the same six tables and their columns, the same bus tuples and
fingerprints, BLAKE2s by Flock, the same public input), a different proof of it:

- **Two proof commitments** and one setup commitment: `C1` = the tables' columns (univariate, novel-basis
  coefficients on Cantor subspaces) and Flock's `q_flock` (values, as leanVM); after the bus challenges, `C2` = a
  **product heap** (the bus's grand product as a committed binary tree on Cantor cosets) and the quotients.
- **No GKR, no table sumcheck, no stack batching sumcheck**: every identity is a quotient identity checked at
  **one random point `t`**, the verifier receiving only the evaluations that occur in nonlinear terms
  (PLONK-style linearisation) and folding everything linear into **one weighted claim per commitment**.
- The bus is a **grand product** (exact multisets), not logUp: in characteristic 2, `Σ 1/(β + f)` only proves
  the multisets equal modulo 2 (two identical fake reads cancel), which leanVM's memory argument cannot afford
  (§5.1).
- Flock (zerocheck, lincheck, `A0`/`B0` claims) as in leanVM; ring switching becomes one weighted claim on
  `q_flock` (§7).

## 1. Statement and workload

leanVM 42422001 (`crates/verifier` there; vendored and made generic in `crates/leanvm_flock_gas`): a proof that the
VM, run on the stacked bytecode (the program, fixed) from `pc = 1, fp = 1`, halts at `pc = g^(2^19 - 1)`, `fp = 1`,
with the 32-byte public input in memory cells 0 and 1 and every BLAKE2s precompile call correct.

- Fields: `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, `E = K[y]/(y^3 + y + 1)`; `g = x` (`GEN`).
- Tables (leanVM's, `layout.rs`): XOR (15 columns), MUL (15), SET (8), DEREF (15), JUMP (14), BLAKE2S (37: 19 own,
  18 value limbs that leanVM commits inside `q_flock`); memory (3 limbs and a final count, `2^lm` cells); bytecode
  (a final count, `2^lb` instructions); `q_flock` (Flock's packed witness, `2^(h_B + 8)` K-words).
- Bus (leanVM's): tuples of up to 16 coordinates, fingerprint `β + Σ_s eq(α, s) τ_s` with `α ∈ E^4`, three channels
  (state, bytecode with counters, memory with counters), the counters powers of `g`, push and pull multisets equal,
  every counter nonzero; the framework blocks (state boundary, memory image with counts 1 and final counts,
  bytecode with counts 1 and final counts); padding rows hold `padRow` (zero, but for BLAKE2S's limbs, which hold
  the padding instance `blake2s(0^64)`).
- Constraints: JUMP's two (`b + v_cond·w`, `v_cond·(b + 1)`), degree 2; the other tables' rows are constrained by
  the bus only.

**Reference workload** (the largest of about 1M cycles; leanVM's own `gas-dump`, run on h1): **1,000 leanXMSS
signatures, 1,023,109 cycles**; table rows XOR 183,266, MUL 195,439, SET 223,851, DEREF 137,591, JUMP 80,937,
BLAKE2S 202,025 (log-heights 18 18 18 18 17 18), memory `2^21`, bytecode `2^19` instructions (`2^23` words),
`q_flock` `2^26` words. leanVM's own stack for it is `2^26.53` words.

## 2. Domain and encodings

- **Cantor basis** of `K`: `β_0 = 1`, `s(β_{k+1}) = β_k`, `s(x) = x^2 + x` (`crates/quotient/src/domain.rs`, the
  same algorithm). `ω_i = Σ_k i_k β_k`, `V_r = {ω_i : i < 2^r}`. Digits `w_0(x) = x`, `w_{k+1} = s(w_k)`;
  `w_r = Z_{V_r}`, the subspace polynomial (`s^(r)` vanishes on `V_r`, is monic of degree `2^r`, `w_r(β_r) = 1`), and
  `w_l(ω_i) = ω_{i >> l}`.
- **Novel basis** `X_k = Π_{l : k_l = 1} w_l`. A column of `2^r` rows is the polynomial of degree `< 2^r` with its
  values on `V_r` (row `i` at `ω_i`), **committed as its `2^r` novel coefficients**. Then
  `f(t) = Π_{l<r} (1 + w_l(t)) · ĉ(u_0, …, u_{r-1})`, `u_l = w_l(t) / (1 + w_l(t))`: a multilinear claim on the
  coefficient table (`eq(u, k) = X_k(t) / Π (1 + w_l(t))`). The sum over `V_r` is the top coefficient
  (`Σ_{V_r} X_k = [k = 2^r - 1]`).
- **Restriction to a coset.** For `F` of `2^m` coefficients and an aligned coset `o + V_r` (`o = ω_j`, `2^r | j`),
  `R(x) = Σ_k c_k X_{k mod 2^r}(x) X_{k - k mod 2^r}(o)` has degree `< 2^r` and agrees with `F` on `o + V_r`; `R(z)` is
  one multilinear claim on `F`'s coefficients at the *mixed point* (`u(z)` on the low `r` coordinates, `u(o)` on the
  high ones). This is how one big committed polynomial (the heap) serves many small identities.
- **Composition with values.** For a K-column `v` committed as **values** (as `q_flock`'s limbs are), let `y_l` be
  the linearised polynomials `Σ_{m<r} a_{l,m} x^{2^m}` with `y_l(ω_i) = i_l` (the Moore system of `β_0..β_{r-1}`).
  `ℓ(x) = ṽ(y_0(x), …, y_{r-1}(x))` agrees with `v` on `V_r`, has degree `≤ r 2^(r-1)`, and `ℓ(t) = ṽ(y(t))` is one
  multilinear claim on the values. The verifier pays `r^2` products for `y(t)`.
- E-valued polynomials are committed as their three K-limb coefficient columns; a claim on one is one term with the
  limb recombination (`crates/quotient`'s extension coordinates).

## 3. Commitments

| commitment | when | content (reference workload) | words |
|---|---|---|---:|
| `F` (setup, fixed) | once per program | the stacked bytecode as 16 slot columns on `V_19`; the pc index `g^i` on `V_19`; the memory address `g^i` on `V_21` | `2^23.3` |
| `A0`, `B0` (setup) | once | Flock's BLAKE2s R1CS (as in the baseline; the Flock agent may change them) | `2^28` each |
| `C1` | first | `q_flock` (values, `2^26`); every table column (coefficients); **added**: BLAKE2S's 18 limbs again as univariate columns (`copy_j`), and one counter-inverse column `z_T` per table; memory (4 columns, `V_21`), bytecode final count (`V_19`) | `2^26.62` → stack `2^27` |
| `C2` | after `α, β, γ` and Flock | the product heap `T` (`2^23` E-values), its tree quotient `Q_tree`, the leaf quotients `Q_b` (one per heap block), the constraint quotient `Q_W` | `≈ 2^26.7` → stack `2^27` |

Roots of `F`, `A0`, `B0` are constants in the contract's code (no `SLOAD`); `C1`, `C2` roots are in calldata.
Every commitment is opened by **one** `PCS_OPEN` call carrying **one** claim (all its claims combined by a final
challenge `ρ`, §8): WHIR takes no OOD sample at level 0, so a root binds only a list of tables and all claims on it
must be checked together (AGENTS.md).

The two additions to `C1` keep leanVM's statement: `copy_j = q_flock`'s limb `j` on every row (a constraint of
`Q_W`), and `z_T · Π_j c_j = 1` on active rows (a constraint of `Q_W`) proves every counter nonzero, which leanVM's
count tree proves (an alternative keeping leanVM's count channel: count leaves in the heap, §5.4).

## 4. Transcript and challenges

Keccak-256 chain (`leanvm_flock_gas::transcript::KeccakChannel`: a challenge is one Keccak-256 of the state and the
calldata bytes read since the last one; 24 bytes a scalar, 16 a root half). Seed: Keccak-256 of a 16-byte name, the
program's IV (which must bind `F`, `A0`, `B0`) and the public input. Order:

1. `C1` root; `α ∈ E^4` (tuple weights `eq(α, ·)`), `β` (fingerprint shift), `γ` (the batching of `C1`-only
   constraints into `Q_W`).
2. Flock (§7): its zerocheck, lincheck and matrices' rounds and challenges, its 64 slices, the ring map.
3. `C2` root; `t ∈ E`.
4. The values at `t` (§8).
5. `ρ` (the combination of all linear relations into one claim per commitment).

The verifier rejects if `t` (or a derived point) makes a denominator vanish: `1 + w_l(t)`, `w_1(t)`, every
`Z_act,T(t)`.

## 5. The bus as a product heap

### 5.1 Why not logUp

`Σ 1/(β + f)` over a multiset in characteristic 2 sees each tuple's multiplicity mod 2. Two accesses at one
address with the same count reading the same fake value pull `(A, v', c)` twice and push `(A, v', g c)` twice: both
cancel, and a program that reads a cell twice can be made to read anything. (A sound variant exists — tag every
push with its public position and every pull with a committed pointer to the push it consumes; then the push side is
a set, `#push = #pull`, and mod-2 equality forces exact equality — but it adds a column per flush and leaves
leanVM's tuples; it is not used.) The bus here is leanVM's grand product.

### 5.2 Heap

`T` is one polynomial on `V_23` (`2^23` E-values): position `i` holds node `i` of a binary heap (children `2i`,
`2i + 1`; root at `i = 1`, `ω_1 = 1`), the leaves at `i ∈ [2^22, 2^23)`, the coset `β_22 + V_22`. Since
`s(ω_i) = ω_{i >> 1}`:

**Tree identity.** `T(s(x)) = T(x) T(x + 1)` for `x ∈ V_23 \ V_1`, i.e.
`T(s(x)) + T(x) T(x+1) = Q_tree(x) · w_23(x) / w_1(x)`, `deg Q_tree ≤ 2^23 + 2`.

**Leaves** (ratio leaves: push fingerprints over pull fingerprints, per row), in aligned blocks of the leaf coset:

| block | rows | leaf | offset in `[0, 2^22)` |
|---|---:|---|---:|
| memory | `2^21` | `D_init / D_fin` of cell `i` | 0 |
| bytecode | `2^19` | `D_init / D_fin` of instruction `i` | `2^21` |
| XOR, MUL, SET, DEREF, BLAKE2S | `2^18` each | `Π_j D'_j / Π_j D_j` over the row's flushes | `2^21 + 2^19 + k 2^18` |
| JUMP | `2^17` | same | `2^21 + 2^19 + 5·2^18` |
| unused | `2^17` | 1 | the rest |

Padding rows (`padRow`) push exactly what they pull (zero row: `g·0 = 0`), so their leaf is 1, as in leanVM.

**Leaf identity** of block `b` (domain `V_{r_b}`, coset `o_b = β_22 + ω_{offset}`), with `R_b` the restriction of `T`
to it (§2) and `P_b, P'_b` the products of its pull and push fingerprints:
`R_b(o_b + y) · P_b(y) + P'_b(y) = Q_b(y) · w_{r_b}(y)` on `V_{r_b}`; the unused block: `R_u(o_u + y) = 1` (degree
`< 2^17`, so an identity of polynomials, no quotient).

**Root.** `T(1) · (β + fp(SEP_STATE, 1, 1)) = β + fp(SEP_STATE, g^(2^19 - 1), 1)`: push and pull products equal,
the state boundary included.

Each identity has its own quotient: with two commitments no challenge can batch identities that involve `C2` after
`C2` is fixed, and a batch drawn before it lets the prover trade errors between them (§9.3).

### 5.3 Leaf degrees (the leaf quotients' sizes)

A fingerprint is of degree 1 in the columns except address forms `fp·o` and the degree-2 values of MUL's product,
DEREF's store and JUMP's next state. With `F_T` flushes: `deg(R_b P_b) ≈ (1 + Σ_j deg D_j) n`, so
`deg Q_b ≈ Σ_j deg D_j · n`: XOR, MUL, DEREF, JUMP `8n`, SET `4n`, BLAKE2S `20n`, memory and bytecode `n`.

### 5.4 Counters nonzero

`z_T(y) Π_j c_j(y) + 1 = 0` on active rows: `(z_T Π_j c_j + 1) · Z_pad,T` vanishes on `V_{r_T}` (in `Q_W`), with
`Z_act,T(t) = Π_{bits b of rows_T} (w_b(t) + ω_{P_b >> b})` (`P_b` the prefix of `rows_T` above bit `b`) and
`Z_pad,T = w_{r_T} / Z_act,T`. leanVM's alternative (the count channel, a third product of all counters with
padding leaves 1) would add `5.5·2^18` count leaves to the heap (a heap of `2^24`) and the same counter values.

## 6. The constraint quotient `Q_W` (`C1` only, batched by `γ`)

On each table's domain, lifted to `V_21` by `w_21 / w_{r}`:
JUMP's two constraints; `padRow` (`(col - pad) · Z_act` for every column but `z_T`); the counters (§5.4); the
public input (`(mem_k - I_k) · w_21 / w_1`, `I_k` the line through the two public values of limb `k`); the limb
copies (`copy_j - ℓ_j`, `ℓ_j` the composition of `q_flock`'s limb slot `j`, §2). `Σ_i γ^i M_i W_i = Q_W · w_21`,
`deg Q_W ≈ 10.3 · 2^18` (BLAKE2S's counters).

## 7. BLAKE2s: Flock (owned by the Flock agent; details and measurements in `SPEC-FLOCK.md`)

Interface fixed here:
- Flock runs after `C1` and before `C2`: it reads only `C1`'s `q_flock` and the setup.
- It draws its own challenges in the transcript between `γ` and the `C2` root.
- It leaves (i) claims on `q_flock`, any number of weighted terms, joined into `C1`'s one claim, and (ii) claims on
  `A0` and `B0`.

What Flock reads and leaves (`crates/leanvm_flock_gas/src/flock_min.rs`, measured on revm at `log_n = 32`):
- **The skip (lever c).** leanVM's zerocheck has a univariate skip over the 6 packing bits. Here it is over
  `k ≤ 6` bits: `2^k` coset values, then `32 - k` rounds of 2 scalars, then `v_a` and `v_b`. The lincheck has 8
  rounds. The matrices' reduction has `k + 6` rounds, then `a` and `b`, as claims on `A0`, `B0`.
- **The slices (lever a).** The lincheck's 64 slices are not sent. The verifier needs only one combination
  `Σ_i μ_i ẑ(i, p) = κ` of them, with `μ` and `κ` known: the matrices' sumcheck carries their part of its claim
  linearly. That combination is `GF(2)`-linear in `q_flock`'s words, not `E`-linear. So it is a **bit-slice term**
  on `C1`, `(q_flock, p ∈ E^26, μ ∈ E^64)`, and `PCS_OPEN` ring-switches it inside the opening, as leanVM's
  `ring_switch_open` does.
- **Cost.** With `k = 4`, Flock reads 112 scalars (2,688 B) for 22,726 gas of execution. leanVM's verifier reads
  224 scalars for 193,108.
- **If `PCS_OPEN`'s terms must stay `E`-linear (lever a′).** Then the 64 slices are sent and the contract computes
  `T = Σ_i g^i Φ(s_i)`, which costs 66,288. The weight `Φ(eq(P, ·))` goes as 64 twisted terms, as first written
  here: 168 scalars at `k = 3`, 87,516 of execution.

**Floor.** Flock's two sumchecks (a zerocheck of `log_n` variables, a lincheck of 14, degree-2 rounds) read at least `2 (log_n + 14) + 4 = 96` scalars, 2.3 KB, about 92,000 gas at
EIP-7623's floor. The < 100K target for the whole PIOP therefore needs BLAKE2s out of the contract. Option B (no
sumcheck) cannot do it: it does not fit WHIR, `SPEC-B.md`. What could is an R1CS-validity claim type that the
block's builder proves.

## 8. The final check: values, relations, claims

**Values sent at `t`** (24 bytes each; the minimum that keeps every relation linear in what is not sent):

- per table: its pull fingerprints `D_j(t)` (one per flush), its counters `c_j(t)`, `fp(t)` (every address is
  `fp·o`), `pc(t)` (the state push `D' = D + eq(α,1)(g+1)pc`), and the factors of the other products: MUL `va_k`
  (3), DEREF `f_pc, f_fp, ptr`, JUMP `b, v_cond` and its state push `D'_state(t)` instead of `pc`;
- memory: `D_fin(t)`, `c_fin(t)`, the address `addr(t)` (on `F`); bytecode: `D_fin(t)`, `c_fin(t)`;
- `C2`: `T(t)` (a factor of the tree identity), `Q_W(t)` (so that `Q_W`'s relation is on `C1` alone).

Push fingerprints are derived (`D'_j = D_j + eq(α, 2)(g + 1) c_j` for counted flushes).

**Linear relations** (each `Σ coefficient · evaluation = value`, with the values above as coefficients):
on `C1`: every sent column value; every sent fingerprint (its tuple's columns at `t`); `Q_W`'s identity (the
padding, counter-inverse, JUMP `w`, limb-copy and public-input terms, and the 18 compositions `ℓ_j(t)` on `q_flock`);
Flock's claims on `q_flock`. On `C2`: the tree identity (`T(s(t)) + T(t)·T(t+1) + (w_23/w_1)(t) Q_tree(t) = 0`, three
terms); the root; each block's leaf identity (`P_b R_b(o_b + t) + w_{r_b}(t) Q_b(t) = P'_b`, two terms); the unused
block; `T(t)`, `Q_W(t)`. On `F`: `addr(t)`; the bytecode fingerprint (`eq(α,1) idx(t) + Σ_s eq(α,s) bc_s(t)`).

**Claims.** All relations on one commitment are combined with powers of `ρ` into **one weighted claim**: `C1`, `C2`,
`F` (+ `A0`, `B0` from Flock): 5 claims in 5 `PCS_OPEN` calls.

**`PCS_OPEN` with weighted claims** (an extension of `crates/evm/src/machine.rs`'s ABI; WHIR verifies a weighted
claim natively, leanVM's verifier hands its stack exactly that): words `root, layout, k, P`, then `P` points (each
`ℓ` then `ℓ` coordinates, a column's low coordinates), then per claim `m`, `m` terms (`(column, point, twist)` packed
in one word, then the coefficient), and the value. The layout names each column's place in the stack (its selector
coordinates) and whether it is E-valued. Price: `c` a claim; the precompile's cost grows with the terms (reported).

## 9. Soundness (`review/leanvm_univariate_params.py`)

Filled in by the script's output (§9 of the report). Ingredients: Schwartz–Zippel at `t` for each identity
(degree / `|E|`), union-bounded over the level-0 Johnson lists of `C1` and `C2` (`L_1 L_2`); the bus fingerprint
(α, β) over `C1`'s list; `γ` over `C1`'s list; `ρ` over all lists; Flock's terms as leanVM's.

## 10. Gas

Filled in from `tests/gas.rs`.

## 11. Prover (estimate)

Filled in.

## 12. Risks and open questions

Filled in.
