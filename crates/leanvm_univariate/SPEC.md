<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# A univariate PIOP for leanVM 42422001, for the EVM

**Status: milestone 1 done** (spec, soundness script, verifier-only gas prototype; no prover yet). Option A:
BLAKE2s by Flock's sumchecks, everything else univariate. §7 (Flock) is the Flock agent's, with details in
`SPEC-FLOCK.md`; option B (BLAKE2s without sumcheck) is in `SPEC-B.md` and does not fit WHIR. *Measured*: revm
runs of the contract compiled from the recorded Rust verifier (`tests/gas.rs`); *modelled*: computed here.

## 0. Summary

The statement is leanVM 42422001's: the same VM, the same six tables and their columns, the same bus tuples and
fingerprints, BLAKE2s by Flock, the same public input. The proof of it is different:

- **Two proof commitments**, `C1` and `C2`, and fixed setup commitments. `C1` holds the tables' columns (univariate:
  coefficients on Cantor subspaces) and Flock's `q_flock` (values, as in leanVM). `C2` comes after the bus
  challenges. It holds a **product heap** (the bus's grand product as a committed binary tree on Cantor cosets) and
  the quotients.
- **No GKR and no table sumcheck.** Every identity is a quotient identity checked at **one random point `t`**. The
  proof sends only the evaluations that occur in nonlinear terms (84 field elements), and every linear relation
  among evaluations is folded into claims.
- **The bus is a grand product** (exact multisets), not logUp. In characteristic 2, `Σ 1/(β + f)` only proves the
  multisets equal modulo 2: two identical fake reads cancel (§5.1).
- **Claims.** On the main line (`PCS_OPEN`'s ABI, point claims), one batching sumcheck over the three stacks turns
  every commitment's relations into one point claim. Extension W (weighted claims) drops that sumcheck.
- **Result at about 1M cycles** (1,000 signatures), transaction gas without the 21,000 base, EIP-7623, `c = 0`:
  **390,141** on the main line (ABI point claims, Flock (a′)), 246,160 with extension B (Flock's bit-slice claim),
  245,230 with extension W, 191,620 with both. The baseline (leanVM's GKR and Flock) costs **1,074,620**.
  Without BLAKE2s's argument the rest costs 139,030 (ABI) or 84,400 (W). The target of < 100K is out of reach with
  Flock: §10, §12.

## 1. Statement and workload

leanVM 42422001's `crates/verifier` is vendored and made generic in `crates/leanvm_flock_gas`. The statement: the VM,
run on the stacked bytecode (the fixed program) from `pc = 1, fp = 1`, halts at `pc = g^(2^19 - 1)`, `fp = 1`. The
32-byte public input is in memory cells 0 and 1, and every BLAKE2s precompile call is correct. In the Lean port
(`formal/Lv42`), this is `M3Holds` = `ConstraintsVanish ∧ Balanced ∧ CountsNonzero ∧ PublicLinesHold ∧ FlockRegion`,
under `Sizes.Admissible`.

- **Fields.** `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and `E = K[y]/(y^3 + y + 1)`, with `g = x` (`GEN`).
- **Tables** (leanVM's `layout.rs`): XOR (15 columns), MUL (15), SET (8), DEREF (15), JUMP (14), and BLAKE2S (37: 19
  own, and 18 value limbs that leanVM commits inside `q_flock`). Also memory (3 limbs and a final count, `2^lm`
  cells), bytecode (a final count, `2^lb` instructions) and `q_flock` (Flock's packed witness, `2^(h_B + 8)` K-words).
- **Bus** (leanVM's). Tuples have up to 16 coordinates, with fingerprint `β + Σ_s eq(α, s) τ_s` and `α ∈ E^4`.
  There are three channels: state, bytecode with counters, and memory with counters. The counters are powers of
  `g`. The push and pull multisets are equal, and every counter is nonzero. Framework blocks: the state boundary,
  the memory image (counts 1, final counts), the bytecode (counts 1, final counts). Padding rows push what they pull.
- **Constraints.** JUMP has two (`b + v_cond·w` and `v_cond·(b + 1)`), of degree 2. The other tables' rows are
  constrained by the bus only.

**Reference workload.** The largest execution of about 1M cycles, from leanVM's own `gas-dump` on h1
(`/root/pcs-quotient-fv/leanvm-univariate/`): **1,000 leanXMSS signatures, 1,023,109 cycles**. Table rows: XOR
183,266, MUL 195,439, SET 223,851, DEREF 137,591, JUMP 80,937, BLAKE2S 202,025 (log-heights 18 18 18 18 17 18).
Memory is `2^21`, the bytecode `2^19` instructions (`2^23` words), `q_flock` `2^26` words. leanVM's own stack
for it is `2^26.53` words. The other shapes (32 to 2,000 signatures) are leanVM's measured ones
(`leanvm_flock_gas::shapes`).

## 2. Domain and encodings

- **Cantor basis** of `K`: `β_0 = 1`, `s(β_{k+1}) = β_k`, `s(x) = x^2 + x` (`src/domain.rs`, as
  `crates/quotient/src/domain.rs`). Let `ω_i = Σ_k i_k β_k` and `V_r = {ω_i : i < 2^r}`. The digits are
  `w_0(x) = x`, `w_{k+1} = s(w_k)`. Then `w_r` is `V_r`'s subspace polynomial, `w_l(ω_i) = ω_{i >> l}`, and
  `w_m / w_r = Π_{j=r}^{m-1} (w_j + 1)`, a product with no division.
- **Basis `B`.** A column of `2^r` rows is the polynomial of degree `< 2^r` whose value at `ω_i` is row `i`. It is
  committed as its coefficients in `B_k = Π_l (w_l if k_l else 1 + w_l)`, a triangular transform of the novel basis
  (`B_k = Σ_{S ⊇ k} X_S`). Then **`f(t) = ĉ(w_0(t), …, w_{r-1}(t))`**: the multilinear claim's point is the digits
  themselves, with no inversion (the novel basis needs `w/(1+w)`).
- **Restriction to a coset.** For `F` of `2^m` coefficients and an aligned coset `o + V_r`, let
  `R(z) = Σ_k c_k B_{k mod 2^r}(z) B_{k - k mod 2^r}(o)`. It has degree `< 2^r` and agrees with `F` on the coset.
  `R(o + t)` is one claim on `F` at the *mixed point* `(w_{<r}(t) + w_{<r}(o), w_{≥r}(o))`. This is how one heap
  serves every block's identity.
- **Composition with values.** `q_flock`'s limbs are committed as values. Let `y_l` be the linearised polynomials
  `Σ_{m<r} a_{l,m} x^{2^m}` with `y_l(ω_i) = i_l` (the inverse Moore system, `domain::coordinate_functionals`). Then
  `ℓ(x) = ṽ(y_0(x), …, y_{r-1}(x))` agrees with the limb on `V_r` and has degree `≤ r 2^(r-1)`. `ℓ(t)` is one claim
  on the values at `y(t)`, for `r^2` products.
- **Vanishing polynomials of the active and padding rows.** `[0, rows)` and `[rows, 2^r)` are unions of aligned
  cosets. `Z_act(t)` and `Z_pad(t)` are products of `w_b(t) + ω_{a >> b}`, one per coset (`domain::prefix_vanishing`,
  `suffix_vanishing`).

## 3. Commitments

| commitment | when | content | words at 1,000 signatures |
|---|---|---|---:|
| setup `F` | once | the bytecode's 16 tuple slots on `V_19` (slot 0 `SEP_BYTECODE`, slot 1 the pc `g^i`, slot 2 zero, then the instruction); the memory's addresses `g^i` on `V_21` | `2^23.2` |
| setup `A0`, `B0` | once | Flock's BLAKE2s R1CS (as the baseline) | `2^28` each |
| `C1` | first | `q_flock` (values, `2^26`); every table column (basis `B`), BLAKE2S's 18 limbs again as columns (`copy_j`), and one counter-inverse column `z_T` per table; memory (4 columns, `V_21`); bytecode final count (`V_19`) | `2^26.62`, stack `2^27` |
| `C2` | after `α, β, γ` and Flock | the heap `T` (`2^23` E), `Q_tree`, one leaf quotient `Q_b` per heap block, the constraint quotient `Q_W`, each E-valued as three K-limb columns | `2^26.69`, stack `2^27` |

The setup roots are constants in the code (no `SLOAD`). The `C1` and `C2` roots are in calldata. Each commitment is
opened by **one** `PCS_OPEN` call. WHIR takes no OOD sample at level 0, so a root binds only a list of tables and
all claims on it must be checked together (AGENTS.md). `src/stacks.rs` gives each column an aligned block, largest
first. A claim reads only its column's block. Nothing relies on the stack's unused words, nor on the zero padding of
a column shorter than its lane, which leanVM's `Layout::new` does not force.

**Sizes over the shapes** (`review/leanvm_univariate_params.py`):

| signatures | 32 | 128 | 400 | **1,000** | 1,290 | 2,000 |
|---|---:|---:|---:|---:|---:|---:|
| `C1` stack | `2^22` | `2^24` | `2^26` | **`2^27`** | `2^27` | `2^28` |
| `C2` stack | `2^24` | `2^25` | `2^27` | **`2^27`** | `2^28` | `2^28` |

Both are under WHIR's `2^28` up to 2,000 signatures.

**Two additions to `C1`, both keeping leanVM's statement.** First, `copy_j` equals `q_flock`'s limb `j` on every
row (a constraint of `Q_W`). Second, `z_T · Π_j c_j = 1` on active rows (a constraint of `Q_W`) proves
`CountsNonzero`. leanVM proves it by a third product, of all counters. The alternative here is count leaves in the
heap, which doubles the heap (`2^24`) for no fewer values.

## 4. Transcript and challenges

The transcript is a Keccak-256 chain (`leanvm_flock_gas::transcript::KeccakChannel`). A challenge is one Keccak-256
of the state and the calldata bytes read since the last one. A scalar is 24 bytes, a root half 16. The seed is the
Keccak-256 of the name `leanVM-univar-v1`, the program's IV (which must bind the setup and the shape) and the public
input. There are no announced sizes: one shape per contract. The order:

1. The `C1` root. Then `α ∈ E^4` (the tuple weights), `β` (the fingerprint shift) and `γ` (the batching of
   `C1`-only constraints).
2. Flock (§7): its rounds, challenges and values.
3. The `C2` root, then `t`.
4. The values at `t` (§8).
5. `ρ`, which combines each commitment's relations.
6. On the main line: `λ`, which batches the three commitments, then the batching sumcheck's rounds and its three
   end values.

82 to 113 Keccak-256 calls (`KECCAK256`, 11–12 KB hashed), about 12,000 gas.

## 5. The bus as a product heap

### 5.1 Why not logUp

`Σ 1/(β + f)` over a multiset, in characteristic 2, sees each tuple's multiplicity modulo 2. Take two accesses at
one address with the same count, both reading the same fake value. They pull `(A, v', c)` twice and push
`(A, v', g c)` twice, and both pairs cancel. So a program that reads a cell twice can be made to read anything.

A sound logUp exists, but it is not used. Tag every push with its public position, and every pull with a committed
pointer to the push it consumes. Then the push side is a set, `#push = #pull`, and equality modulo 2 forces exact
equality (pigeonhole). It adds a column per flush and leaves leanVM's tuples.

### 5.2 Heap

`T` is one polynomial on `V_H` (`H = 23` at 1,000 signatures). Position `i` holds node `i` of a binary heap, with
children `2i` and `2i + 1` and the root at `1` (`ω_1 = 1`). The leaves are `[2^(H-1), 2^H)`. Since
`s(ω_i) = ω_{i>>1}`, the tree is one identity:

**Tree.** `w_1(t) (T(s(t)) + T(t) T(t+1)) + w_H(t) Q_tree(t) = 0`, where `Q_tree = Q_0 + w_H q_1` (degree
`2^H`). Here `T(s(t))` is at the digits `(w_1, …, w_H)` and `T(t + 1)` at `(w_0 + 1, w_1, …)`.

**Leaves.** The aligned blocks of `src/heap.rs`, largest first:

| block | leaves | leaf | at 1,000 signatures |
|---|---:|---|---|
| memory | `2^21` | `D_init / D_fin` of cell `i` | `[0, 2^21)` |
| bytecode | `2^19` | `D_init / D_fin` of instruction `i` | next |
| each table | its height | `Π_j D'_j / Π_j D_j` over its row's flushes | next |
| unused | the rest, in aligned blocks | 1 | 1 block of `2^17` |

The last column is the reference workload's. In general `HeapLayout::new` leaves the rest as several aligned unused
blocks (one per set bit of the gap), each with its own identity.

**Leaf identities**, each with its own quotient `Q_b`. The heap restricted to block `b` is `R_b`, read at the mixed
point (§2):

- table: `(R_b P_b + P'_b) Z_pad + (R_b + 1) Z_act = Q_b w_r`. On an active row `Z_act` vanishes and `Z_pad` does
  not, so the leaf is the ratio. On a padding row `Z_pad` vanishes and `Z_act` does not, so the leaf is 1, whatever
  the row holds. Padding rows are exempt from the bus: no constraint is placed on them, and none is needed (there is
  no `padRow` constraint).
- memory and bytecode: `R_b D_fin + D_init ≡ 0` mod `w_r`.
- unused: `R_u(o_u + t) = 1`. This is degree `< 2^r`, an identity of polynomials, with no quotient.

**Root.** `T(1) (β + fp(SEP_STATE, 1, 1)) = β + fp(SEP_STATE, g^(2^19 - 1), 1)`: the pushes' product equals the
pulls', the state boundary included. `T(1)` is a claim at the digits `(1, 0, …, 0)`. Read it as
`T(1) · fp(init) = fp(fin)`, a product, not as a division.

**Zero fingerprints need no exclusion.** Every heap identity only multiplies: a leaf is `R P = P'`, not `R = P'/P`.
So the bus's soundness argument (Balanced, the Lean heap proof `lean-heap`) needs no event "a pull fingerprint
vanishes", and the soundness script has no such term.

**The BLAKE2S leaves read the `copy_j` columns.** So the bus's soundness for BLAKE2S needs `Q_W`'s identity
`copy_j = ℓ_j` (§6): it ties the columns the leaves read to `q_flock`, which Flock checks. Every iteration keeps it.

**One quotient per identity.** With two proof commitments, nothing drawn after `C2` can batch the identities that
involve `C2`. A batch drawn before `C2` lets the prover trade errors between them: perturb two leaves at one point
and solve for the product.

### 5.3 Degrees

Each fingerprint is linear in the columns, except addresses `fp·o` and the products in MUL's result, DEREF's store
and JUMP's next state, which are degree 2. So `deg Q_b ≈ (Σ_j deg D_j) n + (n - rows)`. That gives XOR, MUL, DEREF
and JUMP `≈ 8.3 n`, SET `≈ 4.6 n`, BLAKE2S `≈ 20.2 n`, memory and bytecode `n`.

## 6. The constraint quotient `Q_W` (`C1` only, batched by `γ`)

Each constraint lives on its table's domain and is lifted to `V_{r_W}` (`r_W = 21`, the memory's) by
`w_21 / w_r = Π (w_j + 1)`:

- JUMP's two constraints, on all rows;
- the counters: `(z_T Π_j c_j + 1) Z_pad`;
- the public input: `(mem_k - I_k) Π_{j=1}^{20} (w_j + 1)`, where `I_k` is the line through limb `k`'s two public
  values (leanVM's public lines);
- the limb copies: `copy_j - ℓ_j`, with `ℓ_j` the composition of `q_flock`'s slot `j` (§2).

`Σ_i γ^i M_i W_i = Q_W w_21`, with `deg Q_W ≈ 10.2 · 2^18`, set by BLAKE2S's counters. Padding rows have no
constraint: the leaf identity exempts them (§5.2).

## 7. BLAKE2s: Flock (the Flock agent's; details and measurements in `SPEC-FLOCK.md`)

**Interface.** Flock runs after `C1` and before `C2`, reading only `C1`'s `q_flock` and the setup. It draws its own
challenges in the transcript between `γ` and the `C2` root. It leaves claims on `q_flock`, which join `C1`'s
relations, and claims on `A0` and `B0`. The verifier runs it as `leanvm_flock_gas::flock_min::verify(variant)`.

- **The skip (lever c).** leanVM's zerocheck has a univariate skip over the 6 packing bits. Here it is over `k ≤ 6`
  bits: `2^k` coset values, then `32 - k` rounds of 2 scalars, then `v_a` and `v_b`. The lincheck has 8 rounds. The
  matrices' reduction has `k + 6` rounds, then `a` and `b`, as claims on `A0` and `B0`.
- **(a′), the main line.** The 64 slices are sent, and the contract computes the ring switch's target
  `Σ_i g^i Φ(s_i)`. Its weight `Φ(eq(P, ·)) = Σ_k c_k eq(φ^k(P), ·)` is 64 Frobenius-twisted eq terms: an
  `E`-linear relation on `q_flock`. With `k = 3` that is 168 scalars and 87,516 gas of execution.
- **(a), extension B.** The slices are not sent. One combination `Σ_i μ_i ẑ(i, p) = κ` is left to a **bit-slice
  claim** that `PCS_OPEN` ring-switches inside the opening. This combination is `GF(2)`-linear in `q_flock`'s
  words, not `E`-linear, so it is a new claim type. With `k = 4` that is 112 scalars and 22,726 gas.
- **Floor.** Flock's two sumchecks read at least `2 (log_n + 14) + 4 = 96` scalars (2.3 KB, about 92,000 gas at
  EIP-7623's floor).

## 8. The final check: values, relations, claims

**Values sent at `t`** (84 at 1,000 signatures, 24 bytes each). These are the minimum that keeps every relation
linear in what is not sent:

- per table: its pull fingerprints `D_j(t)` whose tuple has an unsent column (29 in all); its counters `c_j(t)`
  (28); `fp(t)`; `pc(t)` (the state push is `D + eq(α,1)(g+1)pc`); and one factor of each other product (MUL
  `va_k`, DEREF `f_pc, f_fp, ptr`, JUMP `b, v_cond`, with JUMP's state push `D'_state(t)` sent instead of `pc`);
- memory: `D_fin(t)`, `c_fin(t)` and the address `addr(t)` (on `F`); bytecode: `D_fin(t)` and `c_fin(t)`;
- `C2`: `T(t)` (a factor of the tree identity) and `Q_W(t)` (so that `Q_W`'s relation is on `C1` alone).

Push fingerprints are derived: `D'_j = D_j + eq(α, 2)(g + 1) c_j` for a counted flush.

**Linear relations.** Each is `Σ coefficient · evaluation = value`, with the values above among the coefficients.
There are 96 to 97 of them.

- On `C1`: every sent column value; every sent fingerprint, as its tuple's columns at `t`; `Q_W`'s identity, with
  its `z_T`, JUMP `w`, copy, public-input and 18 composition terms; Flock's (a′) terms on `q_flock`.
- On `C2`: the tree (four terms), the root, each block's leaf identity (the heap at the mixed point and the quotient's
  chunks), the unused block, `T(t)` and `Q_W(t)`.
- On `F`: `addr(t)`, and the bytecode's fingerprint as **one** point, `(α, w_{<19}(t))`, on the 16-slot block.

Each commitment's relations are combined by the powers of `ρ`: `C1` has 197 terms, `C2` 42 and `F` 2.

**Claims, main line: `PCS_OPEN`'s ABI** (`crates/evm/src/machine.rs`: point claims, `c` each). A batching sumcheck
takes `Σ_k λ^k Σ_u W_k(u) C_k(u) = Σ_k λ^k v_k` over the longest stack (27 variables), the others zero-extended.
It has two scalars a round, then the three stacks' values at its point `r`. The verifier evaluates every `W_k(r)`.
Columns at one row point share their eq factor, selector factors share their high bits, and Frobenius twists are
cached (`stacks::EqCache`). The result is one point claim per commitment, plus `A0` and `B0`: 5 claims in 5 calls.
With Flock (a), `C1`'s call also carries the bit-slice claim, so 6 claims in 5 calls.

The alternative, route (i), sends every evaluation as its own point claim. That is about 177 values plus (a′)'s 64
twisted points: about 5.7 KB of values and some 240 claims against (ii)'s 1.4 KB and 5 claims. It is not built.

**Extension W: weighted claims.** A call is `root, layout, k`, then per claim its points (each a column's low
coordinates), its terms (`column | point << 32 | twist << 48`, then the coefficient) and its value. The precompile
evaluates the weight, as leanVM's own WHIR verifier does. No batching sumcheck. Price `c` a claim; the precompile's
work grows with the terms (197 + 42 + 2).

## 9. Soundness (`review/leanvm_univariate_params.py`)

Each challenge's error is a Schwartz–Zippel bound times the number of committed tables it is drawn against. That is
`L_1` before `C2` and `L_1 L_2` after it. The setup is honestly computed, and an honest codeword's list within the
Johnson radius is itself, so `L = 1` there. The lists are the certified level-0 lists of `lean-whir-large` (0aceeb1):
4,473 at a `2^27` stack, so `L_1 L_2 = 2^24.3`. At 1,000 signatures:

| round | error | bits alone | after the union |
|---|---|---:|---:|
| bus `(α, β)`: if the push and pull multisets differ, `Π(β + fp)` differs: one Schwartz–Zippel over `E^5`, degree 4 a factor, `N = 8,501,434 ≈ 2^23.02` tuples | `4N/|E|` | 167.0 | 154.9 |
| `γ`: `C1`-only constraints (29) batched | `28/|E|` | 187.1 | 175.0 |
| Flock (zerocheck, lincheck, matrices, ring map) | `≈ 2^8/|E|` | 183.8 | 171.7 |
| `t`: every identity (tree `2^24`, leaves, `Q_W`), `Σ deg ≈ 2^25.3` | `Σ deg/|E|` | 166.7 | **142.4** |
| `ρ` (relations into one claim) and `λ` and the batching sumcheck's 27 rounds | `≈ 2^7/|E|` | 185 | 160 |
| **all rounds** | | | **142.4** |

With the code's eta-search lists (216, which omit a row-union factor) the result is 151 bits. Under leanerVM's
generic cap `L ≤ 2^18` it is 130.7. A third proof commitment would leave 130.3 with the certified lists.

The table does not count WHIR's own soundness at each opening (leanVM's parameters), Fiat–Shamir (Keccak-256 as a
random oracle), or Flock's fixed zerocheck coordinates (leanVM's).

## 10. Gas (measured on revm; transaction gas computed from the calldata)

**At 1,000 signatures (1,023,109 cycles).** Transaction gas is EIP-7623's `max(16 B + execution, 40 B)` (zero bytes 4
and 10) and EIP-7976's 64 a byte. `c` is the price of a claim. "Straight" is the one straight-line contract.
"Deployed" is `crates/evm_link`'s contracts of at most 24,576 bytes. The ** cells add the 21,000 base.

| claims ABI × BLAKE2s | calldata | execution straight / deployed (contracts) | claims / calls | tx 7623 straight, `c` = 0 / 2K / 5K / 20K | tx 7623 deployed, `c` = 0 / 2K / 5K / 20K | tx 7976 deployed, `c` = 0 / 20K |
|---|---:|---|---:|---|---|---|
| **ABI points × (a′)** (main line) | 7,516 | 270,221 / 297,094 (4: 24,466, 24,441, 24,563, 19,402 B) | 5 / 5 | 390,141 / 400,141 / 415,141 / 490,141 | **417,014** / 427,014 / 442,014 / 517,014 | 481,024 / 517,014 |
| ABI points × (a) [ext. B] | 6,172 | 99,948 / 105,436 (2) | 6 / 5 | 246,160 / 246,160 / 246,160 / 318,412 | 246,160 / 246,160 / 246,160 / 323,900 | 395,008 / 395,008 |
| ext. W × (a′) | 6,148 | 139,640 / 154,663 (3) | 5 / 5 | 245,230 / 247,732 / 262,732 / 337,732 | 252,755 / 262,755 / 277,755 / 352,755 | 393,472 / 393,472 |
| ext. W × (a) [ext. B] | 4,804 | 71,381 / 82,659 (2) | 5 / 5 | 191,620 / 191,620 / 191,620 / 248,029 | 191,620 / 191,620 / 191,620 / 259,307 | 307,456 / 307,456 |
| *without BLAKE2s's argument*, ABI | 3,484 | 73,836 / 77,030 (2) | 3 / 3 | 139,030 / 139,030 / 144,448 / 189,448 | 139,030 / 139,030 / 147,642 / 192,642 | 222,976 / 222,976 |
| *without BLAKE2s's argument*, W | 2,116 | 43,214 / 43,214 (1) | 3 / 3 | 84,400 / 84,400 / 91,974 / 136,974 | 84,400 / 84,400 / 91,974 / 136,974 | 135,424 / 136,974 |
| baseline (leanVM's GKR, table sumcheck, Flock, stack batch) | 27,068 | 334,216 / — | 4 / 4 | 1,074,620 (all `c`) | | 1,732,352 |

\*\* With the base: add 21,000. The main line deployed at `c = 0` is 438,014, against the baseline's 1,095,620: 2.5×
less. Extension W with B is 212,620, 5.2× less.

**Where it goes (main line, straight, 1,000 signatures).**

| part | calldata bytes | execution |
|---|---:|---:|
| selector, public input, two roots | 100 | 46 (entry) |
| values at `t` (84 scalars) | 2,016 | bus fingerprints 5,539; heap identities 3,967; `Q_W` 10,681; combination 9,096; digits 913 |
| batching sumcheck (27 rounds, 3 values) | 1,368 | its rounds 1,161; **its weights at the point 135,240**, of which Flock (a′)'s 64 twisted terms are about 101,000 |
| Flock (a′), `k = 3` (168 scalars) | 4,032 | ring switch's map and target 70,521; matrices 6,241; rounds 2,561; skip 1,159 |
| shared | | transcript 12,100; calldata reads 6,616; `PCS_OPEN` calls 4,380 |
| **total** | **7,516** | **270,221** |

**The design choices' contributions** (1,000 signatures, at the floor's 40 a byte; execution counts when it binds):

| choice | calldata | execution | claims |
|---|---|---|---|
| GKR and table sumcheck → product heap and quotients | 20.1 KB → 2.0 KB of values (−724K at 40/B) | about −20K (bus, leaves, table terminal: ~50K → ~30K) | one more commitment: `C2` (5 claims with `A0`, `B0`) |
| point-claim ABI: batching sumcheck | +1.4 KB (+55K) | +34K, and +101K with (a′)'s twisted terms | 3 |
| extension W instead | 0 | −30K | 3, 241 terms |
| Flock (a′), `k = 3` | 4.0 KB (161K) | 87.5K | 2 (`A0`, `B0`) |
| Flock (a), `k = 4` [ext. B] | 2.7 KB (108K) | 22.7K | 3 |
| roots in code, no announced sizes | −8 scalars | −6.3K (no `SLOAD`) | |

**Over the shapes** (straight-line, tx EIP-7623 without the base, `c = 0`):

| signatures | 32 | 128 | 400 | **1,000** | 1,290 | 2,000 |
|---|---:|---:|---:|---:|---:|---:|
| ABI × (a′) | 357,958 | 369,983 | 388,543 | **390,141** | 395,531 | 398,809 |
| ext. W × (a) | 182,110 | 185,890 | 189,730 | **191,620** | 191,620 | 193,540 |
| baseline | 860,240 | 917,510 | 1,020,080 | **1,074,620** | 1,077,470 | 1,133,030 |

(Every cell is in `tests/gas.rs`'s report. The design is almost size-independent: values and Flock's rounds grow
only with the logarithms of the sizes.)

## 11. Prover (estimate, modelled; step 2 builds it)

At 1,000 signatures, against leanVM's 2.12 s for the whole proof on h1 (measured by its `gas-dump`):

- **`C1`.** An inverse additive NTT per table column (about 100 columns of `2^17`–`2^21`), then WHIR's commit of
  `2^27` words, as leanVM's. The copies are 18 more columns of `2^18`.
- **The heap and the leaves.** For every row of every table, the fingerprints and their products, one batch
  inversion (3 products a leaf), and the heap's `2^22` products. This is like leanVM's GKR leaf layer, without its
  layers' sumchecks.
- **The quotients**, the dominant cost. Each table's columns are evaluated on a coset of size `≥ deg + 1`: `2^22`,
  or `2^23` for BLAKE2S (21 n). That is about 39 × `2^23` (BLAKE2S) plus 5 × 15 × `2^22` K-values, roughly `2^33`
  butterfly operations. Then the fingerprints' products there, and one E-NTT per quotient back to coefficients.
  `Q_tree` needs `T` on a coset of `2^24`.
- **The compositions `ℓ_j`.** On a coset `c + V_22`, `y(c + V_22)` is 16 shifted boolean cubes. A multilinear on a
  shifted cube `Π_l {a_l, a_l + 1}` takes `18 · 2^18` operations, so `2^26` E-operations a limb and `2^30` in all.
- **`C2`.** WHIR's commit of `2^27` words, as `C1`.
- **The openings.** One per commitment. The batching sumcheck's prover is linear in the stacks (`2^27`).

**Estimate.** About 2–3× leanVM's time (5–7 s at 1,000 signatures, 16 cores), and about 2× its memory: two
committed stacks of `2^27` words at rate 1/2, plus the quotients' cosets, which can be built in chunks. leanVM itself
uses about 12 GB at 1,000 signatures.

**What step 2 needs.**

- a leanVM 42422001 fork that keeps its trace generation and Flock prover, and replaces the GKR and table sumcheck by
  this PIOP's `C1` (basis-`B` coefficients, copies, `z_T`), the heap, the quotients and `C2`;
- the prover side of the batching sumcheck (`stack.rs`'s, over three stacks);
- Flock (a′) or (a) as in `flock_min` (its prover: the skip size and, for (a), no slices);
- the same Keccak-256 transcript;
- tests: the real-trace proof accepted by `reduce`, and the contract's parity on it.

## 12. Risks and open questions

1. **The < 100K target is out of reach with Flock at `2^18` compressions.**
   - Flock's sumchecks alone are ≥ 96 scalars (92K at the floor).
   - The rest of the PIOP is 84 values (80.6K at the floor). That is the floor of this design: each value is a
     nonlinear factor, and the counters (28) are needed both for the push fingerprints and for `CountsNonzero`.
   - The cheapest configuration measured is extension W × (a): 191,620. Getting below 100K needs BLAKE2s out of the
     contract, e.g. an R1CS-validity claim type that the block's builder proves (`SPEC-FLOCK.md`).
2. **The main line pays for faithfulness in execution.**
   - The point ABI forces a batching sumcheck: +1.4 KB and +34K execution.
   - With (a′), the batch's weight carries the ring switch's 64 Frobenius-twisted eq terms: about 101K, the cost
     leanVM's verifier pays at WHIR's terminal point. Extension W moves it to the precompile, and B removes it.
   - Execution binds on the main line, so `c` shows at once (+5c).
3. **Extensions W and B are precompile changes.** Their price per claim should grow with the terms or the
   ring-switching work, which the table does not charge.
4. **Faithfulness deltas** (the statement is the same; to prove in milestone 4):
   - `CountsNonzero` by inverse columns `z_T` instead of leanVM's count product;
   - BLAKE2S's limbs committed twice, with `copy = ℓ(q_flock)` in `Q_W`;
   - padding rows unconstrained (the leaf identity forces their leaves to 1; no `padRow` constraint);
   - the bus as a committed heap instead of a GKR;
   - one shape per contract.

   `Balanced` (a `List.Perm`) follows from the heap's root as leanVM's GKR root gives it.
5. **Not built.**
   - **Lever (d)** (Flock's folded tables `a, b, c` in `C2`) is dropped. Each table is `2^26` E-values (`2^27.6`
     words), and three exceed `2^28`.
   - **Lever (e)** (the lincheck as a univariate sumcheck over `V_14`, its quotient and remainder of `2^14` in `C2`)
     is assessed only. It would replace the lincheck's 8 rounds and the matrices' 6 column rounds by `Q` and `R`,
     claims on `A0`, `B0` at `(r, y(t))` and `z(t)` through a bit-slice claim at a composed point: about −28
     scalars (−27K at the floor). The row side's Lagrange weights still need `k` rounds. Left for the Flock work.
   - **A third proof commitment** (one batched quotient for every `C2` identity) leaves 130.3 bits with the
     certified lists. It would shrink `C2` and its claim's terms, not the calldata.
6. **The soundness script is an analysis, not a proof.** It takes Flock's error as leanVM's, and assumes the
   batching sumcheck and `ρ` as standard. Fiat–Shamir over Keccak-256 is assumed.
7. **The gas is measured on random streams.** There is no prover yet. The code is straight-line with fixed-cost
   opcodes, so a valid proof costs the same.
   - Each measuring build jumps over failed checks: one `JUMPDEST` a check and a call, subtracted.
   - The contract equals the Rust verifier word for word, straight and deployed (`contract_is_the_rust_verifier`,
     `deployable_is_the_rust_verifier`).

## 13. Changes since milestone 1 (iteration 2, branch `leanvm-univariate-iter2`)

Each entry says what changed, why, and what the prover must change (none if the proof is unchanged).

1. **Text fixes from the Lean heap proof** (`lean-heap`; no change to the proof or the code):
   - §5.2 and §6: padding rows are exempt in the leaf identity `(R P + P') Z_pad + (R + 1) Z_act = Q w_r` (the code
     since 56ea040); there is no `padRow` constraint.
   - §5: the root is `T(1) · fp(init) = fp(fin)`, a product; zero fingerprints need no exclusion, since every heap
     identity only multiplies.
   - §5.2: the leaf table is the reference workload's; `HeapLayout::new` can leave several unused blocks.
   - §9 and `review/leanvm_univariate_params.py`: the bus error is `4N/|E|` (one Schwartz–Zippel over `E^5`, degree
     4 a factor), `N = 8,501,434 ≈ 2^23.02` at the reference workload: `2^-166.98` alone, `2^-154.9` over `C1`'s list
     4,473. The "no pull fingerprint vanishes" term is gone.
   - §5.2: the BLAKE2S leaves read the `copy_j` columns, so the bus's soundness for BLAKE2S needs `Q_W`'s
     `copy_j = ℓ_j`. Every iteration keeps that constraint.

   Prover: nothing.

2. **Lever 1a: the ring map in tower order** (`leanvm_flock_gas::ring_tower`, `Slices::Tower`, the main line's
   `FLOCK_MAIN`). The map's six stages are applied shift 1 first, 32 last (leanVM: 32 first). The outermost stage is
   then `GF(2^32)`-linear, the next `GF(2^16)`-linear, and so on, so the target `Σ_i x^i Φ(s_i)` is computed through
   `K`'s subfields: 64 sums of slices (the coordinates of `x^i` in a tower basis, 1,938 slice terms), then six levels
   with `6 · 64` squarings and `3 · 63` products, against `64 · 63` squarings. On the main line the ring-switch term
   is one term of `C1`'s relations ([`RING_TWIST`]), whose weight at the batch's point is computed from the inside
   out (the 64 twisted eq products, then 63 products and the chains `f_j^(2^k)`; no coefficients `d_k`). Each eq
   factor is `(1 + r_k) + p_k`, with `1 + r_k` shared. The map's error is at most `6/|E|` (SPEC-FLOCK's leanVM order:
   `2^31/|E|` by Schwartz–Zippel): a node of the tower is `(A + θB) + f_j(A^q + θB^q)`, which vanishes for at most one
   `f_j` unless both children do.
   Measured at 1,000 signatures, main line: straight 270,221 → 203,829; deployed 297,094 → 216,116 (4 contracts);
   tx (EIP-7623, `c = 0`) 417,014 → 336,036. Target 70,521 → 26,832; twisted weight ~101,000 → 81,850. Ext. W × (a′):
   139,640 → 101,820 straight.
   Prover: the ring map's stages in the order shift 1, 2, 4, 8, 16, 32 (the same six challenges, drawn as before):
   `Φ(a)` applies `a ← a + f_j a^(2^(2^j))` for `j = 0..5`, and the weight is `Φ(eq(p, u))` with that `Φ`.

3. **Lever 1b: the tower's leaves as an `XOR` network** (Paar's greedy common subexpressions, `ring_tower::Tower`):
   1,938 slice terms become 767 `XOR`s (251 shared). Measured, main line straight: 203,829 → 196,524 (target
   26,832 → 19,542). Prover: nothing.
