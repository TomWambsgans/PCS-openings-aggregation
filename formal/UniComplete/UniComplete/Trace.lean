-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `crates/leanvm_univariate/src/prover/{trace,
-- columns, stack, setup, fingerprint}.rs` (branch `leanvm-univariate-prover2`): the placed trace, `C1`'s and the
-- setup's polynomials and stacks, the bus fingerprints.
import UniComplete.Basic

/-!
# The placed trace, `C1`'s and the setup's stacks, the fingerprints

**The placed trace** (`Trace`, the Rust's `Trace` with `placed = true`): every table's columns as `2^h` values in
the univariate PIOP's row order (the executed rows at the fixed cosets of the count's set bits, `activePositions`;
padding rows elsewhere, their counters nonzero; BLAKE2S's limb columns the copies of `q_flock`'s slots), the
memory's four columns, the bytecode's final counts, `q_flock` (its instances with BLAKE2S's rows), the bytecode's
16 tuple slots (the setup's), the public input.

**A column** (`colPolyK`): its novel coefficients (`novelOfValuesK`, the additive transform) and its polynomial
(`ofNovel`); its basis-`B` coefficients are `bCoefficients` (UniStatement's `Mapping.lean`, what `C1` holds).

**The stacks** (`placeStack`): each column's words at its block of the verifier's layout (`c1Layout`, `layoutsOf`,
`setupLayout`), zeros elsewhere, `2^vars` words; `E`-valued columns limb by limb.

**The fingerprints** (`fpE`, `fpP`): `β + Σ_s eq(α, s) τ_s` of a tuple of forms, at a row's values or at the
columns' polynomials.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **The placed trace**: what the prover proves (the Rust's `Trace`, its rows placed). -/
structure Trace where
  shape : Shape
  rows : List ℕ
  /-- Per table (opcode order), per column, `2^h` values, rows at the PIOP's positions. -/
  tables : List (List (Array K))
  /-- The memory's limbs `0, 1, 2` and its final counts, `2^lm` each. -/
  memory : List (Array K)
  /-- The bytecode's final counts, `2^lb`. -/
  bytecodeFinal : Array K
  /-- `q_flock`, `2^(h_B + 8)` words, instance `i` at words `256 i …`. -/
  qflock : Array K
  /-- The bytecode's 16 tuple slots (slot 0 `SEP_BYTECODE`, 1 the pc `g^i`, 2 zero), `2^lb` each. -/
  slots : List (Array K)
  /-- The public input's 32 bytes. -/
  publicInput : List UInt8

/-- Column `c` of table `t`. -/
def Trace.column (tr : Trace) (t c : ℕ) : Array K := (tr.tables.getD t []).getD c #[]

/-- Table `t`'s height. -/
def Trace.height (tr : Trace) (t : ℕ) : ℕ := tr.shape.heights.getD t 0

/-! ### Columns -/

/-- The polynomial of a `K`-column of `2^r` values. -/
def colPolyK (r : ℕ) (v : Array K) : Poly := ofNovel r (novelOfValuesK r v)

/-- The polynomial of an `E`-column of `2^r` values. -/
def colPolyE (r : ℕ) (v : Array E) : Poly := ofNovel r (novelOfValuesE r v)

/-- **The counter-inverse column** `z_T` of a table (`c1_polys`): `(Π_j c_j)⁻¹` on every row (`0⁻¹ = 0`, never met
by an honest trace: its counters are nonzero on every row). -/
def inverseColumn (tr : Trace) (t : ℕ) : Array K :=
  let counters := (tables.getD t default).countColumns
  Array.ofFn (n := 2 ^ tr.height t) fun i ↦
    (counters.foldl (fun acc c ↦ acc * (tr.column t c).getD i.val 0) 1)⁻¹

/-- The memory's addresses `g^i`, `2^lm` (the setup's). -/
def addressColumn (lm : ℕ) : Array K := Array.ofFn (n := 2 ^ lm) fun i ↦ LeanVM.Parameters.gpow i.val

/-! ### Stacks -/

/-- **A stack of a layout**: `2^vars` words, each block's column limb at its offset (`Stack::put_k`, `put_e`), zero
elsewhere. `data column limb` is the block's words. -/
def placeStack (layout : StackLayout) (data : Column → ℕ → Array K) : Array K :=
  layout.blocks.foldl (fun (stack : Array K) (column, limb, vars, offset) ↦
    let words := data column limb
    (List.range (2 ^ vars)).foldl (fun s i ↦ s.set! (offset + i) (words.getD i 0)) stack)
    (Array.replicate (2 ^ layout.vars) 0)

/-- An `E`-column's limb `l` as `K`-words. -/
def limbWords (data : Array E) (l : ℕ) : Array K :=
  data.map fun x ↦ if h : l < 3 then x.limb ⟨l, h⟩ else 0

/-- **`C1`'s columns' words** (`prove`, step 1): every table column and `z_T` in basis `B` at the table's height,
the memory's four columns and the bytecode's final counts in basis `B`, `q_flock` as values. -/
def c1Words (tr : Trace) : Column → ℕ → Array K
  | .table t c, _ => bCoefficients (tr.height t) (tr.column t c)
  | .inverse t, _ => bCoefficients (tr.height t) (inverseColumn tr t)
  | .memory k, _ => bCoefficients tr.shape.logMemory (tr.memory.getD k #[])
  | .bytecodeFinal, _ => bCoefficients tr.shape.logBytecode tr.bytecodeFinal
  | .qflock, _ => tr.qflock
  | _, _ => #[]

/-- **`C1`'s stack**. -/
def c1Stack (tr : Trace) : Array K := placeStack (c1Layout tr.shape) (c1Words tr)

/-- The setup's 16 slots' basis-`B` coefficients and the addresses'. -/
def setupWords (tr : Trace) : Column → ℕ → Array K
  | .address, _ => bCoefficients tr.shape.logMemory (addressColumn tr.shape.logMemory)
  | _, _ => #[]

/-- **The setup stack** from the trace's slots (as `UniStatement.setupStack`: slot `s` of coefficient `k` at word
`s + 16 k` of the tuple block, the addresses' coefficients at theirs). -/
def setupStackOf (tr : Trace) : Array K :=
  let layout := setupLayout tr.shape
  let lb := tr.shape.logBytecode
  let lm := tr.shape.logMemory
  let slots : Array (Array K) := Array.ofFn (n := 16) fun s ↦ bCoefficients lb (tr.slots.getD s.val #[])
  let addresses := bCoefficients lm (addressColumn lm)
  let (_, _, tupleOffset) := (layout.limbs .bytecodeTuple).headD (0, 0, 0)
  let (_, _, addressOffset) := (layout.limbs .address).headD (0, 0, 0)
  Array.ofFn (n := 2 ^ layout.vars) fun w ↦
    let w := w.val
    if tupleOffset ≤ w ∧ w < tupleOffset + 2 ^ (lb + 4) then
      let j := w - tupleOffset
      (slots.getD (j % 16) #[]).getD (j / 16) 0
    else if addressOffset ≤ w ∧ w < addressOffset + 2 ^ lm then
      addresses.getD (w - addressOffset) 0
    else 0

/-! ### Fingerprints -/

/-- A form at a row's values: `Σ c Π_{j ∈ monomial} x_j`. -/
def formE (f : Form) (col : ℕ → E) : E :=
  f.foldl (fun acc (mono, c) ↦ acc + c * mono.foldl (fun p j ↦ p * col j) 1) 0

/-- A form at the columns' polynomials. -/
def formP (f : Form) (col : ℕ → Poly) : Poly :=
  f.foldl (fun acc (mono, c) ↦ acc + pC c * mono.foldl (fun p j ↦ p * col j) 1) 0

/-- **A tuple's fingerprint** `β + Σ_s eq(α, s) τ_s` at a row's values (`Fingerprint::at`). -/
def fpE (tuple : List Form) (weights : Array E) (beta : E) (col : ℕ → E) : E :=
  (tuple.zip (List.range tuple.length)).foldl (fun acc (f, s) ↦ acc + weights.getD s 0 * formE f col) beta

/-- A tuple's fingerprint at the columns' polynomials. -/
def fpP (tuple : List Form) (weights : Array E) (beta : E) (col : ℕ → Poly) : Poly :=
  (tuple.zip (List.range tuple.length)).foldl (fun acc (f, s) ↦ acc + pC (weights.getD s 0) * formP f col) (pC beta)

/-- The memory cell's fingerprint (`Bus::memory`): `β + fp(SEP_MEM, address, count, limbs)`. -/
def memoryFp (weights : Array E) (beta address count : E) (limbs : List E) : E :=
  (List.range 3).foldl (fun acc k ↦ acc + weights.getD (3 + k) 0 * limbs.getD k 0)
    (beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * address + weights.getD 2 0 * count)

/-- The instruction's fingerprint (`Bus::bytecode`): `β + Σ_s eq(α, s) slot_s`, slot `2` the count. -/
def bytecodeFp (weights : Array E) (beta : E) (slot : ℕ → E) : E :=
  (List.range 16).foldl (fun acc s ↦ acc + weights.getD s 0 * slot s) beta

/-- `β + fp(SEP_STATE, pc, 1)` (`Bus::state`). -/
def stateFp (weights : Array E) (beta pc : E) : E :=
  beta + weights.getD 0 0 * sepState + weights.getD 1 0 * pc + weights.getD 2 0

end UniComplete
