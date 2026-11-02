-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Witness
import UniComplete.Claims
import Lv42.Protocol.FlockSpec

/-!
# What an honest trace satisfies, and the bad bus challenges

**`TraceHonest tr`**: the properties of a placed trace from which every quotient divides exactly, fits its chunks,
and every relation the verifier states holds (the algebra's hypotheses; `honestTrace` of an `M3Honest` witness at
row counts that fit has them, the mapping's theorem):

* the shape is valid, the row counts fit (`RowsFit`), every column has its size, the setup's fixed slots;
* JUMP's two constraints vanish on every row (`b + v_cond w`, `v_cond (b + 1)`);
* every row's counters are nonzero (`z_T` inverts them, `z_T Π c + 1` vanishes);
* BLAKE2S's limb columns are `q_flock`'s slots, row `i` at word `slot + 256 i`;
* the memory's cells `0`, `1` hold the public input's lines (limbs `0`, `1`; limb `2` zero);
* **the bus balances**: the pushed tuples (each table's active rows' push tuples, the memory's cells with count `1`,
  the bytecode's instructions with count `1`, the state's `(SEP_STATE, 1, 1)`) are a permutation of the pulled
  ones (the active rows' pull tuples, the memory's with its final counts, the bytecode's with its, the state's
  `(SEP_STATE, g^(2^lb − 1), 1)`), each tuple its 16 coordinates (`tupleAt`, zero-padded);
* Flock's R1CS holds of `q_flock`'s bits, block by block (`FlockRegion.Holds` of leanVM's BLAKE2s R1CS).

**`BadFp tr α β`**: some fingerprint the heap divides by vanishes: an active row's pull tuple, a memory cell's or an
instruction's final tuple. For each `α` at most `pullCount tr` values of `β` (one per tuple).
-/

namespace UniComplete

open UniStatement LeanVM.Parameters

/-- A tuple's 16 coordinates at a row (zero-padded): `τ_s = form_s(row)`. -/
def tupleAt (tuple : List Form) (col : ℕ → E) : List E :=
  (List.range 16).map fun s ↦ formE (tuple.getD s []) col

/-- The fingerprint of 16 coordinates: `β + Σ_s eq(α, s) τ_s`. -/
def fpOf (weights : Array E) (beta : E) (tau : List E) : E :=
  (List.range 16).foldl (fun acc s ↦ acc + weights.getD s 0 * tau.getD s 0) beta

/-- Table `t`'s active rows, in increasing position. -/
def activeRows (tr : Trace) (t : ℕ) : List ℕ :=
  (List.range (2 ^ tr.height t)).filter fun i ↦ isActive i (tr.rows.getD t 0) (tr.height t)

/-- A memory cell's tuple at count `count`: `(SEP_MEM, g^i, count, limbs)`. -/
def memoryTuple (tr : Trace) (i : ℕ) (count : E) : List E :=
  [sepMem, ofK (LeanVM.Parameters.gpow i), count] ++
    (List.range 3).map (fun k ↦ ofK ((tr.memory.getD k #[]).getD i 0)) ++ List.replicate 10 0

/-- An instruction's tuple at count `count`: its 16 slots, slot `2` the count. -/
def bytecodeTuple (tr : Trace) (i : ℕ) (count : E) : List E :=
  (List.range 16).map fun s ↦ bytecodeSlot tr i s count

/-- The state's tuple at `pc`: `(SEP_STATE, pc, 1)`. -/
def stateTuple (pc : E) : List E := [sepState, pc, 1] ++ List.replicate 13 0

/-- **The pushed tuples**. -/
def pushTuples (tr : Trace) : List (List E) :=
  ((List.range 6).flatMap fun t ↦ (tables.getD t default).flushes.push.flatMap fun tuple ↦
      (activeRows tr t).map fun i ↦ tupleAt tuple (tr.cell t · i)) ++
    (List.range (2 ^ tr.shape.logMemory)).map (fun i ↦ memoryTuple tr i 1) ++
    (List.range (2 ^ tr.shape.logBytecode)).map (fun i ↦ bytecodeTuple tr i 1) ++
    [stateTuple 1]

/-- The pulled tuples the heap divides by: the active rows' pull tuples, the memory's and the bytecode's final
tuples. -/
def dividedTuples (tr : Trace) : List (List E) :=
  ((List.range 6).flatMap fun t ↦ (tables.getD t default).flushes.pull.flatMap fun tuple ↦
      (activeRows tr t).map fun i ↦ tupleAt tuple (tr.cell t · i)) ++
    (List.range (2 ^ tr.shape.logMemory)).map (fun i ↦
      memoryTuple tr i (ofK ((tr.memory.getD 3 #[]).getD i 0))) ++
    (List.range (2 ^ tr.shape.logBytecode)).map (fun i ↦
      bytecodeTuple tr i (ofK (tr.bytecodeFinal.getD i 0)))

/-- **The pulled tuples**: the divided ones and the state's final `(SEP_STATE, g^(2^lb − 1), 1)`. -/
def pullTuples (tr : Trace) : List (List E) :=
  dividedTuples tr ++ [stateTuple (gpow (2 ^ tr.shape.logBytecode - 1))]

/-- The public input's four words, in `K` (`publicWordsOf`'s). -/
def publicK (tr : Trace) (k : ℕ) : K := K.ofLane (beWordAt tr.publicInput.toArray (8 * k))

/-- `q_flock` as Lv42's column of `2^(8 + h_B)` words (instances in the PIOP's order). -/
def qflockColumn (tr : Trace) : LeanVM.Protocol.Column (Lv42.Parameters.Flock.kIn + tr.height 5) :=
  ⟨Vector.ofFn fun u ↦ tr.qflock.getD u.val 0⟩

/-- **The properties of an honest placed trace.** -/
structure TraceHonest (tr : Trace) : Prop where
  valid : tr.shape.Valid
  rowsFit : tr.shape.RowsFit tr.rows
  tablesSize : tr.tables.length = 6 ∧ ∀ t < 6, (tr.tables.getD t []).length = (tables.getD t default).width ∧
    ∀ c < (tables.getD t default).width, (tr.column t c).size = 2 ^ tr.height t
  memorySize : tr.memory.length = 4 ∧ ∀ k < 4, (tr.memory.getD k #[]).size = 2 ^ tr.shape.logMemory
  bytecodeSize : tr.bytecodeFinal.size = 2 ^ tr.shape.logBytecode
  qflockSize : tr.qflock.size = 2 ^ (tr.height 5 + 8)
  slotsSize : tr.slots.length = 16 ∧ ∀ s < 16, (tr.slots.getD s #[]).size = 2 ^ tr.shape.logBytecode
  slotsFixed : ∀ i < 2 ^ tr.shape.logBytecode, (tr.slots.getD 0 #[]).getD i 0 = K.ofBits 4 ∧
    (tr.slots.getD 1 #[]).getD i 0 = LeanVM.Parameters.gpow i ∧ (tr.slots.getD 2 #[]).getD i 0 = 0
  publicSize : tr.publicInput.length = 32
  jump : ∀ i < 2 ^ tr.height opJump,
    let col (n : String) : K := (tr.column opJump (colIdx jumpColumns n)).getD i 0
    col "b" + col "v_cond" * col "w" = 0 ∧ col "v_cond" * (col "b" + 1) = 0
  counters : ∀ t < 6, ∀ i < 2 ^ tr.height t,
    (tables.getD t default).countColumns.foldl (fun acc c ↦ acc * (tr.column t c).getD i 0) 1 ≠ 0
  copies : ∀ i < 2 ^ tr.height opBlake2s, ∀ c < blake2sColumns.length, ∀ slot,
    qflockSlot (blake2sColumns.getD c "") = some slot →
      (tr.column opBlake2s c).getD i 0 = tr.qflock.getD (slot + 256 * i) 0
  publicLines : (tr.memory.getD 0 #[]).getD 0 0 = publicK tr 0 ∧ (tr.memory.getD 0 #[]).getD 1 0 = publicK tr 2 ∧
    (tr.memory.getD 1 #[]).getD 0 0 = publicK tr 1 ∧ (tr.memory.getD 1 #[]).getD 1 0 = publicK tr 3 ∧
    (tr.memory.getD 2 #[]).getD 0 0 = 0 ∧ (tr.memory.getD 2 #[]).getD 1 0 = 0
  bus : (pushTuples tr).Perm (pullTuples tr)
  flock : Lv42.Protocol.BlockR1CS.BatchHolds Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs
    Lv42.Parameters.Flock.constPos (Lv42.Protocol.bitTable (qflockColumn tr))

/-- **The bad bus challenges**: a fingerprint the heap divides by vanishes. -/
def BadFp (tr : Trace) (alphas : List E) (beta : E) : Prop :=
  ∃ tau ∈ dividedTuples tr, fpOf (eqKernel alphas) beta tau = 0

end UniComplete
