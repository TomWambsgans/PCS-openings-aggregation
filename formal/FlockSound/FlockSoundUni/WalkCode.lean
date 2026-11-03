-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The walk is `formal/UniStatement`'s
-- (`UniStatement/Rec.lean`: `Flock.blake2sRowValues`, `Flock.walkAdd`, `Flock.walkAdd3`, `Flock.walkedTerminal`),
-- transcribed there from `crates/leanvm_flock_gas/src/flock.rs` (`RowValues`, `blake2s_row_values`, adapted from
-- leanVM 42422001's `crates/verifier/src/flock.rs`) and `flock_min.rs` (`walked_terminal`).
import UniStatement.Rec
import FlockSoundUni.Transcription

/-!
# The walked terminal's code as folds

π1-rec3's verifier (`Slices::TowerWalk`, `flock_min::verify_walked`) checks Flock's lincheck terminal against
`walked_terminal` (`flock_min.rs:185-215`), which walks the BLAKE2s circuit once (`flock.rs:318-388`,
`blake2s_row_values`, with `RowValues::{slots, literal, add, add3, linear_rows}`, `xor`, `rotate_right` at
`flock.rs:239-316`). The proof is about the **official transcription** of that code, `UniStatement.Rec`'s
`Flock.blake2sRowValues`, `Flock.walkAdd`, `Flock.walkAdd3` and `Flock.walkedTerminal` (`lean-rec-graph` def3bb3).

**Decision (recorded):** the brief first asked for a transcription of our own here; the official one landed meanwhile,
so this module transcribes nothing. It restates the official definitions as `List.foldl`s over named step functions
(`addModel`, `add3Model`, `rowModel`, `colWeights`, `matrixSum`) and proves them equal to the official ones
(`walkAdd_eq`, `walkAdd3_eq`, `blake2sRowValues_eq`, `walkedTerminal_eq`), so that `Walk.lean` reasons about folds.

How the equalities are proved, without evaluating anything:

* a `for` loop in `Id` whose body always yields is a `List.foldl` (`forIn_list_eq`, `forIn_range0_eq`; and with the
  body's own value as the step, `forIn_list_value`, `forIn_range0_value`, `forIn_range_value`);
* `walkAdd`, `walkAdd3` (bodies with `if`s): their loops are rewritten with the named steps, each step checked by
  cases on its condition;
* `blake2sRowValues`, `walkedTerminal` (no `if` in a body): every loop is rewritten with its body's value as the step,
  without unfolding the bodies' `have`s (`zeta := false`: unfolding them would copy each gadget's result into all its
  uses), and the result is the model **by definitional unfolding** (`rfl`), with `List.foldl`, the lists, the arrays
  and the walk's word operations irreducible so that nothing is unrolled. The models re-tuple each loop's state as
  the `do` notation does (`(st.1, st.2)` for `st`), so that the kernel compares the folds argument by argument.
-/

namespace FlockSound.Uni.Walk

open UniStatement UniStatement.Flock LeanVM.Parameters

/-! ## `for` loops in `Id` as folds -/

theorem forIn_list_eq {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (g : β → α → β)
    (h : ∀ a b, f a b = pure (ForInStep.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    rw [List.forIn_cons, h, List.foldl_cons, ← ih]
    rfl

theorem forIn_range0_eq {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) (g : β → ℕ → β)
    (h : ∀ i b, f i b = pure (ForInStep.yield (g b i))) :
    forIn [:n] init f = pure ((List.range' 0 n).foldl g init) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_list_eq _ _ _ g fun a b ↦ h a b]
  congr 2
  simp [Std.Legacy.Range.size]

theorem forIn_list_value {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (h : ∀ a b, ∃ c, f a b = pure (ForInStep.yield c)) :
    forIn l init f = pure (l.foldl (fun b a ↦ (Id.run (f a b)).value) init) := by
  refine forIn_list_eq l init f _ fun a b ↦ ?_
  obtain ⟨c, hc⟩ := h a b
  rw [hc]
  rfl

theorem forIn_range0_value {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (h : ∀ a b, ∃ c, f a b = pure (ForInStep.yield c)) :
    forIn [:n] init f = pure ((List.range' 0 n).foldl (fun b a ↦ (Id.run (f a b)).value) init) := by
  refine forIn_range0_eq n init f _ fun a b ↦ ?_
  obtain ⟨c, hc⟩ := h a b
  rw [hc]
  rfl

theorem forIn_range_value {β : Type} (a n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (h : ∀ a b, ∃ c, f a b = pure (ForInStep.yield c)) :
    forIn [a:a + n] init f = pure ((List.range' a n).foldl (fun b i ↦ (Id.run (f i b)).value) init) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_list_value _ _ _ h]
  congr 2
  simp [Std.Legacy.Range.size]

/-! ## `RowValues::add` (`flock.rs:255-276`) -/

/-- One bit of `walkAdd`: the carry row `(x_i + c, y_i + c)` at `cb + i` for `i < 31`, the sum's bit, the carry
updated by the row's slot. The state: left, right, the carry, the output. -/
def addStep (cw : Array E) (x y : WalkWord) (cb : ℕ) (st : Array E × Array E × E × Array E) (bit : ℕ) :
    Array E × Array E × E × Array E :=
  (if bit < 31 then st.1.set! (cb + bit) (x.getD bit 0 + st.2.2.1) else st.1,
   if bit < 31 then st.2.1.set! (cb + bit) (y.getD bit 0 + st.2.2.1) else st.2.1,
   if bit < 31 then st.2.2.1 + cw.getD (cb + bit) 0 else st.2.2.1,
   st.2.2.2.set! bit (x.getD bit 0 + y.getD bit 0 + st.2.2.1))

/-- `walkAdd` as a fold. -/
def addModel (cw left right : Array E) (x y : WalkWord) (cb : ℕ) : Array E × Array E × WalkWord :=
  let st := (List.range' 0 32).foldl (addStep cw x y cb) (left, right, 0, Array.replicate 32 0)
  (st.1, st.2.1, st.2.2.2)

theorem walkAdd_eq (cw left right : Array E) (x y : WalkWord) (cb : ℕ) :
    walkAdd cw left right x y cb = addModel cw left right x y cb := by
  unfold walkAdd addModel
  dsimp only
  rw [forIn_range0_eq 32 _ _ (addStep cw x y cb)]
  · rfl
  · intro i b
    by_cases h : i < 31 <;> simp [h, addStep]

/-! ## `RowValues::add3` (`flock.rs:278-299`) -/

/-- One bit of `walkAdd3`'s majority layer: the row `(x_i + z_i, y_i + z_i)` at `base + i`, the majority
`w_(base+i) + z_i`. The state: left, right, the majorities. -/
def majStep (cw : Array E) (x y z : WalkWord) (base : ℕ) (st : Array E × Array E × Array E) (bit : ℕ) :
    Array E × Array E × Array E :=
  (st.1.set! (base + bit) (x.getD bit 0 + z.getD bit 0), st.2.1.set! (base + bit) (y.getD bit 0 + z.getD bit 0),
    st.2.2.set! bit (cw.getD (base + bit) 0 + z.getD bit 0))

/-- One bit of `walkAdd3`'s ripple layer: for `1 ≤ i ≤ 30` the row `(x_i + y_i + z_i + c, q_i + c)` at
`rb + i - 1` (`q_i` the majority `i - 1`, `q_0 = 0`) and the carry updated; the sum's bit. -/
def rippleStep (cw : Array E) (x y z : WalkWord) (maj : Array E) (rb : ℕ) (st : Array E × Array E × E × Array E)
    (bit : ℕ) : Array E × Array E × E × Array E :=
  (if 1 ≤ bit ∧ bit ≤ 30 then st.1.set! (rb + bit - 1) (x.getD bit 0 + y.getD bit 0 + z.getD bit 0 + st.2.2.1)
    else st.1,
   if 1 ≤ bit ∧ bit ≤ 30 then st.2.1.set! (rb + bit - 1)
      ((if bit = 0 then 0 else maj.getD (bit - 1) 0) + st.2.2.1) else st.2.1,
   if 1 ≤ bit ∧ bit ≤ 30 then st.2.2.1 + cw.getD (rb + bit - 1) 0 else st.2.2.1,
   st.2.2.2.set! bit (x.getD bit 0 + y.getD bit 0 + z.getD bit 0 + st.2.2.1 +
      (if bit = 0 then 0 else maj.getD (bit - 1) 0)))

/-- `walkAdd3` as two folds. -/
def add3Model (cw left right : Array E) (x y z : WalkWord) (base : ℕ) : Array E × Array E × WalkWord :=
  let m := (List.range' 0 31).foldl (majStep cw x y z base) (left, right, Array.replicate 31 0)
  let st := (List.range' 0 32).foldl (rippleStep cw x y z m.2.2 (base + 31)) (m.1, m.2.1, 0, Array.replicate 32 0)
  (st.1, st.2.1, st.2.2.2)

theorem walkAdd3_eq (cw left right : Array E) (x y z : WalkWord) (base : ℕ) :
    walkAdd3 cw left right x y z base = add3Model cw left right x y z base := by
  unfold walkAdd3 add3Model
  dsimp only
  rw [forIn_range0_eq 31 _ _ (majStep cw x y z base)]
  · simp only [pure_bind]
    rw [forIn_range0_eq 32 _ _ (rippleStep cw x y z _ (base + 31))]
    · rfl
    · intro i b
      by_cases h : 1 ≤ i ∧ i ≤ 30
      · have h0 : i ≠ 0 := by omega
        simp [h, h0, rippleStep]
      · simp [h, rippleStep]
  · intro i b
    rfl

/-! ## `blake2s_row_values` (`flock.rs:318-388`) -/

/-- One input row: `(w_row, w_512)`. -/
def inputRow (cw : Array E) (b : Array E × Array E) (i : ℕ) : Array E × Array E :=
  (b.1.set! i (cw.getD i 0), b.2.set! i (cw.getD constantColumn 0))

/-- The input rows `base … base + length − 1`. -/
def inputRows (cw : Array E) (b : Array E × Array E) (a : ℕ × ℕ) : Array E × Array E :=
  (((List.range' a.1 a.2).foldl (inputRow cw) (b.1, b.2)).1, ((List.range' a.1 a.2).foldl (inputRow cw) (b.1, b.2)).2)

/-- The initial working vector: `h`, `IV[0..4]`, `IV[4..8]` XOR the counter and the flags. -/
def initState (cw : Array E) : Array WalkWord :=
  let s := (List.range' 0 8).foldl (fun s word ↦ s.set! word (walkSlots cw (32 * word)))
    (Array.replicate 16 (Array.replicate 32 0))
  let s := (List.range' 0 4).foldl (fun s word ↦ s.set! (8 + word) (walkLiteral cw (blake2sIv.getD word 0))) s
  ([1152, 1184, 1216, 1248].zip (List.range 4)).foldl (fun s bw ↦
    s.set! (12 + bw.2) (walkXor (walkLiteral cw (blake2sIv.getD (4 + bw.2) 0)) (walkSlots cw bw.1))) s

/-- One mixing step `G` of round `roundIndex` (lanes `lg.1`, gate `lg.2` of the round): its 184 rows from
`1280 + 184 (8 roundIndex + lg.2)`, and the four lanes updated. The state: left, right, the working vector. -/
def gateStep (cw : Array E) (sigma : List ℕ) (roundIndex : ℕ) (st : Array E × Array E × Array WalkWord)
    (lg : List ℕ × ℕ) : Array E × Array E × Array WalkWord :=
  let gateBase := 1280 + 184 * (roundIndex * 8 + lg.2)
  let la := lg.1.getD 0 0
  let lb := lg.1.getD 1 0
  let lc := lg.1.getD 2 0
  let ld := lg.1.getD 3 0
  let a := st.2.2.getD la #[]
  let b := st.2.2.getD lb #[]
  let c := st.2.2.getD lc #[]
  let d := st.2.2.getD ld #[]
  let mx := walkSlots cw (640 + 32 * sigma.getD (2 * lg.2) 0)
  let my := walkSlots cw (640 + 32 * sigma.getD (2 * lg.2 + 1) 0)
  let r1 := walkAdd3 cw st.1 st.2.1 a b mx gateBase
  let d1 := walkRotr (walkXor d r1.2.2) 16
  let r2 := walkAdd cw r1.1 r1.2.1 c d1 (gateBase + 61)
  let b1 := walkRotr (walkXor b r2.2.2) 12
  let r3 := walkAdd3 cw r2.1 r2.2.1 r1.2.2 b1 my (gateBase + 92)
  let d2 := walkRotr (walkXor d1 r3.2.2) 8
  let r4 := walkAdd cw r3.1 r3.2.1 r2.2.2 d2 (gateBase + 153)
  let b2 := walkRotr (walkXor b1 r4.2.2) 7
  (r4.1, r4.2.1, (((st.2.2.set! la r3.2.2).set! lb b2).set! lc r4.2.2).set! ld d2)

/-- One round: its eight mixing steps. -/
def roundStep (cw : Array E) (st : Array E × Array E × Array WalkWord) (sr : List ℕ × ℕ) :
    Array E × Array E × Array WalkWord :=
  (((blake2sGLanes.zip (List.range blake2sGLanes.length)).foldl (gateStep cw sr.1 sr.2) (st.1, st.2.1, st.2.2)).1,
   ((blake2sGLanes.zip (List.range blake2sGLanes.length)).foldl (gateStep cw sr.1 sr.2) (st.1, st.2.1, st.2.2)).2.1,
   ((blake2sGLanes.zip (List.range blake2sGLanes.length)).foldl (gateStep cw sr.1 sr.2) (st.1, st.2.1, st.2.2)).2.2)

/-- One output row `(out_bit, w_512)` at `256 + 32 word + bit`. -/
def outBit (cw out : Array E) (word : ℕ) (st : Array E × Array E) (bit : ℕ) : Array E × Array E :=
  (st.1.set! (256 + 32 * word + bit) (out.getD bit 0), st.2.set! (256 + 32 * word + bit) (cw.getD constantColumn 0))

/-- The output word `h[w] ^ v[w] ^ v[w + 8]`. -/
def outWord (cw : Array E) (state : Array WalkWord) (word : ℕ) : Array E :=
  walkXor (walkXor (state.getD word #[]) (state.getD (word + 8) #[])) (walkSlots cw (32 * word))

/-- The output word's 32 rows. -/
def outStep (cw : Array E) (state : Array WalkWord) (st : Array E × Array E) (word : ℕ) : Array E × Array E :=
  (((List.range' 0 32).foldl (outBit cw (outWord cw state word) word) (st.1, st.2)).1,
   ((List.range' 0 32).foldl (outBit cw (outWord cw state word) word) (st.1, st.2)).2)

/-- **`blake2s_row_values` as folds**: the input rows, the working vector, ten rounds, the output rows, the
constant row. -/
def rowModel (cw : Array E) : Array E × Array E :=
  let st1 := [(0, 256), (640, 512), (1152, 128)].foldl (inputRows cw)
    (Array.replicate (2 ^ blake2sR1csLogSize) 0, Array.replicate (2 ^ blake2sR1csLogSize) 0)
  let st2 := (blake2sSigma.zip (List.range blake2sSigma.length)).foldl (roundStep cw)
    (st1.1, st1.2, initState cw)
  let st3 := (List.range' 0 8).foldl (outStep cw st2.2.2) (st2.1, st2.2.1)
  (st3.1.set! constantColumn (cw.getD constantColumn 0), st3.2.set! constantColumn (cw.getD constantColumn 0))

section
attribute [local irreducible] List.foldl walkAdd walkAdd3 walkSlots walkLiteral walkXor walkRotr Array.set!
  Array.replicate List.range List.range' List.zip blake2sSigma blake2sGLanes blake2sIv

set_option maxRecDepth 100000 in
/-- **The official walk is the model**, by unfolding (nothing evaluated: the folds, lists, arrays and word operations
are irreducible here). -/
theorem blake2sRowValues_eq (cw : Array E) : blake2sRowValues cw = rowModel cw := by
  unfold blake2sRowValues
  simp (config := { zeta := false }) (disch := exact fun _ _ ↦ ⟨_, rfl⟩) only [forIn_range0_value,
    forIn_range_value, forIn_list_value]
  rfl

end

/-! ## `walked_terminal` (`flock_min.rs:185-215`) -/

/-- The column weights `w[h·64 + l] = s_l · eq_kernel(chi_in')[h]`. -/
def colWeights (s : List E) (high : Array E) : Array E :=
  (List.range' 0 high.size).foldl (fun w h ↦ (List.range' 0 s.toArray.size).foldl
    (fun w l ↦ w.set! (h * kBits + l) (s.toArray.getD l 0 * high.getD h 0)) w)
    (Array.replicate (2 ^ blake2sR1csLogSize) 0)

/-- The matrix terms `Σ_h rows[h] (Σ_low lw[low] left[h·64 + low] + α Σ_low lw[low] right[h·64 + low])`. -/
def matrixSum (lw rows left right : Array E) (alpha : E) : E :=
  (List.range' 0 rows.size).foldl (fun m h ↦
    let st := (List.range' 0 lw.size).foldl (fun st low ↦
      (st.1 + lw.getD low 0 * left.getD (h * kBits + low) 0, st.2 + lw.getD low 0 * right.getD (h * kBits + low) 0))
      ((0 : E), (0 : E))
    m + rows.getD h 0 * (st.1 + alpha * st.2)) 0

/-- **The official walked terminal as folds.** -/
theorem walkedTerminal_eq (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) :
    walkedTerminal zSkip rowLow chiIn chiInPrime s alpha =
      matrixSum (rowLowWeights zSkip rowLow).2.toArray (eqKernel chiIn)
          (blake2sRowValues (colWeights s (eqKernel chiInPrime))).1
          (blake2sRowValues (colWeights s (eqKernel chiInPrime))).2 alpha +
        (knownWeights alpha chiIn chiInPrime).1 * dot (rowLowWeights zSkip rowLow).2 s +
        (knownWeights alpha chiIn chiInPrime).2 * s.getD (constantColumn % kBits) 0 := by
  unfold walkedTerminal
  simp (config := { zeta := false }) (disch := exact fun _ _ ↦ ⟨_, rfl⟩) only [forIn_range0_value]
  rfl

end FlockSound.Uni.Walk
