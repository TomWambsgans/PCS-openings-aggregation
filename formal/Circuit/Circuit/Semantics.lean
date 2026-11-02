/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-/
import Circuit.Defs

/-!
# What the builder's rows compute

The meaning of a builder is relational: a valuation `v` of the rows' outputs *satisfies* it
(`Sat v b`) when every row from `512` on has the output its gate gives (an input row reads its own
output three times, and `gateBits v v v = v`, so its value is free). A gadget *computes* `f` with
its result `a` (`Computes b a f`) when `a` reads `f v` under every valuation satisfying the builder.
Since a gadget only appends rows, a valuation satisfying a later builder satisfies every earlier one
(`Sat.of_ext`), so what a gadget computes stays computed.

A run of a gadget is specified by `Spec m b k P`: from `b`, the builder grows (`Grows`: the rows of
`b` kept, at most `k` added, the inputs kept, well-formed), and the result satisfies `P`.
Well-formed (`WF`) is the loop-freeness the soundness argument needs: an input row reads its own
output in `X, Y, C`, every other row from `512` on reads constants or rows from `512` on before it.
`Spec.bind`, `Spec.mapM` compose them; `spec_row`, `spec_notG`, `spec_xorG`, `spec_chiG` are the
gadgets, their constant folding included.
-/

namespace PcsCircuit

open Builder

/-! ## Arrays -/

theorem getD_push {α : Type} (a : Array α) (x d : α) (r : Nat) :
    (a.push x).getD r d = if r < a.size then a.getD r d else if r = a.size then x else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> split <;> simp_all

theorem toArray_getD {α : Type} (l : List α) (d : α) (k : Nat) : l.toArray.getD k d = l.getD k d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem toArray_getD_of_lt {α : Type} (l : List α) (d : α) (k : Nat) (h : k < l.length) :
    l.toArray.getD k d = l[k] := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem map_range_getD {α : Type} (f : Nat → α) (n k : Nat) (d : α) (h : k < n) :
    ((List.range n).map f).toArray.getD k d = f k := by
  simp [Array.getD_eq_getD_getElem?, h]

/-! ## Values -/

/-- The value a source reads, the rows' outputs being `v` (`circuit::read`). -/
def read (v : Nat → Bool) : Src → Bool
  | .zero => false
  | .one => true
  | .row r => v r

@[simp] theorem read_zero (v : Nat → Bool) : read v .zero = false := rfl
@[simp] theorem read_one (v : Nat → Bool) : read v .one = true := rfl
@[simp] theorem read_row (v : Nat → Bool) (r : Nat) : read v (.row r) = v r := rfl

/-- What a row's gate makes its output. -/
def Row.eval (v : Nat → Bool) (row : Row) : Bool := gateBits (read v row.x) (read v row.y) (read v row.c)

/-- `v` satisfies the gates of the rows from `512` on. -/
def Sat (v : Nat → Bool) (b : Builder) : Prop :=
  ∀ r, publicRows ≤ r → r < b.rows.size → v r = (b.rows.getD r .idle).eval v

/-- What row `r` may read: a constant, or a row from `512` on before `r`. -/
def Below (r : Nat) : Src → Prop
  | .row r' => publicRows ≤ r' ∧ r' < r
  | _ => True

/-- A source a new row of `b` may read. -/
def Valid (b : Builder) (s : Src) : Prop := Below b.rows.size s

/-- A source that is a row, not a constant. -/
def IsRow : Src → Prop
  | .row _ => True
  | _ => False

/-- `b'` has the rows of `b` first. -/
structure RowsExt (b b' : Builder) : Prop where
  size_le : b.rows.size ≤ b'.rows.size
  rows_eq : ∀ r < b.rows.size, b'.rows.getD r .idle = b.rows.getD r .idle

/-- `b'` extends `b`: the same rows first, the same inputs. -/
structure Ext (b b' : Builder) : Prop extends RowsExt b b' where
  inputs_eq : b'.inputs = b.inputs

theorem RowsExt.refl (b : Builder) : RowsExt b b := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem RowsExt.trans {b b' b'' : Builder} (h : RowsExt b b') (h' : RowsExt b' b'') : RowsExt b b'' :=
  ⟨Nat.le_trans h.size_le h'.size_le,
    fun r hr => (h'.rows_eq r (Nat.lt_of_lt_of_le hr h.size_le)).trans (h.rows_eq r hr)⟩

theorem Ext.refl (b : Builder) : Ext b b := ⟨RowsExt.refl b, rfl⟩

theorem Ext.trans {b b' b'' : Builder} (h : Ext b b') (h' : Ext b' b'') : Ext b b'' :=
  ⟨h.toRowsExt.trans h'.toRowsExt, h'.inputs_eq.trans h.inputs_eq⟩

theorem Sat.of_rowsExt {v : Nat → Bool} {b b' : Builder} (h : RowsExt b b') (hv : Sat v b') :
    Sat v b := by
  intro r h1 h2
  rw [hv r h1 (Nat.lt_of_lt_of_le h2 h.size_le), h.rows_eq r h2]

theorem Sat.of_ext {v : Nat → Bool} {b b' : Builder} (h : Ext b b') (hv : Sat v b') : Sat v b :=
  hv.of_rowsExt h.toRowsExt

theorem Below.mono {r r' : Nat} {s : Src} (h : r ≤ r') (hs : Below r s) : Below r' s := by
  cases s <;> simp_all [Below]
  omega

theorem Valid.of_rowsExt {b b' : Builder} {s : Src} (h : RowsExt b b') (hs : Valid b s) : Valid b' s :=
  Below.mono h.size_le hs

theorem Valid.of_ext {b b' : Builder} {s : Src} (h : Ext b b') (hs : Valid b s) : Valid b' s :=
  hs.of_rowsExt h.toRowsExt

/-- The builder is well-formed: the public rows are there, the inputs are rows from `512` on, in
increasing order, each reading its own output three times, and every other row from `512` on reads
constants or rows from `512` on before it. -/
structure WF (b : Builder) : Prop where
  size : publicRows ≤ b.rows.size
  sorted : b.inputs.toList.Pairwise (· < ·)
  input_range : ∀ r ∈ b.inputs, publicRows ≤ r ∧ r < b.rows.size
  input_row : ∀ r ∈ b.inputs, b.rows.getD r .idle = ⟨.row r, .row r, .row r⟩
  order : ∀ r, publicRows ≤ r → r < b.rows.size → r ∉ b.inputs →
    Below r (b.rows.getD r .idle).x ∧ Below r (b.rows.getD r .idle).y ∧ Below r (b.rows.getD r .idle).c

/-- `a` computes `f` in `b`: it is a source new rows may read, and it reads `f v` whenever `v`
satisfies `b`. -/
def Computes (b : Builder) (a : Src) (f : (Nat → Bool) → Bool) : Prop :=
  Valid b a ∧ ∀ v, Sat v b → read v a = f v

theorem Computes.of_rowsExt {b b' : Builder} {a : Src} {f : (Nat → Bool) → Bool} (h : RowsExt b b')
    (ha : Computes b a f) : Computes b' a f :=
  ⟨ha.1.of_rowsExt h, fun v hv => ha.2 v (hv.of_rowsExt h)⟩

theorem Computes.of_ext {b b' : Builder} {a : Src} {f : (Nat → Bool) → Bool} (h : Ext b b')
    (ha : Computes b a f) : Computes b' a f :=
  ha.of_rowsExt h.toRowsExt

/-- A constant computes itself. -/
theorem computes_zero (b : Builder) : Computes b .zero fun _ => false := ⟨trivial, fun _ _ => rfl⟩
theorem computes_one (b : Builder) : Computes b .one fun _ => true := ⟨trivial, fun _ _ => rfl⟩

/-- A valid source computes what it reads. -/
theorem Computes.self {b : Builder} {a : Src} (ha : Valid b a) : Computes b a fun v => read v a :=
  ⟨ha, fun _ _ => rfl⟩

theorem Computes.congr {b : Builder} {a : Src} {f g : (Nat → Bool) → Bool} (ha : Computes b a f)
    (h : ∀ v, Sat v b → f v = g v) : Computes b a g :=
  ⟨ha.1, fun v hv => (ha.2 v hv).trans (h v hv)⟩

/-! ## Runs -/

/-- Run a gadget from a builder. -/
def runB {α : Type} (m : BuildM α) (b : Builder) : α × Builder := (m.run b).run

/-- `b` grows to `b'` by at most `k` rows, keeping its rows and inputs, well-formed. -/
structure Grows (b b' : Builder) (k : Nat) : Prop where
  ext : Ext b b'
  le : b'.rows.size ≤ b.rows.size + k
  wf : WF b'

theorem Grows.trans {b b' b'' : Builder} {k k' : Nat} (h : Grows b b' k) (h' : Grows b' b'' k') :
    Grows b b'' (k + k') :=
  ⟨h.ext.trans h'.ext, by have := h.le; have := h'.le; omega, h'.wf⟩

theorem Grows.mono {b b' : Builder} {k k' : Nat} (h : Grows b b' k) (hk : k ≤ k') : Grows b b' k' :=
  ⟨h.ext, by have := h.le; omega, h.wf⟩

/-- The run of `m` from `b` grows `b` by at most `k` rows and its result satisfies `P`. -/
def Spec {α : Type} (m : BuildM α) (b : Builder) (k : Nat) (P : α → Builder → Prop) : Prop :=
  Grows b (runB m b).2 k ∧ P (runB m b).1 (runB m b).2

theorem runB_pure {α : Type} (a : α) (b : Builder) : runB (pure a : BuildM α) b = (a, b) := rfl

theorem runB_bind {α β : Type} (m : BuildM α) (f : α → BuildM β) (b : Builder) :
    runB (m >>= f) b = runB (f (runB m b).1) (runB m b).2 := rfl

theorem Spec.pure {α : Type} {a : α} {b : Builder} {k : Nat} {P : α → Builder → Prop} (hb : WF b)
    (h : P a b) : Spec (Pure.pure a : BuildM α) b k P :=
  ⟨⟨Ext.refl b, by simp [runB_pure], hb⟩, h⟩

theorem Spec.bind {α β : Type} {m : BuildM α} {f : α → BuildM β} {b : Builder} {k k' : Nat}
    {P : α → Builder → Prop} {Q : β → Builder → Prop} (hm : Spec m b k P)
    (hf : ∀ a b', Grows b b' k → P a b' → Spec (f a) b' k' Q) : Spec (m >>= f) b (k + k') Q := by
  obtain ⟨hg, hp⟩ := hm
  obtain ⟨hg', hq⟩ := hf _ _ hg hp
  rw [Spec, runB_bind]
  exact ⟨hg.trans hg', hq⟩

theorem Spec.mono {α : Type} {m : BuildM α} {b : Builder} {k k' : Nat} {P Q : α → Builder → Prop}
    (hm : Spec m b k P) (hk : k ≤ k') (h : ∀ a b', Grows b b' k → P a b' → Q a b') : Spec m b k' Q :=
  ⟨hm.1.mono hk, h _ _ hm.1 hm.2⟩

theorem Spec.wf {α : Type} {m : BuildM α} {b : Builder} {k : Nat} {P : α → Builder → Prop}
    (hm : Spec m b k P) : WF (runB m b).2 := hm.1.wf

/-- A property of a result that a builder's growth keeps. -/
def Mono {α : Type} (P : α → Builder → Prop) : Prop := ∀ a b b', Ext b b' → P a b → P a b'

/-- **A loop of gadgets.** `mapM` of a gadget that, from any growth of `b`, grows it by at most
`k` rows and gives a result satisfying `P x` (kept by growth): the results, one for each element,
satisfy `P`, and the builder grows by at most `k` rows an element. -/
theorem Spec.mapM {α β : Type} (f : β → BuildM α) (l : List β) (b : Builder) (k : Nat)
    (P : β → α → Builder → Prop) (hP : ∀ x, Mono (P x))
    (hf : ∀ x ∈ l, ∀ b', Ext b b' → WF b' → Spec (f x) b' k (P x)) (hb : WF b) :
    Spec (l.mapM f) b (k * l.length) fun as b' =>
      as.length = l.length ∧ ∀ i (hi : i < l.length) (hi' : i < as.length), P l[i] as[i] b' := by
  induction l generalizing b with
  | nil =>
    exact Spec.pure hb ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | cons x l ih =>
    rw [List.mapM_cons]
    have hk : k * (x :: l).length = k + (k * l.length + 0) := by simp [Nat.mul_succ]; omega
    rw [hk]
    refine Spec.bind (hf x (by simp) b (Ext.refl b) hb) fun a b' hg ha => ?_
    refine Spec.bind (ih b' (fun y hy b'' he hw => hf y (by simp [hy]) b'' (hg.ext.trans he) hw) hg.wf)
      fun as b'' hg' ⟨hlen, has⟩ => Spec.pure hg'.wf ⟨by simp [hlen], fun i hi hi' => ?_⟩
    cases i with
    | zero => exact hP x a b' b'' hg'.ext ha
    | succ i => exact has i (by simpa using hi) (by simpa using hi')

/-! ## The gadgets -/

theorem runB_row (x y c : Src) (b : Builder) :
    runB (row x y c) b = (.row b.rows.size, { b with rows := b.rows.push ⟨x, y, c⟩ }) := rfl

/-- **A row** computes the gate on what it reads. -/
theorem spec_row {x y c : Src} {b : Builder} (hb : WF b) (hx : Valid b x) (hy : Valid b y)
    (hc : Valid b c) :
    Spec (row x y c) b 1 fun a b' =>
      IsRow a ∧ Computes b' a fun v => gateBits (read v x) (read v y) (read v c) := by
  have hb1 := hb.size
  simp only [Spec, runB_row]
  have hext : Ext b { b with rows := b.rows.push ⟨x, y, c⟩ } :=
    ⟨⟨by simp, fun r hr => by simp only [getD_push, hr, ite_true]⟩, rfl⟩
  have hwf : WF { b with rows := b.rows.push ⟨x, y, c⟩ } := by
    refine ⟨by simp; omega, hb.sorted, fun r hr => ?_, fun r hr => ?_, fun r h1 h2 h3 => ?_⟩
    · have := hb.input_range r hr; simp; omega
    · have := hb.input_range r hr; simp only [getD_push, this.2, ite_true]; exact hb.input_row r hr
    · simp only [Array.size_push] at h2
      by_cases h : r < b.rows.size
      · simp only [getD_push, h, ite_true]; exact hb.order r h1 h h3
      · have : r = b.rows.size := by omega
        subst this
        simp only [getD_push, Nat.lt_irrefl, ite_false, ite_true]
        exact ⟨hx, hy, hc⟩
  refine ⟨⟨hext, by simp, hwf⟩, trivial, ⟨⟨hb1, by simp⟩, fun v hv => ?_⟩⟩
  have := hv b.rows.size hb1 (by simp)
  simpa [getD_push, Row.eval] using this

/-- The property of a gadget's result: it computes `f`, and it is a row when `row` holds. -/
def Out (row : Prop) (f : (Nat → Bool) → Bool) (a : Src) (b : Builder) : Prop :=
  (row → IsRow a) ∧ Computes b a f

theorem Out.mono (row : Prop) (f : (Nat → Bool) → Bool) : Mono (Out row f) :=
  fun _ _ _ h ⟨hr, hc⟩ => ⟨hr, hc.of_ext h⟩

/-- **NOT** (`Builder::not`): `¬a`, folded on a constant. -/
theorem spec_notG {a : Src} {b : Builder} (hb : WF b) (ha : Valid b a) :
    Spec (notG a) b 1 (Out (IsRow a) fun v => !read v a) := by
  cases a with
  | zero => exact Spec.pure hb ⟨fun h => h.elim, computes_one b⟩
  | one => exact Spec.pure hb ⟨fun h => h.elim, computes_zero b⟩
  | row r =>
    exact (spec_row (x := .one) (y := .zero) hb trivial trivial ha).mono (Nat.le_refl _) fun a b' _ ⟨hr, hc⟩ =>
      ⟨fun _ => hr, hc.congr fun v _ => by simp [gateBits]⟩

/-- **XOR** (`Builder::xor`): `a ⊕ c`, folded when either is a constant; a row when either is. -/
theorem spec_xorG {a c : Src} {b : Builder} (hb : WF b) (ha : Valid b a) (hc : Valid b c) :
    Spec (xorG a c) b 1 (Out (IsRow a ∨ IsRow c) fun v => read v a ^^ read v c) := by
  cases a with
  | zero =>
    cases c with
    | zero => exact Spec.pure hb ⟨fun h => by simp [IsRow] at h, computes_zero b⟩
    | one => exact Spec.pure hb ⟨fun h => by simp [IsRow] at h, computes_one b⟩
    | row r => exact Spec.pure hb ⟨fun _ => trivial, (Computes.self hc).congr fun v _ => by simp⟩
  | one =>
    cases c with
    | zero => exact Spec.pure hb ⟨fun h => by simp [IsRow] at h, computes_one b⟩
    | one => exact Spec.pure hb ⟨fun h => by simp [IsRow] at h, computes_zero b⟩
    | row r =>
      exact (spec_notG hb hc).mono (Nat.le_refl _) fun a b' _ ⟨hr, hc'⟩ =>
        ⟨fun _ => hr trivial, hc'.congr fun v _ => by simp⟩
  | row r =>
    cases c with
    | zero => exact Spec.pure hb ⟨fun _ => trivial, (Computes.self ha).congr fun v _ => by simp⟩
    | one =>
      exact (spec_notG hb ha).mono (Nat.le_refl _) fun a b' _ ⟨hr, hc'⟩ =>
        ⟨fun _ => hr trivial, hc'.congr fun v _ => by simp⟩
    | row r' =>
      exact (spec_row (y := .zero) hb ha trivial hc).mono (Nat.le_refl _) fun a b' _ ⟨hr, hc'⟩ =>
        ⟨fun _ => hr, hc'.congr fun v _ => by simp [gateBits]⟩

/-- The rows χ may make: two when `c` is the constant one (a NOT and an XOR), else at most one. -/
def chiCost (c : Src) : Nat := if c = .one then 2 else 1

theorem chiCost_le (c : Src) : chiCost c ≤ 2 := by unfold chiCost; split <;> omega

theorem chiCost_row {c : Src} (h : IsRow c) : chiCost c = 1 := by
  cases c <;> simp_all [chiCost, IsRow]

/-- **χ** (`Builder::chi`): `a ⊕ (¬b ∧ c)`, in one row unless a constant makes it cheaper; a row
when its three inputs are. -/
theorem spec_chiG {a b c : Src} {bld : Builder} (hbld : WF bld) (ha : Valid bld a) (hb : Valid bld b)
    (hc : Valid bld c) :
    Spec (chiG a b c) bld (chiCost c)
      (Out (IsRow a ∧ IsRow b ∧ IsRow c) fun v => read v a ^^ (!read v b && read v c)) := by
  cases b with
  | one =>
    exact Spec.pure hbld ⟨fun h => h.1, (Computes.self ha).congr fun v _ => by simp⟩
  | zero =>
    cases c with
    | zero => exact Spec.pure hbld ⟨fun h => h.1, (Computes.self ha).congr fun v _ => by simp⟩
    | one =>
      exact (spec_xorG hbld ha hc).mono (by simp [chiCost]) fun r b' _ ⟨_, hc'⟩ =>
        ⟨fun h => by simp [IsRow] at h, hc'.congr fun v _ => by simp⟩
    | row r =>
      exact (spec_xorG hbld ha hc).mono (by simp [chiCost]) fun r b' _ ⟨_, hc'⟩ =>
        ⟨fun h => by simp [IsRow] at h, hc'.congr fun v _ => by simp⟩
  | row rb =>
    cases c with
    | zero => exact Spec.pure hbld ⟨fun h => h.1, (Computes.self ha).congr fun v _ => by simp⟩
    | one =>
      show Spec (notG (.row rb) >>= xorG a) bld 2 _
      refine Spec.bind (k := 1) (k' := 1) (spec_notG hbld hb) fun nb b' hg ⟨_, hnb⟩ => ?_
      exact (spec_xorG hg.wf (ha.of_ext hg.ext) hnb.1).mono (Nat.le_refl _) fun r b'' hg' ⟨_, hc'⟩ =>
        ⟨fun h => by simp [IsRow] at h, hc'.congr fun v hv => by
          rw [hnb.2 v (hv.of_ext hg'.ext)]; simp⟩
    | row rc =>
      exact (spec_row hbld ha hb hc).mono (by simp [chiCost]) fun r b' _ ⟨hr, hc'⟩ =>
        ⟨fun _ => hr, hc'.congr fun v _ => by simp [gateBits, Bool.and_comm]⟩

/-! ## Inputs -/

/-- The builder with one more input row. -/
def Builder.addInput (b : Builder) : Builder :=
  ⟨b.rows.push ⟨.row b.rows.size, .row b.rows.size, .row b.rows.size⟩, b.inputs.push b.rows.size⟩

theorem runB_input (b : Builder) : runB input b = (.row b.rows.size, b.addInput) := rfl

theorem addInput_rowsExt (b : Builder) : RowsExt b b.addInput :=
  ⟨by simp [Builder.addInput], fun r hr => by simp only [Builder.addInput, getD_push, hr, ite_true]⟩

theorem addInput_size (b : Builder) : b.addInput.rows.size = b.rows.size + 1 := by
  simp [Builder.addInput]

/-- An input row's gate holds for every value: `v ⊕ (v ∧ ¬v) = v`. -/
theorem sat_addInput (v : Nat → Bool) (b : Builder) : Sat v b.addInput ↔ Sat v b := by
  refine ⟨fun h => h.of_rowsExt (addInput_rowsExt b), fun h r h1 h2 => ?_⟩
  simp only [addInput_size] at h2
  by_cases hr : r < b.rows.size
  · rw [(addInput_rowsExt b).rows_eq r hr]; exact h r h1 hr
  · have : r = b.rows.size := by omega
    subst this
    simp only [Builder.addInput, getD_push, Nat.lt_irrefl, ite_false, ite_true, Row.eval, read_row]
    cases v b.rows.size <;> rfl

theorem addInput_wf {b : Builder} (hb : WF b) : WF b.addInput := by
  have hs := hb.size
  refine ⟨by simp [Builder.addInput]; omega, ?_, fun r hr => ?_, fun r hr => ?_, fun r h1 h2 h3 => ?_⟩
  · simp only [Builder.addInput, Array.toList_push, List.pairwise_append, List.pairwise_singleton,
      List.mem_singleton, forall_eq, true_and]
    exact ⟨hb.sorted, fun a ha => (hb.input_range a (Array.mem_def.mpr ha)).2⟩
  · simp only [Builder.addInput, Array.mem_push] at hr
    simp only [Builder.addInput, Array.size_push]
    rcases hr with hr | rfl
    · have := hb.input_range r hr; omega
    · omega
  · simp only [Builder.addInput, Array.mem_push] at hr
    simp only [Builder.addInput, getD_push]
    rcases hr with hr | rfl
    · have := hb.input_range r hr; simp only [this.2, ite_true]; exact hb.input_row r hr
    · simp
  · simp only [Builder.addInput, Array.mem_push, not_or] at h3
    simp only [addInput_size] at h2
    have hr : r < b.rows.size := by omega
    rw [(addInput_rowsExt b).rows_eq r hr]
    exact hb.order r h1 hr h3.1

/-- **Free bits** (`freeBits n`, `n` calls of `Builder::input`): rows `s, …, s + n - 1` from the
current size `s`, each an input, appended to the inputs in order; every valuation satisfies them. -/
theorem spec_freeBits_list {β : Type} (l : List β) (b : Builder) (hb : WF b) :
    let r := runB (l.mapM fun _ => input) b
    RowsExt b r.2 ∧ r.2.rows.size = b.rows.size + l.length ∧ WF r.2 ∧
    r.2.inputs = b.inputs ++ ((List.range l.length).map (b.rows.size + ·)).toArray ∧
    r.1 = (List.range l.length).map (fun k => Src.row (b.rows.size + k)) ∧
    ∀ v, Sat v r.2 ↔ Sat v b := by
  induction l generalizing b with
  | nil => exact ⟨RowsExt.refl b, rfl, hb, by simp [runB_pure], rfl, fun _ => Iff.rfl⟩
  | cons u l ih =>
    rw [List.mapM_cons, runB_bind, runB_input]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih b.addInput (addInput_wf hb)
    rw [runB_bind, runB_pure]
    refine ⟨(addInput_rowsExt b).trans h1, ?_, h3, ?_, ?_, fun v => (h6 v).trans (sat_addInput v b)⟩
    · rw [h2, addInput_size]; simp; omega
    · rw [h4]
      simp only [Builder.addInput, List.length_cons, List.range_succ_eq_map]
      apply Array.ext'
      simp [Nat.add_assoc, Nat.add_comm 1]
    · rw [h5]
      simp [addInput_size, List.range_succ_eq_map, Nat.add_assoc, Nat.add_comm 1]

end PcsCircuit
