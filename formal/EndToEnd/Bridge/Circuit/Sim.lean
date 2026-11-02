-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient.Circuit
import Circuit.Final

/-!
# The two builders, step by step: the simulation

The statement's circuit (`PcsQuotient`, `formal/Statement/PcsQuotient/Circuit.lean`) and F0b's
(`PcsCircuit`, `formal/Circuit/Circuit/Defs.lean`) transcribe the same Rust builder
(`quotient::circuit`) with two types of sources (`PcsQuotient.Src`, `PcsCircuit.Src`, the same three
constructors). `srcTr` reads one as the other, `rowTr` a row, `bTr` a builder (its rows read, its
inputs kept). **`SimR p q R`**: run from any statement builder `b`, `p` and `q` (from `bTr b`) end in
builders related by `bTr` and with results related by `R`. Each gate is simulated (`sim_row`,
`sim_input`, `sim_not`, `sim_xor`, `sim_chi`), simulations compose (`SimR.bind`), and lists of
steps simulate (`simR_mapM`, `simR_forIn`). Nothing here evaluates a circuit: every lemma is about
general arguments.
-/

namespace Bridge.Circuit

/-! ## Reading one transcription as the other -/

/-- A statement source as F0b's. -/
def srcTr : PcsQuotient.Src → PcsCircuit.Src
  | .zero => .zero
  | .one => .one
  | .row r => .row r

/-- An F0b source as the statement's. -/
def srcOf : PcsCircuit.Src → PcsQuotient.Src
  | .zero => .zero
  | .one => .one
  | .row r => .row r

@[simp] theorem srcOf_srcTr (s : PcsQuotient.Src) : srcOf (srcTr s) = s := by cases s <;> rfl

@[simp] theorem srcTr_srcOf (s : PcsCircuit.Src) : srcTr (srcOf s) = s := by cases s <;> rfl

theorem srcTr_injective : Function.Injective srcTr := fun a b h => by
  rw [← srcOf_srcTr a, h, srcOf_srcTr]

@[simp] theorem srcTr_zero : srcTr .zero = .zero := rfl
@[simp] theorem srcTr_one : srcTr .one = .one := rfl
@[simp] theorem srcTr_row (r : ℕ) : srcTr (.row r) = .row r := rfl

/-- A statement row as F0b's. -/
def rowTr (r : PcsQuotient.Row) : PcsCircuit.Row := ⟨srcTr r.x, srcTr r.y, srcTr r.c⟩

@[simp] theorem rowTr_idle : rowTr PcsQuotient.idle = PcsCircuit.Row.idle := rfl

/-- A statement builder as F0b's: its rows read as F0b's rows, the same inputs. -/
def bTr (b : PcsQuotient.Builder) : PcsCircuit.Builder := ⟨b.rows.map rowTr, b.inputs⟩

@[simp] theorem bTr_rows (b : PcsQuotient.Builder) : (bTr b).rows = b.rows.map rowTr := rfl
@[simp] theorem bTr_inputs (b : PcsQuotient.Builder) : (bTr b).inputs = b.inputs := rfl

theorem bTr_new : bTr PcsQuotient.Builder.new = PcsCircuit.Builder.new := by
  simp only [bTr, PcsQuotient.Builder.new, PcsCircuit.Builder.new, Array.map_replicate, rowTr_idle,
    PcsQuotient.publicRows, PcsCircuit.publicRows]

/-! ## Runs and the simulation -/

/-- Run a statement builder program from a builder. -/
def qrun {α : Type} (p : PcsQuotient.BuildM α) (b : PcsQuotient.Builder) :
    α × PcsQuotient.Builder := (p.run b).run

theorem qrun_bind {α β : Type} (p : PcsQuotient.BuildM α) (f : α → PcsQuotient.BuildM β)
    (b : PcsQuotient.Builder) : qrun (p >>= f) b = qrun (f (qrun p b).1) (qrun p b).2 := rfl

theorem qrun_pure {α : Type} (a : α) (b : PcsQuotient.Builder) :
    qrun (pure a : PcsQuotient.BuildM α) b = (a, b) := rfl

theorem crun_bind {α β : Type} (p : PcsCircuit.BuildM α) (f : α → PcsCircuit.BuildM β)
    (b : PcsCircuit.Builder) :
    PcsCircuit.runBuild (p >>= f) b =
      PcsCircuit.runBuild (f (PcsCircuit.runBuild p b).1) (PcsCircuit.runBuild p b).2 := rfl

theorem crun_pure {α : Type} (a : α) (b : PcsCircuit.Builder) :
    PcsCircuit.runBuild (pure a : PcsCircuit.BuildM α) b = (a, b) := rfl

/-- **`q` simulates `p`**: from every statement builder `b`, the run of `q` from `bTr b` ends in
`bTr` of the run of `p`'s builder, the two results related by `R`. -/
def SimR {α β : Type} (p : PcsQuotient.BuildM α) (q : PcsCircuit.BuildM β) (R : α → β → Prop) :
    Prop :=
  ∀ b, R (qrun p b).1 (PcsCircuit.runBuild q (bTr b)).1 ∧
    (PcsCircuit.runBuild q (bTr b)).2 = bTr (qrun p b).2

theorem SimR.bind {α β γ δ : Type} {p : PcsQuotient.BuildM α} {q : PcsCircuit.BuildM β}
    {R : α → β → Prop} {p' : α → PcsQuotient.BuildM γ} {q' : β → PcsCircuit.BuildM δ}
    {R' : γ → δ → Prop} (h : SimR p q R) (h' : ∀ a c, R a c → SimR (p' a) (q' c) R') :
    SimR (p >>= p') (q >>= q') R' := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  obtain ⟨h3, h4⟩ := h' _ _ h1 (qrun p b).2
  rw [qrun_bind, crun_bind, h2]
  exact ⟨h3, h4⟩

theorem SimR.pure {α β : Type} {R : α → β → Prop} {a : α} {c : β} (h : R a c) :
    SimR (Pure.pure a : PcsQuotient.BuildM α) (Pure.pure c : PcsCircuit.BuildM β) R :=
  fun _ => ⟨h, rfl⟩

theorem SimR.mono {α β : Type} {p : PcsQuotient.BuildM α} {q : PcsCircuit.BuildM β}
    {R R' : α → β → Prop} (h : SimR p q R) (h' : ∀ a c, R a c → R' a c) : SimR p q R' :=
  fun b => ⟨h' _ _ (h b).1, (h b).2⟩

/-- A statement step against `pure` on F0b's side. -/
theorem SimR.bind_left {α β γ : Type} {p : PcsQuotient.BuildM α} {q : PcsCircuit.BuildM β}
    {R : α → β → Prop} {p' : α → PcsQuotient.BuildM γ} {R' : γ → β → Prop} (h : SimR p q R)
    (h' : ∀ a c, R a c → SimR (p' a) (Pure.pure c) R') : SimR (p >>= p') q R' := by
  rw [← bind_pure q]
  exact h.bind h'

/-- A statement step simulated by a pure value, then the rest. -/
theorem SimR.bind_pure_left {α β γ δ : Type} {p : PcsQuotient.BuildM α} {c : β}
    {R : α → β → Prop} {p' : α → PcsQuotient.BuildM γ} {q : PcsCircuit.BuildM δ}
    {R' : γ → δ → Prop} (h : SimR p (Pure.pure c) R) (h' : ∀ a, R a c → SimR (p' a) q R') :
    SimR (p >>= p') q R' := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  rw [crun_pure] at h1 h2
  simp only at h1 h2
  rw [qrun_bind, h2]
  exact h' _ h1 _

/-- F0b's result mapped. -/
theorem SimR.pure_map {α β γ : Type} {p : PcsQuotient.BuildM α} {q : PcsCircuit.BuildM β}
    {R : α → β → Prop} {R' : α → γ → Prop} (f : β → γ) (h : SimR p q R)
    (h' : ∀ a c, R a c → R' a (f c)) : SimR p (f <$> q) R' := by
  rw [map_eq_pure_bind, ← bind_pure p]
  exact h.bind fun a c hac => SimR.pure (h' a c hac)

/-- A simulation whose results are read by `srcTr`. -/
abbrev SimS (p : PcsQuotient.BuildM PcsQuotient.Src) (q : PcsCircuit.BuildM PcsCircuit.Src) : Prop :=
  SimR p q fun a c => c = srcTr a

/-! ## The gates -/

theorem sim_row (x y c : PcsQuotient.Src) :
    SimS (PcsQuotient.Build.row x y c) (PcsCircuit.Builder.row (srcTr x) (srcTr y) (srcTr c)) := by
  intro b
  refine ⟨?_, ?_⟩
  · show PcsCircuit.Src.row (b.rows.map rowTr).size = srcTr (.row b.rows.size)
    simp
  · show (⟨(b.rows.map rowTr).push ⟨srcTr x, srcTr y, srcTr c⟩, b.inputs⟩ : PcsCircuit.Builder) =
      bTr ⟨b.rows.push ⟨x, y, c⟩, b.inputs⟩
    simp [bTr, Array.map_push, rowTr]

theorem sim_input : SimS PcsQuotient.Build.input PcsCircuit.Builder.input := by
  intro b
  refine ⟨?_, ?_⟩
  · show PcsCircuit.Src.row (b.rows.map rowTr).size = srcTr (.row b.rows.size)
    simp
  · show (⟨(b.rows.map rowTr).push ⟨.row (b.rows.map rowTr).size, .row (b.rows.map rowTr).size,
        .row (b.rows.map rowTr).size⟩, b.inputs.push (b.rows.map rowTr).size⟩ : PcsCircuit.Builder) =
      bTr ⟨b.rows.push ⟨.row b.rows.size, .row b.rows.size, .row b.rows.size⟩,
        b.inputs.push b.rows.size⟩
    simp [bTr, Array.map_push, rowTr]

theorem sim_not (a : PcsQuotient.Src) : SimS (PcsQuotient.Build.not a) (PcsCircuit.Builder.notG (srcTr a)) := by
  cases a with
  | zero => exact SimR.pure rfl
  | one => exact SimR.pure rfl
  | row r => exact sim_row .one .zero (.row r)

theorem sim_xor (a b : PcsQuotient.Src) :
    SimS (PcsQuotient.Build.xor a b) (PcsCircuit.Builder.xorG (srcTr a) (srcTr b)) := by
  cases a <;> cases b
  all_goals first
    | exact SimR.pure rfl
    | exact sim_not _
    | exact sim_row _ _ _

theorem sim_chi (a b c : PcsQuotient.Src) :
    SimS (PcsQuotient.Build.chi a b c) (PcsCircuit.Builder.chiG (srcTr a) (srcTr b) (srcTr c)) := by
  cases b <;> cases c
  all_goals first
    | exact SimR.pure rfl
    | exact sim_xor _ _
    | exact (sim_not _).bind fun _ _ h => h ▸ sim_xor _ _
    | exact sim_row _ _ _

end Bridge.Circuit
