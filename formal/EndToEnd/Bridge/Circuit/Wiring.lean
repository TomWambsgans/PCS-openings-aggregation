-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit.Sim
import Circuit.Wiring

/-!
# The wiring: the statement's σ is F0b's

The statement's `wiring` (`for` loops in `Id`, a slot's first and last cell held as numbers with
the sentinel `4n` for none) and F0b's (`Joins`, `Option`s, folds): `wiring_eq`, equal on every
`2^logRows` rows whose sources read slots below `n + 2` (constants, or rows of the circuit). The
statement's loops are folds of `qJoin` (`wiring_eq_fold`), and `JRel` relates the two states step
by step (`jRel_join`).
-/

namespace Bridge.Circuit

/-! ## The statement's wiring as folds -/

/-- `finish`'s `slot` (statement). -/
def qSlot : PcsQuotient.Src → ℕ
  | .zero => 0
  | .one => 1
  | .row r => 2 + r

theorem qSlot_eq (s : PcsQuotient.Src) : qSlot s = PcsCircuit.slot (srcTr s) := by
  cases s <;> rfl

/-- One join of the statement's `finish`: `cell` joins the cycle of slot `at_`, the sentinel
`none` for a slot without a cell. -/
def qJoin (none : ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (at_ cell : ℕ) : Array ℕ × Array ℕ × Array ℕ :=
  if s.1[at_]! = none then
    (s.1.set! at_ cell, s.2.1.set! at_ cell, s.2.2.set! cell (s.1.set! at_ cell)[at_]!)
  else (s.1, s.2.1.set! at_ cell, (s.2.2.set! s.2.1[at_]! cell).set! cell s.1[at_]!)

/-- The statement's wiring, its loops as folds. -/
def wiringFoldQ (logRows : ℕ) (rows : Array PcsQuotient.Row) : Array ℕ × Array ℕ × Array ℕ :=
  let n := 2 ^ logRows
  let st₀ := (Array.replicate (n + 2) (4 * n), Array.replicate (n + 2) (4 * n), Array.range (4 * n))
  let st₁ := (List.range n).foldl (fun st r => qJoin (4 * n) st (2 + r) (4 * r + 3)) st₀
  (List.range n).foldl (fun st r =>
    let row := rows.getD r PcsQuotient.idle
    qJoin (4 * n) (qJoin (4 * n) (qJoin (4 * n) st (qSlot row.x) (4 * r)) (qSlot row.y) (4 * r + 1))
      (qSlot row.c) (4 * r + 2)) st₁

theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, h, pure_bind, List.foldl_cons]; exact ih _

theorem forIn_range_id {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) :
    forIn [:n] init f = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size, List.range_eq_range']

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem wiring_eq_fold (logRows : ℕ) (rows : Array PcsQuotient.Row) :
    PcsQuotient.wiring logRows rows = (wiringFoldQ logRows rows).2.2 := by
  unfold PcsQuotient.wiring wiringFoldQ
  simp only [forIn_range_id]
  rw [forIn_id_yield (g := fun st r => qJoin (4 * 2 ^ logRows) st (2 + r) (4 * r + 3))]
  · simp only [pure_bind]
    rw [forIn_id_yield (g := fun st r =>
      qJoin (4 * 2 ^ logRows) (qJoin (4 * 2 ^ logRows) (qJoin (4 * 2 ^ logRows) st
        (qSlot (rows.getD r PcsQuotient.idle).x) (4 * r)) (qSlot (rows.getD r PcsQuotient.idle).y)
        (4 * r + 1)) (qSlot (rows.getD r PcsQuotient.idle).c) (4 * r + 2))]
    · rfl
    · intro r s
      rw [forIn_id_yield (g := fun st (a : ℕ × PcsQuotient.Src) =>
        qJoin (4 * 2 ^ logRows) st (qSlot a.2) (4 * r + a.1))]
      · simp only [List.foldl_cons, List.foldl_nil, pure_bind, Nat.add_zero, Prod.mk.eta]
      · intro a st
        obtain ⟨k, src⟩ := a
        cases src <;> simp only [ite_pure_yield, qJoin, qSlot] <;> rfl
  · intro r s
    simp only [ite_pure_yield, qJoin]

/-! ## The two states, related -/

theorem getElem!_eq_getD (a : Array ℕ) (i : ℕ) : a[i]! = a.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, getElem!_def]
  cases a[i]? <;> rfl

/-- The statement's state (numbers, the sentinel `4n`) and F0b's (`Option`s). -/
structure JRel (n : ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (st : PcsCircuit.Joins) : Prop where
  sigma : s.2.2 = st.sigma
  fsize : s.1.size = n + 2
  lsize : s.2.1.size = n + 2
  pfsize : st.first.size = n + 2
  plsize : st.last.size = n + 2
  none_ : ∀ i < n + 2, st.first.getD i none = none → s.1.getD i 0 = 4 * n
  some_ : ∀ i < n + 2, ∀ f, st.first.getD i none = some f →
    s.1.getD i 0 = f ∧ f < 4 * n ∧ ∃ l, st.last.getD i none = some l ∧ s.2.1.getD i 0 = l

theorem jRel_join {n : ℕ} {s : Array ℕ × Array ℕ × Array ℕ} {st : PcsCircuit.Joins}
    (h : JRel n s st) {at_ cell : ℕ} (ha : at_ < n + 2) (hc : cell < 4 * n) :
    JRel n (qJoin (4 * n) s at_ cell) (PcsCircuit.join st at_ cell) := by
  obtain ⟨first, last, sigma⟩ := st
  obtain ⟨f₁, l₁, σ₁⟩ := s
  unfold qJoin PcsCircuit.join
  simp only [getElem!_eq_getD]
  rcases hf : first.getD at_ none with _ | f
  · -- a new cycle
    have h1 := h.none_ at_ ha hf
    simp only [h1, if_true]
    have hfs : at_ < f₁.size := by rw [h.fsize]; exact ha
    rw [PcsCircuit.getD_set!_eq _ _ _ hfs]
    refine ⟨by have := h.sigma; simp only at this ⊢; rw [this], by simp [PcsCircuit.size_set!, h.fsize], by simp [PcsCircuit.size_set!, h.lsize],
      by simp [PcsCircuit.size_set!, h.pfsize], by simp [PcsCircuit.size_set!, h.plsize], ?_, ?_⟩
    · intro i hi hn
      by_cases hia : at_ = i
      · subst hia
        rw [PcsCircuit.getD_set!_eq _ _ _ (by rw [h.pfsize]; exact ha)] at hn
        cases hn
      · rw [PcsCircuit.getD_set!_ne _ _ _ hia] at hn
        rw [PcsCircuit.getD_set!_ne _ _ _ hia]
        exact h.none_ i hi hn
    · intro i hi f hs
      by_cases hia : at_ = i
      · subst hia
        rw [PcsCircuit.getD_set!_eq _ _ _ (by rw [h.pfsize]; exact ha)] at hs
        cases hs
        refine ⟨PcsCircuit.getD_set!_eq _ _ _ hfs, hc, cell, ?_, ?_⟩
        · exact PcsCircuit.getD_set!_eq _ _ _ (by rw [h.plsize]; exact ha)
        · exact PcsCircuit.getD_set!_eq _ _ _ (by rw [h.lsize]; exact ha)
      · rw [PcsCircuit.getD_set!_ne _ _ _ hia] at hs
        obtain ⟨e1, e2, l, e3, e4⟩ := h.some_ i hi f hs
        exact ⟨by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact e1, e2, l,
          by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact e3,
          by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact e4⟩
  · -- joining an existing cycle
    obtain ⟨e1, e2, l, e3, e4⟩ := h.some_ at_ ha f hf
    have hne : f ≠ 4 * n := by omega
    simp only [e1, hne, if_false, e4, e3, Option.getD_some]
    refine ⟨by have := h.sigma; simp only at this ⊢; rw [this], h.fsize, by simp [PcsCircuit.size_set!, h.lsize], h.pfsize,
      by simp [PcsCircuit.size_set!, h.plsize], ?_, ?_⟩
    · intro i hi hn
      exact h.none_ i hi hn
    · intro i hi f' hs
      obtain ⟨g1, g2, l', g3, g4⟩ := h.some_ i hi f' hs
      by_cases hia : at_ = i
      · subst hia
        exact ⟨g1, g2, cell, PcsCircuit.getD_set!_eq _ _ _ (by rw [h.plsize]; exact ha),
          PcsCircuit.getD_set!_eq _ _ _ (by rw [h.lsize]; exact ha)⟩
      · exact ⟨g1, g2, l', by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact g3,
          by rw [PcsCircuit.getD_set!_ne _ _ _ hia]; exact g4⟩

theorem jRel_init (n : ℕ) :
    JRel n (Array.replicate (n + 2) (4 * n), Array.replicate (n + 2) (4 * n), Array.range (4 * n))
      ⟨Array.replicate (n + 2) none, Array.replicate (n + 2) none, Array.range (4 * n)⟩ := by
  refine ⟨rfl, by simp, by simp, by simp, by simp, fun i hi _ => ?_, fun i hi f hs => ?_⟩
  · simp [Array.getD_eq_getD_getElem?, hi]
  · simp [Array.getD_eq_getD_getElem?, hi] at hs

/-- **The statement's σ is F0b's**, on `2^logRows` rows whose sources read slots below `n + 2`. -/
theorem wiring_eq (logRows : ℕ) (rows : Array PcsQuotient.Row) (hn : rows.size = 2 ^ logRows)
    (hs : ∀ r < rows.size, qSlot (rows.getD r PcsQuotient.idle).x < rows.size + 2 ∧
      qSlot (rows.getD r PcsQuotient.idle).y < rows.size + 2 ∧
      qSlot (rows.getD r PcsQuotient.idle).c < rows.size + 2) :
    PcsQuotient.wiring logRows rows = PcsCircuit.wiring (rows.map rowTr) := by
  rw [wiring_eq_fold]
  unfold wiringFoldQ PcsCircuit.wiring
  simp only [Array.size_map, hn]
  rw [hn] at hs
  generalize 2 ^ logRows = n at hs ⊢
  have h1 : ∀ (l : List ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (st : PcsCircuit.Joins),
      (∀ r ∈ l, r < n) → JRel n s st →
      JRel n (l.foldl (fun st r => qJoin (4 * n) st (2 + r) (4 * r + 3)) s)
        (l.foldl (fun st r => PcsCircuit.join st (2 + r) (4 * r + 3)) st) := by
    intro l
    induction l with
    | nil => intro s st _ h; exact h
    | cons r l ih =>
      intro s st hl h
      have hr := hl r (List.mem_cons_self ..)
      exact ih _ _ (fun r' h' => hl r' (List.mem_cons_of_mem _ h'))
        (jRel_join h (by omega) (by omega))
  have h2 : ∀ (l : List ℕ) (s : Array ℕ × Array ℕ × Array ℕ) (st : PcsCircuit.Joins),
      (∀ r ∈ l, r < n) → JRel n s st →
      JRel n (l.foldl (fun st r =>
          qJoin (4 * n) (qJoin (4 * n) (qJoin (4 * n) st (qSlot (rows.getD r PcsQuotient.idle).x)
            (4 * r)) (qSlot (rows.getD r PcsQuotient.idle).y) (4 * r + 1))
            (qSlot (rows.getD r PcsQuotient.idle).c) (4 * r + 2)) s)
        (l.foldl (fun st r =>
          PcsCircuit.join (PcsCircuit.join (PcsCircuit.join st
            (PcsCircuit.slot ((rows.map rowTr).getD r .idle).x) (4 * r))
            (PcsCircuit.slot ((rows.map rowTr).getD r .idle).y) (4 * r + 1))
            (PcsCircuit.slot ((rows.map rowTr).getD r .idle).c) (4 * r + 2)) st) := by
    intro l
    induction l with
    | nil => intro s st _ h; exact h
    | cons r l ih =>
      intro s st hl h
      have hr := hl r (List.mem_cons_self ..)
      obtain ⟨hx, hy, hc⟩ := hs r hr
      have hrow : (rows.map rowTr).getD r .idle = rowTr (rows.getD r PcsQuotient.idle) := by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
        cases rows[r]? <;> rfl
      refine ih _ _ (fun r' h' => hl r' (List.mem_cons_of_mem _ h')) ?_
      simp only [hrow, rowTr, ← qSlot_eq]
      exact jRel_join (jRel_join (jRel_join h hx (by omega)) hy (by omega)) hc (by omega)
  exact (h2 _ _ _ (fun r h => List.mem_range.mp h)
    (h1 _ _ _ (fun r h => List.mem_range.mp h) (jRel_init n))).sigma

end Bridge.Circuit
