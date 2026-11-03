-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Check

/-!
# A satisfied circuit's values

The dataflow facts, from `Satisfied` and the checked view (`viewOk`): every placement of a value carries one word,
`val v` (`val_holds`): its producer's push for a produced value, the word around its cycle for a free one. Then a
gate's value is its formula on its cells' values plus its `κ` (`gate_val`). This is `lean-rec-piop`'s dataflow lemma,
for this compiler's circuits: proved here from the chains the compiler builds `σ` from, which the checker reads back
from the circuit's `σ`.
-/

namespace RecCircuit

open Primitives

/-! ## Loops and dense columns -/

theorem allBelow_go_spec (n : ℕ) (f : ℕ → Bool) :
    ∀ (k i : ℕ), n - i = k → allBelow.go n f i = true → ∀ j, i ≤ j → j < n → f j = true := by
  intro k
  induction k with
  | zero => intro i hk _ j hij hjn; omega
  | succ k ih =>
    intro i hk h j hij hjn
    rw [allBelow.go] at h
    have hi : i < n := by omega
    simp only [hi, ite_true, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact h.1
    · exact ih (i + 1) (by omega) h.2 j (by omega) hjn

theorem allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) : ∀ i < n, f i = true :=
  fun i hi => allBelow_go_spec n f _ 0 rfl h i (Nat.zero_le _) hi

theorem foldl_set_getD (L : List (ℕ × K)) (a : Array K) (i : ℕ) (hi : i < a.size) :
    (L.foldl (fun a e => a.set! e.1 e.2) a).getD i 0 = L.foldl (fun acc e => if e.1 = i then e.2 else acc) (a.getD i 0) := by
  induction L generalizing a with
  | nil => rfl
  | cons e L ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simpa using hi)]
    congr 1
    simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases h : e.1 = i
    · subst h; simp [hi]
    · simp [h]

theorem denseKappa_getD (C : Circuit) (i : ℕ) (hi : i < C.n) : (denseKappa C).getD i 0 = C.kappaAt i := by
  unfold denseKappa Circuit.kappaAt
  rw [← Array.foldl_toList, ← Array.foldl_toList, foldl_set_getD _ _ _ (by simpa using hi)]
  simp [Array.getD_eq_getD_getElem?, hi]

theorem denseKappa_size (C : Circuit) : (denseKappa C).size = C.n := by
  unfold denseKappa
  rw [← Array.foldl_toList]
  generalize C.kappa.toList = L
  suffices ∀ (a : Array K), (L.foldl (fun a e => a.set! e.1 e.2) a).size = a.size by
    exact (this _).trans (Array.size_replicate ..)
  induction L with
  | nil => intro a; rfl
  | cons e L ih => intro a; rw [List.foldl_cons, ih]; exact Array.size_setIfInBounds ..

/-! ## The values -/

namespace Ctx

variable (X : Ctx)

/-- **A value's word** on a witness: its producer's push, or (a free value) the word at its first forward. -/
def val (w : ℕ → K) (v : ℕ) : K :=
  if X.prod v = NONE then w ((X.chain v).getD 0 0) else X.C.push w (X.prod v)

theorem kap_eq (hX : X.kd = denseKappa X.C) {q : ℕ} (hq : q < X.n) : X.kap q = X.C.kappaAt q := by
  rw [kap, hX]; exact denseKappa_getD _ _ hq

/-- The parts of `viewOk`. -/
theorem viewOk_parts (hv : X.viewOk = true) :
    X.kd.size = X.n ∧ X.V.cellF.size = X.n ∧ X.V.chains.size = X.V.producerF.size ∧
      (∀ v < X.V.producerF.size, X.chainOk v = true) ∧ (∀ q < X.n, X.placedOk q = true) := by
  simp only [viewOk, Bool.and_eq_true, beq_iff_eq] at hv
  exact ⟨hv.1.1.1.1, hv.1.1.1.2, hv.1.1.2, allBelow_spec hv.1.2, allBelow_spec hv.2⟩

/-- A forward's push is its pull. -/
theorem push_fwd (hX : X.kd = denseKappa X.C) (w : ℕ → K) {a : ℕ} (ha : a < X.n) (h : X.fwd a = true) :
    X.C.push w a = w a := by
  simp only [fwd, Bool.and_eq_true, beq_iff_eq] at h
  rw [Circuit.push, h.1, Formula.eval, ← denseKappa_getD _ _ ha, ← hX, ← kap, h.2, add_zero]

/-- Along a linked chain, the pushes reach the next position. -/
theorem link_push {w : ℕ → K} (hw : X.C.Satisfied w) {a b : ℕ} (h : X.link a b = true) : w b = X.C.push w a := by
  simp only [link, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hs⟩, hp⟩ := h
  rw [← hs]
  exact hw a ha hp (hs ▸ hb)

/-- **Along its chain, a value's word is the same** (past its producer). -/
theorem chain_val (hv : X.viewOk = true) (hX : X.kd = denseKappa X.C) {w : ℕ → K} (hw : X.C.Satisfied w)
    {v : ℕ} (hvs : v < X.V.producerF.size) :
    ∀ i < (X.chain v).size, (X.prod v = NONE ∨ 1 ≤ i) → w ((X.chain v).getD i 0) = X.val w v := by
  have hc := (X.viewOk_parts hv).2.2.2.1 v hvs
  simp only [chainOk, Bool.and_eq_true] at hc
  obtain ⟨hlink, hrest⟩ := hc
  have hl := allBelow_spec hlink
  intro i
  induction i with
  | zero =>
    intro _ h
    rcases h with h | h
    · simp [val, h]
    · omega
  | succ i ih =>
    intro hi h
    have hlk := hl i (by omega)
    rw [X.link_push hw hlk]
    have ha : (X.chain v).getD i 0 < X.n := by
      simp only [link, Bool.and_eq_true, decide_eq_true_eq] at hlk; exact hlk.1.1.1
    by_cases hfree : X.prod v = NONE
    · simp only [hfree, beq_self_eq_true, ite_true] at hrest
      rw [X.push_fwd hX w ha (allBelow_spec hrest i (by omega))]
      exact ih (by omega) (Or.inl hfree)
    · have hne : (X.prod v == NONE) = false := by simpa using hfree
      simp only [hne, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrest
      obtain ⟨⟨_, h0⟩, hf⟩ := hrest
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp [val, hfree, h0]
      · have := allBelow_spec hf i (by omega)
        simp only [Bool.or_eq_true, beq_iff_eq] at this
        rcases this with h' | h'
        · omega
        · rw [X.push_fwd hX w ha h']
          exact ih (by omega) (Or.inr hpos)

/-- **A placed value's word** (`val_holds`): every position holding a value carries its word. -/
theorem val_holds (hv : X.viewOk = true) (hX : X.kd = denseKappa X.C) {w : ℕ → K} (hw : X.C.Satisfied w)
    {q : ℕ} (hq : q < X.n) {v : ℕ} (hc : X.cellAt q = v) (hne : v ≠ NONE) : w q = X.val w v := by
  have hp := (X.viewOk_parts hv).2.2.2.2 q hq
  simp only [placedOk, hc, Bool.or_eq_true, beq_iff_eq, hne, false_or, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hi, hq'⟩, hfree⟩ := hp
  have hvs : v < X.V.producerF.size := by
    have hcs := (X.viewOk_parts hv).2.2.1
    by_contra hcon
    have : X.chain v = #[] := by
      simp [chain, Array.getD_eq_getD_getElem?, show X.V.chains.size ≤ v by omega]
    rw [this] at hi; simp at hi
  rw [← hq']
  exact X.chain_val hv hX hw hvs _ hi hfree

/-- A position holding a value is a position. -/
theorem cellAt_lt (hv : X.viewOk = true) {q : ℕ} (h : X.cellAt q ≠ NONE) : q < X.n := by
  have hs := (X.viewOk_parts hv).2.1
  by_contra hcon
  apply h
  simp [cellAt, Array.getD_eq_getD_getElem?, show X.V.cellF.size ≤ q by omega]

end Ctx

/-! ## Polynomials read only their cells -/

theorem Poly.eval_congr (p : Poly) {f g : ℕ → K} (h : ∀ c ∈ p.reads, f c = g c) : p.eval f = p.eval g := by
  unfold Poly.eval
  have hl : p.linear.foldl (fun acc t => acc + t.2 * f t.1) 0 = p.linear.foldl (fun acc t => acc + t.2 * g t.1) 0 := by
    apply List.foldl_ext
    intro acc t ht
    rw [h t.1 (List.mem_append_left _ (List.mem_map_of_mem (f := fun t : ℕ × K => t.1) ht))]
  rw [hl]
  apply List.foldl_ext
  intro acc t ht
  rw [h t.1 (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, by simp⟩)),
    h t.2.1 (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, by simp⟩))]

namespace Ctx

variable (X : Ctx)

/-- The cell assignment's value at a cell. -/
def cellVal (w : ℕ → K) (cells : List (ℕ × ℕ)) (c : ℕ) : K := X.val w ((cells.lookup c).getD NONE)

/-- **A gate's value**: its formula on its cells' values, plus its `κ`. -/
theorem gate_val (hv : X.viewOk = true) (hX : X.kd = denseKappa X.C) {w : ℕ → K} (hw : X.C.Satisfied w)
    {v : ℕ} {p : Poly} {k : K} {cells : List (ℕ × ℕ)} (h : X.gate v p k cells = true) :
    X.val w v = p.eval (X.cellVal w cells) + k := by
  simp only [gate, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hq, hqn⟩, hf⟩, hk⟩, hreads⟩, hcells⟩ := h
  rw [val, ite_cond_eq_false _ _ (eq_false hq), Circuit.push, hf, Formula.eval, ← denseKappa_getD _ _ hqn, ← hX, ← kap, hk]
  refine congrArg (· + k) ?_
  apply Poly.eval_congr
  intro c hc
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hreads c hc)
  have hmem : (c, u) ∈ cells := by
    obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp hu
    rw [hl]; simp
  obtain ⟨hne, hcell⟩ := hcells (c, u) hmem
  rw [cellVal, hu, Option.getD_some]
  exact X.val_holds hv hX hw (X.cellAt_lt hv (hcell ▸ hne)) hcell hne

end Ctx

end RecCircuit
