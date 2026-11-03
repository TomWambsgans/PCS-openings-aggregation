-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecPiop.Circuit

/-!
# The dataflow lemma: the witness is a fixed point of the circuit

The copy argument (`RecPiop.Copy`) gives `w (σ i) = push w i` at every non-hole `i`: the pull at
the target is the push meant for it. Read as dataflow (SPEC-REC.md §2.3), each non-hole cell `j`
has exactly one producer, `σ⁻¹ j` (`producer`), and its value is the producer's push
(`flow`): **the witness is a fixed point of the circuit's dataflow** (`copy_iff_flow`,
`satisfies_iff`), the statement a compiler-correctness proof consumes. Read slot by slot:

* **an expression slot's push arrives at its target**: `w (σ i) = E_i(cells of i's row) + κ_i`
  (`expr_slot`), and **a constant** (an expression of no terms) pushes `κ_i` (`constant_slot`);
* **a forward carries its value**: `w (σ i) = w i` (`forward_slot`; `κ = 0` there), so along a chain
  of forwards the value is unchanged (`forward_chain`), and a value travels from its producing
  expression slot through forwards to the chain's end (`expr_chain`);
* **holes are never read**: the pushes at every position, holes included, do not depend on the
  holes' values (`push_congr_off_holes`), which the PIOP leaves free (REVIEW-REC.md N1): two
  witnesses that agree off the holes have the same dataflow (`flow_congr_off_holes`).

Generic in the layout; only `Valid` is assumed.
-/

set_option linter.unusedSectionVars false

namespace RecPiop

variable {F : Type} [Field F]

/-! ## Formulas read only their cells -/

theorem Poly2.eval_congr {R : Type} [CommRing R] [Algebra F R] (p : Poly2 F) {cell cell' : ℕ → R}
    (h : ∀ c ∈ p.reads, cell c = cell' c) : p.eval cell = p.eval cell' := by
  unfold Poly2.eval
  congr 1
  · congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [h t.1 (List.mem_append_left _ (List.mem_map_of_mem ht))]
  · congr 1
    refine List.map_congr_left fun t ht => ?_
    have hm : ∀ c ∈ [t.1, t.2.1], c ∈ p.reads := fun c hc =>
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, hc⟩)
    rw [h t.1 (hm _ (by simp)), h t.2.1 (hm _ (by simp))]

theorem fpEval_congr {R : Type} [CommRing R] [Algebra F R] (ls : List (Limb F)) (γ : F)
    {cell cell' : ℕ → R} (h : ∀ c ∈ ls.map (·.cell), cell c = cell' c) :
    fpEval ls γ cell = fpEval ls γ cell' := by
  unfold fpEval
  congr 1
  refine List.map_congr_left fun l hl => ?_
  rw [h l.cell (List.mem_map_of_mem hl)]

/-- **A role's push reads its cells, and its own pull only if it is a forward.** -/
theorem Role.value_congr {R : Type} [CommRing R] [Algebra F R] (r : Role F) (γ : F)
    {own own' : R} {cell cell' : ℕ → R} (ho : r.isForward = true → own = own')
    (h : ∀ c ∈ r.reads, cell c = cell' c) : r.value γ own cell = r.value γ own' cell' := by
  cases r with
  | forward => exact ho rfl
  | expr p => exact Poly2.eval_congr p h
  | port ls => exact fpEval_congr ls γ h

namespace Circuit

variable (G : Circuit F)

/-! ## The dataflow -/

/-- **The producer of a cell**: the position whose push targets it (`σ⁻¹ j`), the first one if any. -/
def producer (j : ℕ) : ℕ :=
  if h : ∃ i, i < G.N ∧ G.sigma i = j then Nat.find h else 0

/-- **The circuit's dataflow** on a witness: every non-hole cell takes its producer's push; holes
and cells past `N` keep their value. -/
def flow (w : ℕ → F) (j : ℕ) : F :=
  if j < G.N ∧ ¬ G.IsHole j then G.push w 0 (G.producer j) else w j

variable {G}

theorem producer_spec (hV : G.Valid) {j : ℕ} (hj : j < G.N) (hh : ¬ G.IsHole j) :
    G.producer j < G.N ∧ G.sigma (G.producer j) = j := by
  have hex : ∃ i, i < G.N ∧ G.sigma i = j := by
    obtain ⟨i, hi, he⟩ := hV.sigma_onto j hj hh
    exact ⟨i, hi, he⟩
  unfold producer
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

/-- The producer of a push's target is the pushing position. -/
theorem producer_sigma (hV : G.Valid) {i : ℕ} (hi : i < G.N) (hh : ¬ G.IsHole i) :
    G.producer (G.sigma i) = i := by
  obtain ⟨hs, hsh⟩ := hV.sigma_inside i hi hh
  obtain ⟨hp, hpe⟩ := producer_spec hV hs hsh
  exact hV.sigma_inj _ hp i hi hpe

/-- A producer of a non-hole is a non-hole: holes push outside. -/
theorem producer_not_hole (hV : G.Valid) {j : ℕ} (hj : j < G.N) (hh : ¬ G.IsHole j) :
    ¬ G.IsHole (G.producer j) := by
  intro hph
  obtain ⟨hp, hpe⟩ := producer_spec hV hj hh
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem ((hV.ports_holes _).mpr ⟨hp, hph⟩)
  have := hV.sigma_port k hk
  have hport : G.port k = G.producer j := by
    unfold port
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hke]
  rw [hport, hpe] at this
  omega

/-- **The copy constraints are the dataflow's fixed point.** Every non-hole's pull is the push
meant for it exactly when the witness is a fixed point of `flow`. -/
theorem copy_iff_flow (hV : G.Valid) (w : ℕ → F) :
    (∀ i < G.N, ¬ G.IsHole i → w (G.sigma i) = G.push w 0 i) ↔ G.flow w = w := by
  constructor
  · intro h
    funext j
    unfold flow
    split_ifs with hj
    · obtain ⟨hp, hpe⟩ := producer_spec hV hj.1 hj.2
      have := h _ hp (producer_not_hole hV hj.1 hj.2)
      rw [hpe] at this
      exact this.symm
    · rfl
  · intro h i hi hh
    obtain ⟨hs, hsh⟩ := hV.sigma_inside i hi hh
    have := congrFun h (G.sigma i)
    unfold flow at this
    rw [ite_eq_left ⟨hs, hsh⟩, producer_sigma hV hi hh] at this
    exact this.symm

/-- **The relation is the dataflow's fixed point with the public ports.** -/
theorem satisfies_iff (hV : G.Valid) (pub : ℕ → List F) (w : ℕ → F) :
    G.Satisfies pub w ↔ G.flow w = w ∧ ∀ j < G.nP, G.limbVals w j = pub j :=
  ⟨fun h => ⟨(copy_iff_flow hV w).mp h.copy, h.ports⟩,
    fun h => ⟨(copy_iff_flow hV w).mpr h.1, h.2⟩⟩

/-! ## Slot by slot -/

variable {pub : ℕ → List F} {w : ℕ → F}

/-- **An expression slot's push arrives at its target**: its formula on its row's cells, plus
`κ`. -/
theorem expr_slot (h : G.Satisfies pub w) {i : ℕ} (hi : i < G.N) {p : Poly2 F}
    (hr : G.role i = .expr p) :
    w (G.sigma i) = p.eval (fun c => w (G.base i + c)) + G.kappa i := by
  have hh : ¬ G.IsHole i := by unfold IsHole; rw [hr]; exact Bool.false_ne_true
  rw [h.copy i hi hh]
  unfold push
  rw [hr]
  rfl

/-- **A constant**: an expression slot of no terms pushes `κ`. -/
theorem constant_slot (h : G.Satisfies pub w) {i : ℕ} (hi : i < G.N)
    (hr : G.role i = .expr ⟨[], []⟩) : w (G.sigma i) = G.kappa i := by
  rw [expr_slot h hi hr]
  simp [Poly2.eval]

/-- **A forward carries its value** (`κ` is zero off the expression slots). -/
theorem forward_slot (hV : G.Valid) (h : G.Satisfies pub w) {i : ℕ} (hi : i < G.N)
    (hr : G.role i = .forward) : w (G.sigma i) = w i := by
  have hh : ¬ G.IsHole i := by unfold IsHole; rw [hr]; exact Bool.false_ne_true
  have hk : G.kappa i = 0 := by
    by_contra hk
    have := hV.kappa_expr i hi hk
    rw [hr] at this
    exact Bool.false_ne_true this
  rw [h.copy i hi hh]
  unfold push
  rw [hr, hk, add_zero]
  rfl

/-- **A chain of forwards carries its value**: if the first `n` positions of the chain
`i, σ i, σ² i, …` are forwards, the value at the chain's `n`-th position is the first one's. -/
theorem forward_chain (hV : G.Valid) (h : G.Satisfies pub w) (i : ℕ) :
    ∀ n, (∀ k < n, G.sigma^[k] i < G.N ∧ G.role (G.sigma^[k] i) = .forward) →
      w (G.sigma^[n] i) = w i
  | 0, _ => rfl
  | n + 1, hc => by
    rw [Function.iterate_succ_apply',
      forward_slot hV h (hc n (by omega)).1 (hc n (by omega)).2,
      forward_chain hV h i n fun k hk => hc k (by omega)]

/-- **A value travels from its expression slot through forwards to the chain's end**: the
formula's value plus `κ`, at the end of a chain of `n` forwards from the slot's target. -/
theorem expr_chain (hV : G.Valid) (h : G.Satisfies pub w) {i : ℕ} (hi : i < G.N) {p : Poly2 F}
    (hr : G.role i = .expr p) (n : ℕ)
    (hc : ∀ k < n, G.sigma^[k] (G.sigma i) < G.N ∧ G.role (G.sigma^[k] (G.sigma i)) = .forward) :
    w (G.sigma^[n] (G.sigma i)) = p.eval (fun c => w (G.base i + c)) + G.kappa i := by
  rw [forward_chain hV h _ n hc, expr_slot h hi hr]

/-! ## Holes are never read -/

/-- A role of a block's region is in the region's list, or a forward. -/
theorem regionRole_mem (hV : G.Valid) {b : Block} (hb : b ∈ G.blocks) (k : ℕ) :
    (∃ r ∈ G.regions, G.regionRole b k ∈ r) ∨ G.regionRole b k = .forward := by
  have hreg := hV.region_lt b hb
  have e : G.regions.getD b.region [] = G.regions[b.region] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hreg, Option.getD_some]
  unfold regionRole
  rw [e, List.getD_eq_getElem?_getD]
  cases hk : (G.regions[b.region])[k]? with
  | none => exact Or.inr rfl
  | some r => exact Or.inl ⟨_, List.getElem_mem hreg, List.mem_of_getElem? hk⟩

theorem role_of_blockAt {i : ℕ} {b : Block} (h : G.blockAt (i / G.W) = some b) :
    G.role i = G.regionRole b (i % G.W) := by
  unfold role
  rw [h]

theorem role_of_blockAt_none {i : ℕ} (h : G.blockAt (i / G.W) = none) : G.role i = .forward := by
  unfold role
  rw [h]

/-- **Every role reads its row**: a cell a role reads is below `W`. -/
theorem role_reads_lt (hV : G.Valid) {i c : ℕ} (hc : c ∈ (G.role i).reads) : c < G.W := by
  cases hb : G.blockAt (i / G.W) with
  | none => rw [role_of_blockAt_none hb] at hc; simp [Role.reads] at hc
  | some b =>
    rw [role_of_blockAt hb] at hc
    rcases regionRole_mem hV (List.mem_of_find?_eq_some hb) (i % G.W) with ⟨r, hr, hm⟩ | hf
    · exact hV.reads_lt r hr _ hm c hc
    · rw [hf] at hc; simp [Role.reads] at hc

theorem W_dvd_N (hV : G.Valid) : G.W ∣ G.N := Nat.pow_dvd_pow 2 hV.logW_lt.le

/-- A cell of a position's row is a position. -/
theorem base_add_lt (hV : G.Valid) {i c : ℕ} (hi : i < G.N) (hc : c < G.W) :
    G.base i + c < G.N := by
  obtain ⟨k, hk⟩ := W_dvd_N hV
  have hW : 0 < G.W := Nat.two_pow_pos _
  have h1 : i / G.W < k := by
    rw [Nat.div_lt_iff_lt_mul hW, mul_comm, ← hk]
    exact hi
  have : G.base i + G.W ≤ G.N := by
    unfold base
    rw [hk]
    nlinarith
  omega

/-- **The pushes do not read the holes**: two witnesses that agree off the holes have the same
push at every position, holes included (no formula reads a hole; a hole's own role is a port,
which does not read its own pull). -/
theorem push_congr_off_holes (hV : G.Valid) {w w' : ℕ → F}
    (hw : ∀ j < G.N, ¬ G.IsHole j → w j = w' j) (γ : F) {i : ℕ} (hi : i < G.N) :
    G.push w γ i = G.push w' γ i := by
  unfold push
  congr 1
  refine Role.value_congr _ γ (fun hf => hw i hi fun hh => ?_) fun c hc => ?_
  · unfold IsHole at hh
    cases hr : G.role i <;> simp_all [Role.isForward, Role.isPort]
  · exact hw _ (base_add_lt hV hi (role_reads_lt hV hc)) (hV.no_hole_read i hi c hc)

/-- **The dataflow does not read the holes.** -/
theorem flow_congr_off_holes (hV : G.Valid) {w w' : ℕ → F}
    (hw : ∀ j < G.N, ¬ G.IsHole j → w j = w' j) {j : ℕ} (hj : j < G.N) (hh : ¬ G.IsHole j) :
    G.flow w j = G.flow w' j := by
  unfold flow
  rw [ite_eq_left ⟨hj, hh⟩, ite_eq_left ⟨hj, hh⟩]
  exact push_congr_off_holes hV hw 0 (producer_spec hV hj hh).1

end Circuit

end RecPiop
