-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockBase

/-!
# The tower's `XOR` network: each leaf is the sum of its mask's slices

`Pi1.xorNetwork leaves` (Paar's greedy common subexpressions) returns the network's new variables (`xors`, each the sum
of two earlier ones) and, for each leaf, the variables it sums. Whatever pairs the greedy choice picks, the loop keeps
`NetInv`: every leaf's variables are distinct and defined, each new variable sums two earlier ones, and for every
assignment `s` of the 64 slices the sum of a leaf's variables (`netVals s xors`: the slices, then each new variable's
value) is the sum of the slices its mask names (`xorNetwork_inv`). The pair chosen is two distinct variables of one
leaf: the count array's positive entries are pairs of a leaf (`CountInv`), the best entry is positive (`BestInv`).

Also `towerLeaves_size`: the tower has 64 leaves. Both are proved on the definitions' loops (`id_forIn_inv`), never by
evaluating them.
-/

namespace RecGraph.Sim

open LeanVM.Parameters UniStatement RecGraph.Pi1

/-- **An invariant of an `Id` loop**: kept by every step, done or not. -/
theorem id_forIn_inv {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) {U : Id β}
    (hU : forIn (m := Id) l init f = U) (P : β → Prop) (h0 : P init)
    (hs : ∀ a ∈ l, ∀ b, P b → P (Id.run (f a b)).value) : P (Id.run U) := by
  subst hU
  induction l generalizing init with
  | nil => exact h0
  | cons a t ih =>
    rw [List.forIn_cons]
    have h1 := hs a (by simp) init h0
    cases hf : Id.run (f a init) with
    | done b =>
      rw [hf] at h1
      show P (Id.run (f a init >>= fun x ↦ match x with | .done b => pure b | .yield b => forIn t b f))
      rw [idBind]
      show P (Id.run (match Id.run (f a init) with | .done b => pure b | .yield b => forIn t b f))
      rw [hf]; exact h1
    | yield b =>
      rw [hf] at h1
      show P (Id.run (f a init >>= fun x ↦ match x with | .done b => pure b | .yield b => forIn t b f))
      rw [idBind]
      show P (Id.run (match Id.run (f a init) with | .done b => pure b | .yield b => forIn t b f))
      rw [hf]
      exact ih b h1 fun a' ha' b' hb' ↦ hs a' (List.mem_cons_of_mem _ ha') b' hb'

theorem id_forIn_inv_range {β : Type} (s e : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) {U : Id β}
    (hU : forIn (m := Id) ({ start := s, stop := e, step := 1, step_pos := Nat.one_pos } : Std.Legacy.Range) init f = U)
    (P : β → Prop) (h0 : P init) (hs : ∀ a, s ≤ a → a < e → ∀ b, P b → P (Id.run (f a b)).value) : P (Id.run U) := by
  rw [forIn_range_list] at hU
  exact id_forIn_inv _ init f hU P h0 fun a ha b hb ↦ by
    rw [List.mem_range'] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact hs _ (by omega) (by omega) b hb

/-! ## The tower's leaves: 64 -/

theorem towerLeaves_size : Flock.towerLeaves.size = Flock.kBits := by
  unfold Flock.towerLeaves
  lift_lets
  extract_lets leaves0
  generalize hU : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array ℕ) _ _ _) = U
  rw [idBind]
  refine id_forIn_inv_range 0 Flock.kBits leaves0 _ hU (fun b ↦ b.size = Flock.kBits) (by simp [leaves0]) ?_
  intro i _ _ b hb
  lift_lets
  extract_lets
  generalize hP : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E) _ _ _) = Pt
  rw [idBind]
  lift_lets
  extract_lets
  generalize hV : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array ℕ) _ _ _) = V
  rw [idBind]
  show V.size = Flock.kBits
  refine id_forIn_inv_range 0 _ b _ hV (fun b ↦ b.size = Flock.kBits) hb ?_
  intro w _ _ c hc
  generalize (_ == (1 : E)) = t
  cases t <;> simp [hc]

/-! ## The network's invariant -/

/-- The variables' values: the slices `s`, then each new variable the sum of its two. -/
def netVals (s : Array E) (xors : List (ℕ × ℕ)) : Array E :=
  xors.foldl (fun vs p ↦ vs.push (vs.getD p.1 0 + vs.getD p.2 0)) s

/-- The sum of a row's variables. -/
def rowSum (vs : Array E) (row : List ℕ) : E := (row.map fun v ↦ vs.getD v 0).sum

/-- A leaf's initial row: the slices its mask names. -/
def leafRow (mask : ℕ) : List ℕ := (List.range Flock.kBits).filter fun i ↦ mask.testBit i

/-- **The network's invariant.** -/
structure NetInv (leaves : Array ℕ) (rows : Array (List ℕ)) (xors : Array (ℕ × ℕ)) : Prop where
  size : rows.size = leaves.size
  nodup : ∀ row ∈ rows.toList, row.Nodup
  lt : ∀ row ∈ rows.toList, ∀ v ∈ row, v < Flock.kBits + xors.size
  xlt : ∀ j (h : j < xors.size), xors[j].1 < Flock.kBits + j ∧ xors[j].2 < Flock.kBits + j
  sum : ∀ s : Array E, s.size = Flock.kBits → ∀ w (h : w < rows.size),
    rowSum (netVals s xors.toList) rows[w] = rowSum s (leafRow (leaves.getD w 0))

theorem netVals_size (s : Array E) (xs : List (ℕ × ℕ)) : (netVals s xs).size = s.size + xs.length := by
  unfold netVals
  induction xs generalizing s with
  | nil => simp
  | cons p t ih => rw [List.foldl_cons, ih]; simp; omega

theorem netVals_snoc (s : Array E) (xs : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    netVals s (xs ++ [p]) = (netVals s xs).push ((netVals s xs).getD p.1 0 + (netVals s xs).getD p.2 0) := by
  unfold netVals
  rw [List.foldl_append]; rfl

theorem rowSum_push (vs : Array E) (x : E) (row : List ℕ) (h : ∀ v ∈ row, v < vs.size) :
    rowSum (vs.push x) row = rowSum vs row := by
  unfold rowSum
  congr 1
  refine List.map_congr_left fun v hv ↦ ?_
  rw [getD_pushB, iteT (h v hv)]

theorem rowSum_append (vs : Array E) (l1 l2 : List ℕ) : rowSum vs (l1 ++ l2) = rowSum vs l1 + rowSum vs l2 := by
  simp [rowSum]

theorem rowSum_erase (vs : Array E) (row : List ℕ) (a : ℕ) (h : a ∈ row) :
    rowSum vs row = vs.getD a 0 + rowSum vs (row.erase a) := by
  unfold rowSum
  induction row with
  | nil => simp at h
  | cons b t ih =>
    rw [List.erase_cons]
    by_cases hb : b = a
    · subst hb; simp
    · have hbe : (b == a) = false := by simpa using hb
      rw [hbe]
      simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      have ht : a ∈ t := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hb
        · exact h'
      rw [ih ht]; ring

theorem contains_iff (row : List ℕ) (a : ℕ) : row.contains a = true ↔ a ∈ row := by simp

/-- **One greedy step keeps the invariant**: the pair is two distinct variables of one row. -/
theorem netInv_step {leaves : Array ℕ} {rows : Array (List ℕ)} {xors : Array (ℕ × ℕ)}
    (h : NetInv leaves rows xors) {a b : ℕ} (hab : a ≠ b) (ha : a < Flock.kBits + xors.size)
    (hb : b < Flock.kBits + xors.size) :
    NetInv leaves (rows.map fun row ↦ if (row.contains a && row.contains b) = true then
      (row.erase a).erase b ++ [Flock.kBits + xors.size] else row) (xors.push (a, b)) := by
  refine ⟨by simp [h.size], fun row hrow ↦ ?_, fun row hrow v hv ↦ ?_, fun j hj ↦ ?_, fun s hs w hw ↦ ?_⟩
  · simp only [Array.toList_map, List.mem_map] at hrow
    obtain ⟨r, hr, rfl⟩ := hrow
    split
    · refine List.nodup_append.mpr ⟨((h.nodup r hr).erase a).erase b, List.nodup_singleton _, ?_⟩
      intro v hv w hw
      simp only [List.mem_singleton] at hw
      subst hw
      have := h.lt r hr v (List.mem_of_mem_erase (List.mem_of_mem_erase hv))
      omega
    · exact h.nodup r hr
  · simp only [Array.toList_map, List.mem_map] at hrow
    obtain ⟨r, hr, rfl⟩ := hrow
    simp only [Array.size_push]
    split at hv
    · rcases List.mem_append.mp hv with hv' | hv'
      · have := h.lt r hr v (List.mem_of_mem_erase (List.mem_of_mem_erase hv')); omega
      · simp at hv'; omega
    · have := h.lt r hr v hv; omega
  · simp only [Array.size_push] at hj
    rw [Array.getElem_push]
    split
    · exact h.xlt j (by assumption)
    · have : j = xors.size := by omega
      subst this; exact ⟨ha, hb⟩
  · simp only [Array.size_map] at hw
    rw [← h.sum s hs w hw, Array.toList_push, netVals_snoc]
    have hsz : (netVals s xors.toList).size = Flock.kBits + xors.size := by rw [netVals_size, hs]; simp
    simp only [Array.getElem_map]
    have hr : rows[w] ∈ rows.toList := by simp
    have hlt : ∀ v ∈ rows[w], v < (netVals s xors.toList).size := fun v hv ↦ hsz ▸ h.lt _ hr v hv
    split
    · rename_i hc
      simp only [Bool.and_eq_true, contains_iff] at hc
      obtain ⟨hca, hcb⟩ := hc
      have hcb' : b ∈ rows[w].erase a := (List.mem_erase_of_ne (Ne.symm hab)).mpr hcb
      rw [rowSum_append, rowSum_push _ _ _ fun v hv ↦ hlt v (List.mem_of_mem_erase (List.mem_of_mem_erase hv)),
        rowSum_erase _ rows[w] a hca, rowSum_erase _ _ b hcb']
      simp only [rowSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [getD_pushB, iteF (by omega), iteT (by omega)]
      ring
    · exact rowSum_push _ _ _ hlt

/-- The count array's positive entries are pairs of a row's variables. -/
def CountInv (rows : List (List ℕ)) (V : ℕ) (count : Array ℕ) : Prop :=
  ∀ idx, 0 < count.getD idx 0 → ∃ row ∈ rows, ∃ x y, x < y ∧ y < row.length ∧ idx = row.getD x 0 * V + row.getD y 0

theorem getD_modifyB (c : Array ℕ) (i j : ℕ) (f : ℕ → ℕ) :
    (c.modify i f).getD j 0 = if i = j then (if j < c.size then f (c.getD j 0) else 0) else c.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : i = j
  · subst h
    by_cases h2 : i < c.size <;> simp [h2]
  · simp [h]

theorem toArray_getD (row : List ℕ) (x : ℕ) : row.toArray.getD x 0 = row.getD x 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- **The greedy network keeps its invariant.** -/
theorem xorNetwork_inv (leaves : Array ℕ) :
    NetInv leaves (Pi1.xorNetwork leaves).2.toArray (Pi1.xorNetwork leaves).1.toArray := by
  unfold Pi1.xorNetwork
  dsimp only [Id.run]
  generalize hU : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array (List ℕ) × Array (ℕ × ℕ)) _ _ _) = U
  rw [idBind]
  show NetInv leaves U.1.toList.toArray U.2.toList.toArray
  simp only [Array.toArray_toList]
  refine id_forIn_inv_range 0 4096 _ _ hU (fun b ↦ NetInv leaves b.1 b.2) ?_ ?_
  · refine ⟨by simp, fun row hrow ↦ ?_, fun row hrow v hv ↦ ?_, fun j hj ↦ by simp at hj, fun s hs w hw ↦ ?_⟩
    · simp only [Array.toList_map, List.mem_map] at hrow
      obtain ⟨m, _, rfl⟩ := hrow
      exact List.nodup_range.filter _
    · simp only [Array.toList_map, List.mem_map] at hrow
      obtain ⟨m, _, rfl⟩ := hrow
      simp only [List.mem_filter, List.mem_range] at hv
      simp; omega
    · simp only [Array.size_map] at hw
      simp only [netVals, List.foldl_nil, Array.getElem_map, leafRow,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw, Option.getD_some]
  · intro _ _ _ b hb
    generalize hC : (forIn (m := Id) (ρ := Array (List ℕ)) (β := Array ℕ) _ _ _) = C
    rw [idBind]
    generalize hB : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := ℕ × ℕ) _ _ _) = B
    rw [idBind]
    -- The count array's positive entries.
    rw [← Array.forIn_toList] at hC
    have hCI : CountInv b.1.toList (Flock.kBits + b.2.size) (Id.run C) := by
      refine id_forIn_inv _ _ _ hC (CountInv b.1.toList (Flock.kBits + b.2.size)) ?_ ?_
      · intro idx hidx
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hidx
        split at hidx <;> simp at hidx
      · intro row hrow c hc
        generalize hX : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array ℕ) _ _ _) = X
        rw [idBind]
        show CountInv b.1.toList (Flock.kBits + b.2.size) (Id.run X)
        refine id_forIn_inv_range 0 _ c _ hX _ hc ?_
        intro x _ hx c2 hc2
        generalize hY : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array ℕ) _ _ _) = Y
        rw [idBind]
        show CountInv b.1.toList (Flock.kBits + b.2.size) (Id.run Y)
        refine id_forIn_inv_range _ _ c2 _ hY _ hc2 ?_
        intro y hy1 hy2 c3 hc3
        show CountInv b.1.toList (Flock.kBits + b.2.size) (c3.modify _ _)
        intro idx hidx
        rw [getD_modifyB] at hidx
        by_cases heq : row.toArray.getD x 0 * (Flock.kBits + b.2.size) + row.toArray.getD y 0 = idx
        · simp only [List.size_toArray] at hx hy2
          exact ⟨row, hrow, x, y, by omega, hy2, by rw [← heq, toArray_getD, toArray_getD]⟩
        · rw [iteF heq] at hidx
          exact hc3 idx hidx
    -- The best entry is positive.
    have hBI : 0 < (Id.run B).2 → (Id.run C).getD (Id.run B).1 0 = (Id.run B).2 := by
      refine id_forIn_inv_range 0 _ (0, 0) _ hB (fun bm ↦ 0 < bm.2 → (Id.run C).getD bm.1 0 = bm.2)
        (fun h ↦ absurd h (by simp)) ?_
      intro at_ _ _ bm hbm
      by_cases hgt : Array.getD C at_ 0 > bm.2
      · rw [iteT hgt]; intro _; rfl
      · rw [iteF hgt]; exact hbm
    by_cases h2 : B.2 < 2
    · rw [iteT h2]
      exact hb
    · rw [iteF h2]
      have hB2 : 0 < (Id.run B).2 := by show 0 < B.2; omega
      obtain ⟨row, hrow, x, y, hxy, hy, hidx⟩ := hCI _ (by rw [hBI hB2]; exact hB2)
      have hyv : row.getD y 0 < Flock.kBits + b.2.size := by
        rw [List.getD_eq_getElem _ _ hy]; exact hb.lt row hrow _ (List.getElem_mem hy)
      have hxv : row.getD x 0 < Flock.kBits + b.2.size := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact hb.lt row hrow _ (List.getElem_mem (by omega))
      have hpos : 0 < Flock.kBits + b.2.size := by simp [Flock.kBits]
      have hdiv : (Id.run B).1 / (Flock.kBits + b.2.size) = row.getD x 0 := by
        rw [hidx, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hyv, Nat.zero_add]
      have hmod : (Id.run B).1 % (Flock.kBits + b.2.size) = row.getD y 0 := by
        rw [hidx, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hyv]
      have hne : row.getD x 0 ≠ row.getD y 0 := by
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hy]
        intro he
        have := ((hb.nodup row hrow).getElem_inj_iff).mp he
        omega
      show NetInv leaves (Array.map _ b.1) (b.2.push (B.1 / (Flock.kBits + b.2.size),
        B.1 % (Flock.kBits + b.2.size)))
      rw [show B.1 = (Id.run B).1 from rfl, hdiv, hmod]
      exact netInv_step hb hne hxv hyv

end RecGraph.Sim
