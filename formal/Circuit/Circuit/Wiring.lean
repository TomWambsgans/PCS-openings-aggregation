/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-/
import Circuit.Semantics

/-!
# The wiring σ

`finish` builds σ by `join`ing cells to the cycles of their slots (a constant, or a row's output),
in a fixed order: every row's `V` cell, then every row's `X`, `Y`, `C` cells. `JoinInv` is what the
joins keep: each slot's cells so far, in order, `l`, have `σ l[i] = l[i + 1 mod |l|]`, and a cell not
yet joined is fixed. So, once every cell is joined, σ is the cyclic successor in its slot's list
(`joins_inv`), a permutation of the cells (`cyc_lt`, `cyc_inj`) whose cycles are the slots
(`cyc_reach`).
-/

namespace PcsCircuit

theorem getD_set! {α : Type} (a : Array α) (i j : Nat) (x d : α) :
    (a.set! i x).getD j d = if i = j ∧ i < a.size then x else a.getD j d := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; by_cases hi : i < a.size <;> simp [hi]
  · simp [h]

theorem size_set! {α : Type} (a : Array α) (i : Nat) (x : α) : (a.set! i x).size = a.size := by
  simp [Array.set!]

theorem getD_set!_ne {α : Type} (a : Array α) {i j : Nat} (x d : α) (h : i ≠ j) :
    (a.set! i x).getD j d = a.getD j d := by
  rw [getD_set!, if_neg (fun h' => h h'.1)]

theorem getD_set!_eq {α : Type} (a : Array α) {i : Nat} (x d : α) (h : i < a.size) :
    (a.set! i x).getD i d = x := by
  rw [getD_set!, if_pos ⟨rfl, h⟩]

/-- The cells joined to slot `a`, in order. -/
def cellsOf (P : List (Nat × Nat)) (a : Nat) : List Nat := (P.filter fun p => p.1 == a).map Prod.snd

theorem cellsOf_append (P : List (Nat × Nat)) (a c b : Nat) :
    cellsOf (P ++ [(a, c)]) b = cellsOf P b ++ (if a = b then [c] else []) := by
  unfold cellsOf
  by_cases h : a = b
  · subst h; simp
  · simp [h]

theorem mem_cellsOf {P : List (Nat × Nat)} {a c : Nat} (h : c ∈ cellsOf P a) : (a, c) ∈ P := by
  unfold cellsOf at h
  simp only [List.mem_map, List.mem_filter, beq_iff_eq] at h
  obtain ⟨⟨a', c'⟩, ⟨hp, ha⟩, hc⟩ := h
  simp only at ha hc
  subst ha hc
  exact hp

theorem mem_cellsOf_of_mem {P : List (Nat × Nat)} {a c : Nat} (h : (a, c) ∈ P) : c ∈ cellsOf P a := by
  unfold cellsOf
  exact List.mem_map.mpr ⟨(a, c), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩

/-- Each cell is joined to one slot. -/
def OneSlot (P : List (Nat × Nat)) : Prop := (P.map Prod.snd).Nodup

theorem cellsOf_nodup {P : List (Nat × Nat)} (h : OneSlot P) (a : Nat) : (cellsOf P a).Nodup := by
  unfold cellsOf OneSlot at *
  exact h.sublist (List.filter_sublist.map Prod.snd)

theorem slot_unique {P : List (Nat × Nat)} (h : OneSlot P) {a b c : Nat} (ha : (a, c) ∈ P)
    (hb : (b, c) ∈ P) : a = b := by
  unfold OneSlot at h
  induction P with
  | nil => simp at ha
  | cons p P ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [← ha] at hb; cases hb; rfl
    · exact absurd ⟨_, hb, by rw [← ha]⟩ h.1
    · exact absurd ⟨_, ha, by rw [← hb]⟩ h.1
    · exact ih h.2 ha hb

/-- σ is the cyclic successor in `l`. -/
def Cyclic (sigma : Nat → Nat) (l : List Nat) : Prop :=
  ∀ i < l.length, sigma (l.getD i 0) = l.getD ((i + 1) % l.length) 0

/-- What the joins of `P` leave: the first and last cell of each slot, σ the cyclic successor in
each slot's list, the other cells fixed. -/
structure JoinInv (P : List (Nat × Nat)) (S N : Nat) (st : Joins) : Prop where
  first_size : st.first.size = S
  last_size : st.last.size = S
  sigma_size : st.sigma.size = N
  first : ∀ a < S, st.first.getD a none = (cellsOf P a).head?
  last : ∀ a < S, st.last.getD a none = (cellsOf P a).getLast?
  cyc : ∀ a < S, Cyclic (fun c => st.sigma.getD c 0) (cellsOf P a)
  fixed : ∀ c < N, c ∉ P.map Prod.snd → st.sigma.getD c 0 = c

theorem joinInv_nil (S N : Nat) :
    JoinInv [] S N ⟨Array.replicate S none, Array.replicate S none, Array.range N⟩ := by
  refine ⟨by simp, by simp, by simp, fun a ha => ?_, fun a ha => ?_, fun a _ i hi => ?_, fun c hc _ => ?_⟩
  · simp [cellsOf, Array.getD_eq_getD_getElem?, ha]
  · simp [cellsOf, Array.getD_eq_getD_getElem?, ha]
  · simp [cellsOf] at hi
  · simp [Array.getD_eq_getD_getElem?, Array.getElem?_range, hc]

theorem getD_append_left' (l l' : List Nat) (i : Nat) (h : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (l l' : List Nat) (i : Nat) (h : l.length ≤ i) :
    (l ++ l').getD i 0 = l'.getD (i - l.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_eq' {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_mem' {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [getD_eq' h]; exact List.getElem_mem h

theorem getD_inj' {l : List Nat} (hl : l.Nodup) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (h : l.getD i 0 = l.getD j 0) : i = j := by
  rw [getD_eq' hi, getD_eq' hj] at h
  exact (List.Nodup.getElem_inj hl).mp h

theorem exists_getD' {l : List Nat} {x : Nat} (h : x ∈ l) : ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, getD_eq' hi⟩

/-- **A join keeps the invariant**: cell `c`, new, joins slot `a`. -/
theorem joinInv_join {P : List (Nat × Nat)} {S N a c : Nat} {st : Joins} (h : JoinInv P S N st)
    (hP : OneSlot (P ++ [(a, c)])) (hPN : ∀ p ∈ P ++ [(a, c)], p.1 < S ∧ p.2 < N) :
    JoinInv (P ++ [(a, c)]) S N (join st a c) := by
  have haS := (hPN (a, c) (by simp)).1
  have hcN := (hPN (a, c) (by simp)).2
  have hcP : c ∉ P.map Prod.snd := by
    unfold OneSlot at hP; simp only [List.map_append, List.map_cons, List.map_nil] at hP
    exact fun hc => (List.nodup_append.mp hP).2.2 c hc c (by simp) rfl
  have hP0 : OneSlot P := by
    unfold OneSlot at *; simp only [List.map_append] at hP; exact (List.nodup_append.mp hP).1
  have hcl : ∀ b, c ∉ cellsOf P b := fun b hc => hcP (List.mem_map.mpr ⟨_, mem_cellsOf hc, rfl⟩)
  have hnew : ∀ x, x ∉ (P ++ [(a, c)]).map Prod.snd → x ≠ c ∧ x ∉ P.map Prod.snd := fun x hx =>
    ⟨fun h' => hx (by rw [h']; simp), fun h' => hx (by simp only [List.map_append, List.mem_append]; exact Or.inl h')⟩
  obtain ⟨first, last, sigma⟩ := st
  obtain ⟨hfs, hls, hss, hf, hl, hcyc, hfix⟩ := h
  simp only at hfs hls hss hf hl hcyc hfix
  have hfa := hf a haS
  unfold join
  simp only
  cases hfirst : first.getD a none with
  | none =>
    rw [hfirst] at hfa
    have hnil : cellsOf P a = [] := List.head?_eq_none_iff.mp hfa.symm
    refine ⟨by simp [size_set!, hfs], by simp [size_set!, hls], by simp [size_set!, hss],
      fun b hb => ?_, fun b hb => ?_, fun b hb i hi => ?_, fun x hxN hx => ?_⟩
    · rw [getD_set!, cellsOf_append]
      by_cases hab : a = b
      · subst hab; simp [hnil, hfs, haS]
      · simp [hab, hf b hb]
    · rw [getD_set!, cellsOf_append]
      by_cases hab : a = b
      · subst hab; simp [hnil, hls, haS]
      · simp [hab, hl b hb]
    · simp only [cellsOf_append] at hi ⊢
      by_cases hab : a = b
      · subst hab
        simp only [hnil, List.nil_append, if_true, List.length_singleton] at hi ⊢
        have : i = 0 := by omega
        subst this
        simp only [List.getD_cons_zero, Nat.zero_add, Nat.mod_self]
        exact getD_set!_eq _ _ _ (by rw [hss]; exact hcN)
      · simp only [hab, if_false, List.append_nil] at hi ⊢
        rw [getD_set!_ne _ _ _ (fun h' => hcl b (by rw [h']; exact getD_mem' hi))]
        exact hcyc b hb i hi
    · obtain ⟨hxc, hxP⟩ := hnew x hx
      rw [getD_set!_ne _ _ _ (Ne.symm hxc)]
      exact hfix x hxN hxP
  | some f =>
    rw [hfirst] at hfa
    have hla := hl a haS
    have hcya := hcyc a haS
    obtain ⟨l, hlP⟩ : ∃ l, cellsOf P a = l := ⟨_, rfl⟩
    rw [hlP] at hfa hla hcya
    have hlnd : l.Nodup := hlP ▸ cellsOf_nodup hP0 a
    have hcl' : c ∉ l := hlP ▸ hcl a
    have hlen : 0 < l.length := by
      cases l with
      | nil => simp at hfa
      | cons _ _ => simp
    have hf0 : f = l.getD 0 0 := by
      cases l with
      | nil => simp at hfa
      | cons y ys => simp at hfa; simp [hfa]
    have hprev : (last.getD a none).getD 0 = l.getD (l.length - 1) 0 := by
      rw [hla, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
    rw [hprev]
    have hprev_mem : l.getD (l.length - 1) 0 ∈ l := getD_mem' (by omega)
    have hprevP : (a, l.getD (l.length - 1) 0) ∈ P := mem_cellsOf (hlP ▸ hprev_mem)
    have hprevN : l.getD (l.length - 1) 0 < N :=
      (hPN (a, l.getD (l.length - 1) 0) (List.mem_append_left _ hprevP)).2
    have hpc : l.getD (l.length - 1) 0 ≠ c := fun h' => hcl' (h' ▸ hprev_mem)
    have hother : ∀ b, b ≠ a → ∀ x ∈ cellsOf P b, x ≠ c ∧ x ≠ l.getD (l.length - 1) 0 := by
      intro b hba x hx
      refine ⟨fun h' => hcl b (by rw [← h']; exact hx), fun h' => hba ?_⟩
      exact slot_unique hP0 (mem_cellsOf hx) (by rw [h']; exact hprevP)
    have hsz1 : (sigma.set! (l.getD (l.length - 1) 0) c).size = N := by rw [size_set!, hss]
    refine ⟨hfs, by simp [size_set!, hls], by rw [size_set!, hsz1],
      fun b hb => ?_, fun b hb => ?_, fun b hb i hi => ?_, fun x hxN hx => ?_⟩
    · rw [hf b hb, cellsOf_append]
      by_cases hab : a = b
      · subst hab; rw [hlP]; simp only [if_true]
        cases l with
        | nil => exact absurd hlen (by simp)
        | cons _ _ => rfl
      · simp [hab]
    · rw [getD_set!, cellsOf_append]
      by_cases hab : a = b
      · subst hab; simp [hls, haS, hlP]
      · simp [hab, hl b hb]
    · simp only [cellsOf_append] at hi ⊢
      by_cases hab : a = b
      · subst hab
        simp only [hlP, if_true, List.length_append, List.length_singleton] at hi ⊢
        by_cases hi1 : i < l.length - 1
        · rw [getD_append_left' _ _ _ (by omega), getD_append_left' _ _ _ (by
            rw [Nat.mod_eq_of_lt (by omega)]; omega)]
          have hxne : l.getD i 0 ≠ c := fun h' => hcl' (h' ▸ getD_mem' (by omega))
          have hxne' : l.getD i 0 ≠ l.getD (l.length - 1) 0 :=
            fun h' => by have := getD_inj' hlnd (by omega) (by omega) h'; omega
          have hci : sigma.getD (l.getD i 0) 0 = l.getD ((i + 1) % l.length) 0 := hcya i (by omega)
          rw [getD_set!_ne _ _ _ (Ne.symm hxne), getD_set!_ne _ _ _ (Ne.symm hxne'), hci,
            Nat.mod_eq_of_lt (show i + 1 < l.length by omega), Nat.mod_eq_of_lt (show i + 1 < l.length + 1 by omega)]
        · by_cases hi2 : i = l.length - 1
          · subst hi2
            rw [getD_append_left' _ _ _ (by omega), getD_set!_ne _ _ _ (Ne.symm hpc),
              getD_set!_eq _ _ _ (by rw [hss]; exact hprevN),
              show (l.length - 1 + 1) % (l.length + 1) = l.length by
                rw [Nat.sub_add_cancel hlen, Nat.mod_eq_of_lt (by omega)],
              getD_append_right' _ _ _ (Nat.le_refl _), Nat.sub_self]
            rfl
          · have hi3 : i = l.length := by omega
            subst hi3
            rw [getD_append_right' _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero,
              getD_set!_eq _ _ _ (by rw [hsz1]; exact hcN), Nat.mod_self, getD_append_left' _ _ _ hlen, hf0]
      · simp only [hab, if_false, List.append_nil] at hi ⊢
        obtain ⟨h1, h2⟩ := hother b (Ne.symm hab) _ (getD_mem' hi)
        rw [getD_set!_ne _ _ _ (Ne.symm h1), getD_set!_ne _ _ _ (Ne.symm h2)]
        exact hcyc b hb i hi
    · obtain ⟨hxc, hxP⟩ := hnew x hx
      have hxp : x ≠ l.getD (l.length - 1) 0 := fun h' =>
        hxP (List.mem_map.mpr ⟨(a, x), by rw [h']; exact hprevP, rfl⟩)
      rw [getD_set!_ne _ _ _ (Ne.symm hxc), getD_set!_ne _ _ _ (Ne.symm hxp)]
      exact hfix x hxN hxP

/-- **The joins of a list** keep the invariant. -/
theorem joinInv_foldl {S N : Nat} : ∀ (Q P : List (Nat × Nat)) (st : Joins), JoinInv P S N st →
    OneSlot (P ++ Q) → (∀ p ∈ P ++ Q, p.1 < S ∧ p.2 < N) →
    JoinInv (P ++ Q) S N (Q.foldl (fun st p => join st p.1 p.2) st)
  | [], P, st, h, _, _ => by rw [List.append_nil]; exact h
  | (a, c) :: Q, P, st, h, hP, hPN => by
    rw [List.foldl_cons]
    have e : P ++ (a, c) :: Q = (P ++ [(a, c)]) ++ Q := by rw [List.append_assoc]; rfl
    rw [e] at hP hPN ⊢
    have hP1 : OneSlot (P ++ [(a, c)]) := by
      unfold OneSlot at hP ⊢; rw [List.map_append] at hP; exact (List.nodup_append.mp hP).1
    exact joinInv_foldl Q (P ++ [(a, c)]) _
      (joinInv_join h hP1 fun p hp => hPN p (List.mem_append_left _ hp)) hP hPN

/-! ## Cycles -/

/-- `f` iterated `k` times. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => iter f k (f x)

theorem cyc_iterate {sigma : Nat → Nat} {l : List Nat} (hl : 0 < l.length) (h : Cyclic sigma l) :
    ∀ k i, i < l.length → iter sigma k (l.getD i 0) = l.getD ((i + k) % l.length) 0
  | 0, i, hi => by simp [Nat.mod_eq_of_lt hi, iter]
  | k + 1, i, hi => by
    show iter sigma k (sigma (l.getD i 0)) = _
    rw [h i hi, cyc_iterate hl h k _ (Nat.mod_lt _ hl)]
    congr 1
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_comm 1 k]

/-- **Any two cells of a slot are on one cycle.** -/
theorem cyc_reach {sigma : Nat → Nat} {l : List Nat} (h : Cyclic sigma l) {x y : Nat} (hx : x ∈ l)
    (hy : y ∈ l) : ∃ k, iter sigma k x = y := by
  obtain ⟨i, hi, rfl⟩ := exists_getD' hx
  obtain ⟨j, hj, rfl⟩ := exists_getD' hy
  have hl : 0 < l.length := by omega
  refine ⟨j + l.length - i, ?_⟩
  rw [cyc_iterate hl h _ i hi]
  congr 1
  rw [show i + (j + l.length - i) = j + l.length by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

/-- The cyclic successor stays in the list. -/
theorem cyc_mem {sigma : Nat → Nat} {l : List Nat} (h : Cyclic sigma l) {x : Nat} (hx : x ∈ l) :
    sigma x ∈ l := by
  obtain ⟨i, hi, rfl⟩ := exists_getD' hx
  rw [h i hi]; exact getD_mem' (Nat.mod_lt _ (by omega))

/-- The cyclic successor is injective on a list without repetitions. -/
theorem cyc_inj {sigma : Nat → Nat} {l : List Nat} (hnd : l.Nodup) (h : Cyclic sigma l) {x y : Nat}
    (hx : x ∈ l) (hy : y ∈ l) (hxy : sigma x = sigma y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := exists_getD' hx
  obtain ⟨j, hj, rfl⟩ := exists_getD' hy
  rw [h i hi, h j hj] at hxy
  have := getD_inj' hnd (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hxy
  have : i = j := by
    rcases Nat.lt_or_ge (i + 1) l.length with h1 | h1 <;> rcases Nat.lt_or_ge (j + 1) l.length with h2 | h2
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this; omega
    · rw [Nat.mod_eq_of_lt h1, show j + 1 = l.length by omega, Nat.mod_self] at this; omega
    · rw [show i + 1 = l.length by omega, Nat.mod_self, Nat.mod_eq_of_lt h2] at this; omega
    · omega
  rw [this]

end PcsCircuit
