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

/-! ## The wiring of `finish` -/

/-- The joins of the `V` cells: row `r`'s output cell `4 r + 3` to slot `2 + r`. -/
def outJoins (n : Nat) : List (Nat × Nat) := (List.range n).map fun r => (2 + r, 4 * r + 3)

/-- The joins of the reading cells: row `r`'s `X`, `Y`, `C` cells to the slots of what they read. -/
def readJoins (rows : Array Row) (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun r =>
    [(slot (rows.getD r .idle).x, 4 * r), (slot (rows.getD r .idle).y, 4 * r + 1),
      (slot (rows.getD r .idle).c, 4 * r + 2)]

theorem wiring_eq (rows : Array Row) :
    wiring rows = ((outJoins rows.size ++ readJoins rows rows.size).foldl (fun st p => join st p.1 p.2)
      ⟨Array.replicate (rows.size + 2) none, Array.replicate (rows.size + 2) none, Array.range (4 * rows.size)⟩).sigma := by
  unfold wiring outJoins readJoins
  rw [List.foldl_append, List.foldl_map, List.foldl_flatMap]
  rfl

/-- The slot cell `c` joins: its row's for a `V` cell, what it reads otherwise. -/
def slotOfCell (rows : Array Row) (c : Nat) : Nat :=
  if c % 4 = 0 then slot (rows.getD (c / 4) .idle).x
  else if c % 4 = 1 then slot (rows.getD (c / 4) .idle).y
  else if c % 4 = 2 then slot (rows.getD (c / 4) .idle).c
  else 2 + c / 4

theorem mem_joins (rows : Array Row) (n c : Nat) (hc : c < 4 * n) :
    (slotOfCell rows c, c) ∈ outJoins n ++ readJoins rows n := by
  unfold slotOfCell outJoins readJoins
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
    List.mem_nil_iff, or_false, Prod.mk.injEq]
  by_cases h3 : c % 4 = 3
  · refine Or.inl ⟨c / 4, by omega, ?_, by omega⟩
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · refine Or.inr ⟨c / 4, by omega, ?_⟩
    by_cases h0 : c % 4 = 0
    · exact Or.inl ⟨by rw [if_pos h0], by omega⟩
    · by_cases h1 : c % 4 = 1
      · exact Or.inr (Or.inl ⟨by rw [if_neg h0, if_pos h1], by omega⟩)
      · exact Or.inr (Or.inr ⟨by rw [if_neg h0, if_neg h1, if_pos (by omega)], by omega⟩)

theorem joins_bounds (rows : Array Row) (n : Nat)
    (hsrc : ∀ r < n, slot (rows.getD r .idle).x < n + 2 ∧ slot (rows.getD r .idle).y < n + 2 ∧
      slot (rows.getD r .idle).c < n + 2) :
    ∀ p ∈ outJoins n ++ readJoins rows n, p.1 < n + 2 ∧ p.2 < 4 * n := by
  intro p hp
  unfold outJoins readJoins at hp
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
    List.mem_nil_iff, or_false] at hp
  rcases hp with ⟨r, hr, rfl⟩ | ⟨r, hr, hp⟩
  · simp only; omega
  · obtain ⟨h1, h2, h3⟩ := hsrc r hr
    rcases hp with rfl | rfl | rfl <;> simp only <;> omega

theorem readCells_mem {m x : Nat} (h : x ∈ (List.range m).flatMap fun r => [4 * r, 4 * r + 1, 4 * r + 2]) :
    x < 4 * m ∧ x % 4 ≠ 3 := by
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at h
  obtain ⟨r, hr, hx⟩ := h
  rcases hx with rfl | rfl | rfl <;> omega

theorem readCells_nodup : ∀ m : Nat, ((List.range m).flatMap fun r => [4 * r, 4 * r + 1, 4 * r + 2]).Nodup
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append]
    refine List.nodup_append.mpr ⟨readCells_nodup m, ?_, fun x hx y hy => ?_⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      omega
    · have := (readCells_mem hx).1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_nil_iff,
        or_false] at hy
      rcases hy with rfl | rfl | rfl <;> omega

theorem joins_oneSlot (rows : Array Row) (n : Nat) : OneSlot (outJoins n ++ readJoins rows n) := by
  unfold OneSlot outJoins readJoins
  rw [List.map_append, List.map_map, List.map_flatMap]
  have e : ((List.range n).flatMap fun r => List.map Prod.snd
      [(slot (rows.getD r .idle).x, 4 * r), (slot (rows.getD r .idle).y, 4 * r + 1),
        (slot (rows.getD r .idle).c, 4 * r + 2)]) =
      (List.range n).flatMap fun r => [4 * r, 4 * r + 1, 4 * r + 2] := by
    simp
  rw [e]
  refine List.nodup_append.mpr ⟨?_, readCells_nodup n, fun x hx y hy => ?_⟩
  · exact List.nodup_range.map (fun r => 4 * r + 3) (fun a b hab h => hab (by omega))
  · have := (readCells_mem hy).2
    simp only [List.mem_map, List.mem_range, Function.comp] at hx
    obtain ⟨r, _, rfl⟩ := hx
    omega

/-- **The wiring of `finish`**: for rows reading rows below their number of rows, σ is, on every
cell, the cyclic successor in its slot's list of cells. -/
theorem wiring_inv (rows : Array Row)
    (hsrc : ∀ r < rows.size, slot (rows.getD r .idle).x < rows.size + 2 ∧
      slot (rows.getD r .idle).y < rows.size + 2 ∧ slot (rows.getD r .idle).c < rows.size + 2) :
    ∃ st : Joins, st.sigma = wiring rows ∧
      JoinInv (outJoins rows.size ++ readJoins rows rows.size) (rows.size + 2) (4 * rows.size) st := by
  refine ⟨_, (wiring_eq rows).symm, ?_⟩
  have h := joinInv_foldl (S := rows.size + 2) (N := 4 * rows.size) (outJoins rows.size ++ readJoins rows rows.size)
    [] _ (joinInv_nil _ _) (by rw [List.nil_append]; exact joins_oneSlot rows rows.size)
    (by rw [List.nil_append]; exact joins_bounds rows rows.size hsrc)
  rw [List.nil_append] at h
  exact h

/-- **σ of `finish`** on the cells `c < 4 n`: it maps them among themselves, injectively, and
any two cells of one slot are on one cycle. -/
theorem wiring_perm (rows : Array Row)
    (hsrc : ∀ r < rows.size, slot (rows.getD r .idle).x < rows.size + 2 ∧
      slot (rows.getD r .idle).y < rows.size + 2 ∧ slot (rows.getD r .idle).c < rows.size + 2) :
    (∀ c < 4 * rows.size, (wiring rows).getD c 0 < 4 * rows.size) ∧
    (∀ c < 4 * rows.size, ∀ d < 4 * rows.size, (wiring rows).getD c 0 = (wiring rows).getD d 0 → c = d) ∧
    (∀ c < 4 * rows.size, ∀ d < 4 * rows.size, slotOfCell rows c = slotOfCell rows d →
      ∃ k, iter (fun x => (wiring rows).getD x 0) k c = d) := by
  obtain ⟨st, hst, hinv⟩ := wiring_inv rows hsrc
  rw [← hst]
  have hP := joins_oneSlot rows rows.size
  have hB := joins_bounds rows rows.size hsrc
  have hmem : ∀ c < 4 * rows.size, c ∈ cellsOf (outJoins rows.size ++ readJoins rows rows.size) (slotOfCell rows c) :=
    fun c hc => mem_cellsOf_of_mem (mem_joins rows rows.size c hc)
  have hS : ∀ c < 4 * rows.size, slotOfCell rows c < rows.size + 2 :=
    fun c hc => (hB _ (mem_joins rows rows.size c hc)).1
  refine ⟨fun c hc => ?_, fun c hc d hd hcd => ?_, fun c hc d hd hcd => ?_⟩
  · have := cyc_mem (hinv.cyc _ (hS c hc)) (hmem c hc)
    exact (hB _ (mem_cellsOf this)).2
  · have h1 := cyc_mem (hinv.cyc _ (hS c hc)) (hmem c hc)
    have h2 := cyc_mem (hinv.cyc _ (hS d hd)) (hmem d hd)
    rw [hcd] at h1
    have e := slot_unique hP (mem_cellsOf h1) (mem_cellsOf h2)
    rw [← e] at h2
    exact cyc_inj (cellsOf_nodup hP _) (hinv.cyc _ (hS c hc)) (hmem c hc) (by rw [e]; exact hmem d hd) hcd
  · have hd' := hmem d hd
    rw [← hcd] at hd'
    exact cyc_reach (hinv.cyc _ (hS c hc)) (hmem c hc) hd'

end PcsCircuit
