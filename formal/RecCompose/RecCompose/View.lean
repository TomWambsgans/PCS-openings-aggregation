-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.ViewDefs
import RecStatement.Spec

/-!
# What `viewOf` and `Spec.of`'s groups compute

* the slots (`mem_slots`, `slotKeys_nodup`: one per (block, role), the blocks distinct), the pairs one per slot
  (`pairsOf_getD`), the formulas every slot's, first appearance (`formulasOf_getD_idxOf`);
* `Spec.of`'s groups (`RecStatement.groupsOf`) partition the pairs' indices (`groupsOf_perm`), a group's pairs of its
  role, pull flag and formula (`groupsOf_mem`).
-/

namespace RecCompose

open RecStatement

/-! ## Folds -/

theorem foldl_add_sum {α M : Type} [AddCommMonoid M] (f : α → M) :
    ∀ (l : List α) (a : M), l.foldl (fun acc x ↦ acc + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_sum f l, List.map_cons, List.sum_cons, add_assoc]

/-! ## The slots -/

theorem mem_slots {c : RecCircuit.Circuit} {s : RecCircuit.Block × ℕ × Formula × Bool} :
    s ∈ slots c ↔ s.1 ∈ c.blocks.toList ∧ s.2.1 < (blockRoles c s.1).length ∧
      roleFormula ((blockRoles c s.1).getD s.2.1 .forward) = some s.2.2 := by
  obtain ⟨b, k, fp⟩ := s
  simp only [slots, List.mem_flatMap, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨b', hb', k', hk', fp', hfp', rfl, rfl, rfl⟩
    exact ⟨hb', hk', hfp'⟩
  · rintro ⟨hb, hk, hfp⟩
    exact ⟨b, hb, k, hk, fp, hfp, rfl, rfl, rfl⟩

/-- The slots' (block, role) keys. -/
def slotKeys (c : RecCircuit.Circuit) : List (RecCircuit.Block × ℕ) := (slots c).map fun s ↦ (s.1, s.2.1)

theorem filterMap_keys_nodup (b : RecCircuit.Block) (n : ℕ) (g : ℕ → Option (Formula × Bool)) :
    (((List.range n).filterMap fun k ↦ (g k).map fun fp ↦ (b, k, fp)).map fun s ↦ (s.1, s.2.1)).Nodup := by
  rw [List.map_filterMap]
  refine List.Nodup.filterMap (fun k k' x hx hx' ↦ ?_) List.nodup_range
  simp only [Option.mem_def, Option.map_map, Option.map_eq_some_iff, Function.comp] at hx hx'
  obtain ⟨_, -, rfl⟩ := hx
  obtain ⟨_, -, h⟩ := hx'
  exact (Prod.mk.inj h).2.symm

/-- **The slots' keys are distinct**, the blocks being so. -/
theorem slotKeys_nodup {c : RecCircuit.Circuit} (hb : c.blocks.toList.Nodup) : (slotKeys c).Nodup := by
  unfold slotKeys slots
  rw [List.map_flatMap]
  refine List.nodup_flatMap.mpr ⟨fun b _ ↦ filterMap_keys_nodup b _ _, ?_⟩
  refine hb.imp fun {b b'} hne ↦ ?_
  intro x hx hx'
  simp only [List.mem_map, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hx hx'
  obtain ⟨_, ⟨_, -, _, -, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨_, -, _, -, rfl⟩, h⟩ := hx'
  exact hne (Prod.mk.inj h).1.symm

theorem slotKeys_length (c : RecCircuit.Circuit) : (slotKeys c).length = (slots c).length := by
  simp [slotKeys]

/-! ## The formulas and the pairs -/

theorem mem_foldl_addFormula {α : Type} (g : α → Formula) :
    ∀ (l : List α) (acc : List Formula) (x : Formula),
      x ∈ l.foldl (fun fs s ↦ addFormula fs (g s)) acc ↔ x ∈ acc ∨ ∃ s ∈ l, g s = x
  | [], acc, x => by simp
  | s :: l, acc, x => by
    rw [List.foldl_cons, mem_foldl_addFormula g l]
    unfold addFormula
    split_ifs with h
    · constructor
      · rintro (h1 | ⟨s', hs', rfl⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨s', List.mem_cons_of_mem _ hs', rfl⟩
      · rintro (h1 | ⟨s', hs', rfl⟩)
        · exact Or.inl h1
        · rcases List.mem_cons.mp hs' with rfl | hs'
          · exact Or.inl h
          · exact Or.inr ⟨s', hs', rfl⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h1 | rfl) | ⟨s', hs', rfl⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨s, Or.inl rfl, rfl⟩
        · exact Or.inr ⟨s', Or.inr hs', rfl⟩
      · rintro (h1 | ⟨s', (rfl | hs'), rfl⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr ⟨s', hs', rfl⟩

/-- Every slot's formula is among the formulas. -/
theorem mem_formulasOf {c : RecCircuit.Circuit} {s : RecCircuit.Block × ℕ × Formula × Bool} (hs : s ∈ slots c) :
    s.2.2.1 ∈ formulasOf c :=
  (mem_foldl_addFormula (fun s ↦ s.2.2.1) (slots c) [] _).mpr (Or.inr ⟨s, hs, rfl⟩)

theorem pairsOf_length (c : RecCircuit.Circuit) : (pairsOf c).length = (slots c).length := by
  simp [pairsOf]

/-- **Pair `i`** is slot `i`'s: its block's rows, its role, its formula's first appearance, its pull flag. -/
theorem pairsOf_getD (c : RecCircuit.Circuit) {i : ℕ} (hi : i < (slots c).length) :
    (pairsOf c).getD i default =
      ⟨((slots c).getD i default).1.row, ((slots c).getD i default).1.logRows, ((slots c).getD i default).2.1,
        (formulasOf c).idxOf ((slots c).getD i default).2.2.1, ((slots c).getD i default).2.2.2⟩ := by
  simp [pairsOf, List.getD_eq_getElem?_getD, hi]

theorem getD_mem_of_lt {α : Type} {l : List α} {i : ℕ} (d : α) (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- **Pair `i`'s formula** is slot `i`'s. -/
theorem formulasOf_getD_pair (c : RecCircuit.Circuit) {i : ℕ} (hi : i < (slots c).length) :
    (formulasOf c).getD ((pairsOf c).getD i default).formula default = ((slots c).getD i default).2.2.1 := by
  rw [pairsOf_getD c hi]
  have hm := mem_formulasOf (getD_mem_of_lt default hi)
  show (formulasOf c).getD ((formulasOf c).idxOf ((slots c).getD i default).2.2.1) default = _
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr hm)]
  exact List.getElem_idxOf _

/-! ## `Spec.of`'s groups -/

/-- `groupsOf`'s step. -/
def gStep (c : Circuit) (gs : List Group) (i : ℕ) : List Group :=
  let p := c.pairs.getD i default
  let f := c.formulas.getD p.formula default
  match gs.findIdx? (fun g ↦ g.role = p.role ∧ g.pulls = p.pulls ∧ g.formula = f) with
  | some j => gs.modify j fun g ↦ { g with pairs := g.pairs ++ [i] }
  | none => gs ++ [⟨p.role, f, p.pulls, [i]⟩]

theorem groupsOf_eq (c : Circuit) : groupsOf c = (List.range c.pairs.length).foldl (gStep c) [] := rfl

/-- What every group's pairs share with it, and the pairs seen so far. -/
def GInv (c : Circuit) (k : ℕ) (gs : List Group) : Prop :=
  (gs.flatMap (·.pairs)).Perm (List.range k) ∧
    ∀ g ∈ gs, ∀ i ∈ g.pairs, i < k ∧ g.role = (c.pairs.getD i default).role ∧
      g.pulls = (c.pairs.getD i default).pulls ∧ g.formula = c.formulas.getD (c.pairs.getD i default).formula default

theorem flatMap_modify_perm (k : ℕ) :
    ∀ (l : List Group) (j : ℕ), j < l.length →
      ((l.modify j fun g ↦ { g with pairs := g.pairs ++ [k] }).flatMap (·.pairs)).Perm (l.flatMap (·.pairs) ++ [k])
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: l, 0, _ => by
    simp only [List.modify_zero_cons, List.flatMap_cons, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  | a :: l, j + 1, h => by
    simp only [List.modify_succ_cons, List.flatMap_cons, List.append_assoc]
    exact List.Perm.append_left _ (flatMap_modify_perm k l j (by simpa using h))

theorem forall_mem_modify (P : Group → Prop) (f : Group → Group) :
    ∀ (l : List Group) (j : ℕ), (∀ g ∈ l, P g) → (∀ h : j < l.length, P (f l[j])) →
      ∀ g ∈ l.modify j f, P g
  | [], _, _, _ => by simp
  | a :: l, 0, hl, hj => by
    simp only [List.modify_zero_cons, List.mem_cons]
    rintro g (rfl | hg)
    · exact hj (by simp)
    · exact hl g (List.mem_cons_of_mem _ hg)
  | a :: l, j + 1, hl, hj => by
    simp only [List.modify_succ_cons, List.mem_cons]
    rintro g (rfl | hg)
    · exact hl _ (List.mem_cons_self ..)
    · exact forall_mem_modify P f l j (fun g hg ↦ hl g (List.mem_cons_of_mem _ hg))
        (fun h ↦ hj (by simpa using h)) g hg

theorem gInv_step (c : Circuit) {k : ℕ} {gs : List Group} (h : GInv c k gs) : GInv c (k + 1) (gStep c gs k) := by
  obtain ⟨hp, hm⟩ := h
  unfold gStep
  dsimp only
  split
  · rename_i j hj
    obtain ⟨hjl, hpj, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
    simp only [decide_eq_true_eq] at hpj
    refine ⟨(flatMap_modify_perm k gs j hjl).trans (by rw [List.range_succ]; exact hp.append_right _), ?_⟩
    refine forall_mem_modify _ _ gs j (fun g hg i hi ↦ ?_) (fun h i hi ↦ ?_)
    · obtain ⟨h1, h2⟩ := hm g hg i hi
      exact ⟨by omega, h2⟩
    · simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · obtain ⟨h1, h2⟩ := hm _ (List.getElem_mem h) i hi
        exact ⟨by omega, h2⟩
      · exact ⟨by omega, hpj.1, hpj.2.1, hpj.2.2⟩
  · refine ⟨?_, ?_⟩
    · rw [List.flatMap_append, List.range_succ]
      exact hp.append (by simp)
    · intro g hg i hi
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · obtain ⟨h1, h2⟩ := hm g hg i hi
        exact ⟨by omega, h2⟩
      · simp only [List.mem_singleton] at hi
        subst hi
        exact ⟨by omega, rfl, rfl, rfl⟩

theorem gInv_foldl (c : Circuit) : ∀ k, GInv c k ((List.range k).foldl (gStep c) [])
  | 0 => ⟨by simp, by simp⟩
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact gInv_step c (gInv_foldl c k)

/-- **The groups partition the pairs' indices.** -/
theorem groupsOf_perm (c : Circuit) : ((groupsOf c).flatMap (·.pairs)).Perm (List.range c.pairs.length) :=
  (gInv_foldl c _).1

/-- **A group's pairs** are of its role, its pull flag and its formula. -/
theorem groupsOf_mem (c : Circuit) {g : Group} (hg : g ∈ groupsOf c) {i : ℕ} (hi : i ∈ g.pairs) :
    i < c.pairs.length ∧ g.role = (c.pairs.getD i default).role ∧ g.pulls = (c.pairs.getD i default).pulls ∧
      g.formula = c.formulas.getD (c.pairs.getD i default).formula default :=
  (gInv_foldl c _).2 g hg i hi

end RecCompose
