-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.ViewDefs
import RecCircuit.Piop

/-!
# `validB` decides `RecPiop.Circuit.Valid` of `toPiop`

**`validB_sound`**: if the loops of `validB` (`ViewDefs.lean`) accept a circuit, its PIOP form is valid
(`RecPiop.Circuit.Valid`): the regions `W` wide and reading their row, the blocks aligned, in range, their regions
existing and disjoint, the ports distinct and exactly the holes (every hole of every block a port's position), each
port pushing to its outside tag, `σ` on the non-holes inside, injective (`sigmaMarks`: no tag marked twice) and onto the
non-holes, no formula reading a hole (no role of a hole's row reads its cell), `κ` only at expression slots.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open Primitives

/-! ## Arrays and lists -/

theorem arr_all_mem {α : Type} {p : α → Bool} {a : Array α} (h : a.all p = true) {x : α} (hx : x ∈ a.toList) :
    p x = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := Array.all_eq_true.mp h i (by simpa using hi)
  simpa using this

theorem arr_any_mem {α : Type} {p : α → Bool} {a : Array α} (h : a.any p = true) : ∃ x ∈ a.toList, p x = true := by
  obtain ⟨i, hi, hp⟩ := Array.any_eq_true.mp h
  exact ⟨a[i], by simp, hp⟩

theorem arr_getD_mem_or {α : Type} (a : Array α) (k : ℕ) (d : α) : a.getD k d ∈ a.toList ∨ a.getD k d = d := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases hk : k < a.size
  · rw [Array.getElem?_eq_getElem hk]
    exact Or.inl (by simp)
  · rw [Array.getElem?_eq_none (by omega)]
    exact Or.inr rfl

/-! ## Roles -/

theorem toRole_reads (f : RecCircuit.Formula) : (RecCircuit.toRole f).reads = f.reads := by
  cases f with
  | forward => rfl
  | expr p =>
    simp [RecCircuit.toRole, RecPiop.Role.reads, RecPiop.Poly2.reads, RecCircuit.toPoly2, RecCircuit.Formula.reads,
      RecCircuit.Poly.reads, List.map_map, Function.comp_def, List.flatMap_map]
  | port ls =>
    show (RecCircuit.portWeights ls).map (·.cell) = ls
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [_, _, _] => rfl
    | [_, _, _, _] => rfl
    | a :: b :: d :: e :: f :: rest =>
      show ((a :: b :: d :: e :: f :: rest).map fun c ↦ (⟨c, [1]⟩ : RecPiop.Limb F192)).map (·.cell) = _
      simp [Function.comp_def]

theorem toRole_isPort (f : RecCircuit.Formula) : (RecCircuit.toRole f).isPort = f.isPort := by
  cases f <;> rfl

theorem toRole_isExpr {f : RecCircuit.Formula} (h : ∃ p, f = .expr p) : (RecCircuit.toRole f).isExpr = true := by
  obtain ⟨p, rfl⟩ := h
  rfl

theorem toRole_forward_of_not (f : RecCircuit.Formula) (h : f = .forward) : (RecCircuit.toRole f).reads = [] := by
  subst h
  rfl

/-! ## The formula at a position -/

variable {c : RecCircuit.Circuit}

theorem regionOf_some {y r : ℕ} (h : c.regionOf y = some r) :
    ∃ b ∈ c.blocks.toList, b.region = r ∧ b.row ≤ y ∧ y < b.row + 2 ^ b.logRows := by
  unfold RecCircuit.Circuit.regionOf at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [← Array.find?_toList] at hb
  have hp := List.find?_some hb
  simp only [decide_eq_true_eq] at hp
  exact ⟨b, List.mem_of_find?_eq_some hb, rfl, hp⟩

/-- A position's formula is a role of a region (or a forward). -/
theorem formulaAt_cases (i : ℕ) : c.formulaAt i = .forward ∨
    ∃ b ∈ c.blocks.toList, b.row ≤ i / c.width ∧ i / c.width < b.row + 2 ^ b.logRows ∧
      c.formulaAt i = (blockRoles c b).getD (i % c.width) .forward := by
  unfold RecCircuit.Circuit.formulaAt
  cases hr : c.regionOf (i / c.width) with
  | none => exact Or.inl rfl
  | some r =>
    obtain ⟨b, hb, rfl, h1, h2⟩ := regionOf_some hr
    refine Or.inr ⟨b, hb, h1, h2, ?_⟩
    unfold blockRoles
    rw [RecCircuit.arr_toList_getD]

theorem readsB_spec (h : readsB c = true) {r : RecCircuit.Region} (hr : r ∈ c.regions.toList)
    {f : RecCircuit.Formula} (hf : f ∈ r.roles.toList) {x : ℕ} (hx : x ∈ f.reads) : x < c.width := by
  have h1 := arr_all_mem (arr_all_mem h hr) hf
  simpa using (List.all_eq_true.mp h1) x hx

theorem formulaAt_reads_lt (h : readsB c = true) (i : ℕ) {x : ℕ} (hx : x ∈ (c.formulaAt i).reads) : x < c.width := by
  rcases formulaAt_cases (c := c) i with hf | ⟨b, -, -, -, hf⟩
  · rw [hf] at hx; simp [RecCircuit.Formula.reads] at hx
  · rw [hf] at hx
    unfold blockRoles at hx
    rw [RecCircuit.arr_toList_getD] at hx
    rcases arr_getD_mem_or (c.regions.getD b.region default).roles (i % c.width) .forward with hm | hm
    · rcases arr_getD_mem_or c.regions b.region default with hr | hr
      · exact readsB_spec h hr hm hx
      · rw [hr, show (default : RecCircuit.Region).roles = #[] from rfl] at hm
        simp at hm
    · rw [hm] at hx; simp [RecCircuit.Formula.reads] at hx

/-! ## The holes' bitmap -/

theorem getD_set_true (a : Array Bool) (p s : ℕ) (hs : s < a.size) :
    (a.set! p true).getD s false = true ↔ p = s ∨ a.getD s false = true := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
  by_cases h : p = s
  · subst h
    simp [hs]
  · simp [h]

theorem holeFold (s : ℕ) : ∀ (L : List RecCircuit.Port) (a : Array Bool),
    (L.foldl (fun a p ↦ a.set! p.position true) a).size = a.size ∧
      (s < a.size → ((L.foldl (fun a p ↦ a.set! p.position true) a).getD s false = true ↔
        a.getD s false = true ∨ ∃ p ∈ L, p.position = s))
  | [], a => by simp
  | p :: L, a => by
    obtain ⟨h1, h2⟩ := holeFold s L (a.set! p.position true)
    have hsz : (a.set! p.position true).size = a.size := by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    rw [List.foldl_cons]
    refine ⟨h1.trans hsz, fun hs ↦ ?_⟩
    rw [h2 (by rw [hsz]; exact hs), getD_set_true _ _ _ hs]
    constructor
    · rintro ((rfl | h) | ⟨q, hq, rfl⟩)
      · exact Or.inr ⟨p, List.mem_cons_self .., rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
    · rintro (h | ⟨q, hq, rfl⟩)
      · exact Or.inl (Or.inr h)
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨q, hq, rfl⟩

/-- **The bitmap marks the ports' positions.** -/
theorem holeMap_spec {s : ℕ} (hs : s < c.n) :
    (holeMap c).getD s false = true ↔ ∃ p ∈ c.ports.toList, p.position = s := by
  unfold holeMap
  rw [← Array.foldl_toList, (holeFold s c.ports.toList _).2 (by simpa using hs)]
  simp [Array.getD_eq_getD_getElem?, hs]

/-! ## `σ`'s marks -/

/-- `sigmaMarks`' step. -/
def markStep (c : RecCircuit.Circuit) (i : ℕ) (acc : Option (Array Bool)) : Option (Array Bool) :=
  acc.bind fun a ↦
    if c.sigmaAt i < c.n + c.ports.size ∧ a.getD (c.sigmaAt i) true = false then some (a.set! (c.sigmaAt i) true)
    else none

/-- What the marks say after `k` positions. -/
def MarksInv (c : RecCircuit.Circuit) (k : ℕ) (a : Array Bool) : Prop :=
  a.size = c.n + c.ports.size ∧ (∀ s < c.n + c.ports.size, a.getD s false = true ↔ ∃ i < k, c.sigmaAt i = s) ∧
    (∀ i < k, c.sigmaAt i < c.n + c.ports.size) ∧ ∀ i < k, ∀ i' < k, c.sigmaAt i = c.sigmaAt i' → i = i'

theorem marks_inv : ∀ (k : ℕ) (a : Array Bool),
    Nat.fold k (fun i _ acc ↦ markStep c i acc) (some (Array.replicate (c.n + c.ports.size) false)) = some a →
      MarksInv c k a
  | 0, a, h => by
    simp only [Nat.fold_zero, Option.some.injEq] at h
    subst h
    refine ⟨by simp, fun s hs ↦ ?_, fun i hi ↦ absurd hi (Nat.not_lt_zero _),
      fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    simp [Array.getD_eq_getD_getElem?, hs]
  | k + 1, a', h => by
    rw [Nat.fold_succ] at h
    cases hk : Nat.fold k (fun i _ acc ↦ markStep c i acc) (some (Array.replicate (c.n + c.ports.size) false)) with
    | none => rw [hk] at h; simp [markStep] at h
    | some a =>
      rw [hk] at h
      unfold markStep at h
      simp only [Option.bind_some] at h
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hsz, hmark, hlt, hinj⟩ := marks_inv k a hk
      have hfresh : a.getD (c.sigmaAt k) false = false := by
        have := hc.2
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; exact hc.1)] at this ⊢
        simpa using this
      refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz], fun s hs ↦ ?_, fun i hi ↦ ?_,
        fun i hi i' hi' he ↦ ?_⟩
      · rw [getD_set_true _ _ _ (by rw [hsz]; exact hs), hmark s hs]
        constructor
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨k, by omega, rfl⟩
          · exact ⟨i, by omega, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact Or.inr ⟨i, hi, rfl⟩
          · exact Or.inl rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hlt i hi
        · exact hc.1
      · have hfr : ∀ j < k, c.sigmaAt j ≠ c.sigmaAt k := fun j hj he' ↦ by
          have := (hmark _ hc.1).mpr ⟨j, hj, he'⟩
          rw [hfresh] at this
          exact absurd this (by simp)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
        · exact hinj i hi i' hi' he
        · exact absurd he (hfr i hi)
        · exact absurd he.symm (hfr i' hi')
        · rfl

theorem sigmaMarks_eq (c : RecCircuit.Circuit) :
    sigmaMarks c = Nat.fold c.n (fun i _ acc ↦ markStep c i acc) (some (Array.replicate (c.n + c.ports.size) false)) :=
  rfl

/-! ## `κ` -/

theorem foldl_kappa (i : ℕ) : ∀ (L : List (ℕ × RecCircuit.K)) (acc : RecCircuit.K),
    L.foldl (fun acc e ↦ if e.1 = i then e.2 else acc) acc = acc ∨
      ∃ e ∈ L, e.1 = i ∧ L.foldl (fun acc e ↦ if e.1 = i then e.2 else acc) acc = e.2
  | [], acc => Or.inl rfl
  | e :: L, acc => by
    rw [List.foldl_cons]
    rcases foldl_kappa i L (if e.1 = i then e.2 else acc) with h | ⟨e', he', h1, h2⟩
    · rw [h]
      split_ifs with he
      · exact Or.inr ⟨e, List.mem_cons_self .., he, rfl⟩
      · exact Or.inl rfl
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩

theorem kappaAt_ne_zero {i : ℕ} (h : c.kappaAt i ≠ 0) : ∃ e ∈ c.kappa.toList, e.1 = i ∧ e.2 = c.kappaAt i := by
  unfold RecCircuit.Circuit.kappaAt at h ⊢
  rw [← Array.foldl_toList] at h ⊢
  rcases foldl_kappa i c.kappa.toList 0 with h0 | ⟨e, he, h1, h2⟩
  · exact absurd h0 h
  · exact ⟨e, he, h1, h2.symm⟩

/-! ## The PIOP form -/

theorem toPiop_nP : c.toPiop.nP = c.ports.size := by
  show (c.ports.toList.map (·.position)).length = _
  simp

theorem toPiop_port {j : ℕ} (hj : j < c.ports.size) : c.toPiop.port j = (c.ports.getD j default).position := by
  simp only [RecPiop.Circuit.port, RecCircuit.Circuit.toPiop, List.getD_eq_getElem?_getD,
    Array.getD_eq_getD_getElem?, List.getElem?_map, Array.getElem?_toList]
  rw [Array.getElem?_eq_getElem hj]
  rfl

theorem mem_toPiop_ports {i : ℕ} : i ∈ c.toPiop.ports ↔ ∃ p ∈ c.ports.toList, p.position = i := by
  show i ∈ c.ports.toList.map (·.position) ↔ _
  exact List.mem_map

theorem isHole_iff {i : ℕ} : c.toPiop.IsHole i ↔ (c.formulaAt i).isPort = true := by
  unfold RecPiop.Circuit.IsHole
  rw [RecCircuit.toPiop_role, toRole_isPort]

theorem mem_ports_iff {p : RecCircuit.Port} (hp : p ∈ c.ports.toList) :
    ∃ j < c.ports.size, c.ports.getD j default = p := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  refine ⟨j, by simpa using hj, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj)]
  simp

/-- **`validB` decides the PIOP form's validity.** -/
theorem validB_sound (h : validB c = true) : c.toPiop.Valid := by
  unfold validB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlt, hwid⟩, hreads⟩, hblocks⟩, hports⟩, hnohole⟩, hkappa⟩, hsigma⟩ := h
  unfold blocksB at hblocks
  simp only [Bool.and_eq_true] at hblocks
  obtain ⟨hb1, hb2⟩ := hblocks
  unfold portsB at hports
  simp only [Bool.and_eq_true] at hports
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hports
  have hp2' : ∀ j < c.ports.size, (c.ports.getD j default).position < c.n ∧
      (c.formulaAt (c.ports.getD j default).position).isPort = true ∧
      c.sigmaAt (c.ports.getD j default).position = c.n + j := by
    intro j hj
    have := RecCircuit.allBelow_spec hp2 j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hNW : c.n = 2 ^ (c.logN - c.logWidth) * c.width := by
    unfold RecCircuit.Circuit.n RecCircuit.Circuit.width
    rw [← pow_add, Nat.sub_add_cancel hlt.le]
  -- the ports are exactly the holes
  have hph : ∀ i, i ∈ c.toPiop.ports ↔ i < c.toPiop.N ∧ c.toPiop.IsHole i := by
    intro i
    rw [mem_toPiop_ports, isHole_iff]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨j, hj, rfl⟩ := mem_ports_iff hp
      exact ⟨(hp2' j hj).1, (hp2' j hj).2.1⟩
    · rintro ⟨hi, hport⟩
      rcases formulaAt_cases (c := c) i with hf | ⟨b, hb, h1, h2, hf⟩
      · rw [hf] at hport; simp [RecCircuit.Formula.isPort] at hport
      · rw [hf] at hport
        have hk : i % c.width < (blockRoles c b).length := by
          by_contra hk
          rw [List.getD_eq_default _ _ (by omega)] at hport
          simp [RecCircuit.Formula.isPort] at hport
        have h3 := RecCircuit.allBelow_spec (arr_all_mem hp3 hb) (i % c.width) hk
        rw [hport] at h3
        simp only [Bool.not_true, Bool.false_or] at h3
        have h4 := RecCircuit.allBelow_spec h3 (i / c.width - b.row) (by omega)
        obtain ⟨p, hp, hpos⟩ := arr_any_mem h4
        refine ⟨p, hp, ?_⟩
        simp only [beq_iff_eq] at hpos
        rw [hpos, Nat.add_sub_cancel' h1]
        exact Nat.div_add_mod i c.width
  have hhole : ∀ i < c.n, (holeMap c).getD i false = true ↔ i ∈ c.toPiop.ports := fun i hi ↦ by
    rw [holeMap_spec hi, mem_toPiop_ports]
  -- `σ`
  unfold sigmaOkB at hsigma
  cases hm : sigmaMarks c with
  | none => rw [hm] at hsigma; simp at hsigma
  | some marks =>
  rw [hm] at hsigma
  simp only at hsigma
  obtain ⟨-, hmark, -, hinj⟩ := marks_inv c.n marks (by rw [← sigmaMarks_eq]; exact hm)
  have hs : ∀ i < c.n, (holeMap c).getD i false = true ∨
      (c.sigmaAt i < c.n ∧ (holeMap c).getD (c.sigmaAt i) false = false ∧ marks.getD i false = true) := by
    intro i hi
    have := RecCircuit.allBelow_spec hsigma i hi
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    rcases this with h | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩
  have hnothole : ∀ i < c.n, ¬ c.toPiop.IsHole i → (holeMap c).getD i false = false := by
    intro i hi hh
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    exact hh ((hph i).mp ((hhole i hi).mp hc)).2
  exact {
    logW_lt := hlt
    width := fun r hr ↦ by
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      have := arr_all_mem hwid hr0
      simp only [beq_iff_eq] at this
      show (r0.roles.toList.map RecCircuit.toRole).length = c.width
      simpa using this
    reads_lt := fun r hr f hf x hx ↦ by
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hf
      rw [toRole_reads] at hx
      exact readsB_spec hreads hr0 hf0 hx
    aligned := fun b hb ↦ by
      obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      have := arr_all_mem hb1 hb0
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      exact Nat.dvd_of_mod_eq_zero this.1.1
    in_range := fun b hb ↦ by
      obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      have := arr_all_mem hb1 hb0
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      exact this.1.2
    region_lt := fun b hb ↦ by
      obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      have := arr_all_mem hb1 hb0
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      show b0.region < (c.regions.toList.map _).length
      simpa using this.2
    disjoint := by
      show (c.blocks.toList.map RecCircuit.toBlock).Pairwise _
      refine List.pairwise_iff_getElem.mpr fun i j hi hj hij ↦ ?_
      simp only [List.length_map, Array.length_toList] at hi hj
      have := RecCircuit.allBelow_spec (RecCircuit.allBelow_spec hb2 i hi) j hj
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt, decide_eq_true_eq] at this
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hj] at this
      simp only [List.getElem_map, Array.getElem_toList, RecCircuit.toBlock]
      rcases this with (h | h) | h
      · omega
      · exact Or.inl h
      · exact Or.inr h
    ports_nodup := by
      show (c.ports.toList.map (·.position)).Nodup
      refine List.pairwise_iff_getElem.mpr fun i j hi hj hij ↦ ?_
      simp only [List.length_map, Array.length_toList] at hi hj
      have := RecCircuit.allBelow_spec (RecCircuit.allBelow_spec hp1 i hi) j hj
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hj] at this
      simp only [List.getElem_map, Array.getElem_toList]
      rcases this with h | h
      · omega
      · exact h
    ports_holes := hph
    sigma_port := fun j hj ↦ by
      rw [toPiop_nP] at hj
      rw [toPiop_port hj]
      exact (hp2' j hj).2.2
    sigma_inside := fun i hi hh ↦ by
      have hi' : i < c.n := hi
      rcases hs i hi' with h | ⟨h1, h2, -⟩
      · rw [hnothole i hi' hh] at h; exact absurd h (by simp)
      · refine ⟨h1, fun hh' ↦ ?_⟩
        have := (hhole _ h1).mpr ((hph _).mpr ⟨h1, hh'⟩)
        rw [h2] at this
        exact absurd this (by simp)
    sigma_inj := fun i hi i' hi' he ↦ hinj i hi i' hi' he
    sigma_onto := fun j hj hh ↦ by
      have hj' : j < c.n := hj
      rcases hs j hj' with h | ⟨-, -, h3⟩
      · rw [hnothole j hj' hh] at h; exact absurd h (by simp)
      · exact (hmark j (by omega)).mp h3
    no_hole_read := fun i hi x hx hh ↦ by
      rw [RecCircuit.toPiop_role, toRole_reads] at hx
      have hxw := formulaAt_reads_lt hreads i hx
      have hW : c.toPiop.W = c.width := rfl
      have hbase : c.toPiop.base i = i / c.width * c.width := by unfold RecPiop.Circuit.base; rw [hW]
      have hwpos : 0 < c.width := Nat.two_pow_pos _
      have hlt' : c.toPiop.base i + x < c.toPiop.N := by
        rw [hbase]
        have hi' : i < c.n := hi
        have : i / c.width < 2 ^ (c.logN - c.logWidth) := by
          rw [Nat.div_lt_iff_lt_mul hwpos]; rw [← hNW]; exact hi'
        show i / c.width * c.width + x < c.n
        rw [hNW]
        nlinarith
      obtain ⟨p, hp, hpos⟩ := mem_toPiop_ports.mp ((hph _).mpr ⟨hlt', hh⟩)
      have h1 := RecCircuit.allBelow_spec (arr_all_mem hnohole hp) (i % c.width) (Nat.mod_lt _ hwpos)
      rw [hpos, hbase] at h1
      have hdiv : (i / c.width * c.width + x) / c.width = i / c.width := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hwpos, Nat.div_eq_of_lt hxw, zero_add]
      have hmod : (i / c.width * c.width + x) % c.width = x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hxw]
      rw [hdiv, hmod, Nat.mul_comm, Nat.div_add_mod' i c.width] at h1
      rw [show (c.formulaAt i).reads.contains x = true from List.contains_iff_mem.mpr hx] at h1
      exact absurd h1 (by simp)
    kappa_expr := fun i hi hk ↦ by
      have hk' : c.kappaAt i ≠ 0 := fun h0 ↦ hk (by
        show F192.ofF64 (c.kappaAt i) = 0
        rw [h0, F192.ofF64_zero])
      obtain ⟨e, he, h1, h2⟩ := kappaAt_ne_zero hk'
      have := arr_all_mem hkappa he
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at this
      rw [RecCircuit.toPiop_role]
      rcases this with (h | h) | h
      · exact absurd (h2 ▸ h) hk'
      · rw [h1] at h; exact absurd (show i < c.n from hi) (by omega)
      · rw [h1] at h
        refine toRole_isExpr ?_
        cases hf : c.formulaAt i with
        | expr p => exact ⟨p, rfl⟩
        | forward => rw [hf] at h; simp at h
        | port ls => rw [hf] at h; simp at h }

end RecCompose
