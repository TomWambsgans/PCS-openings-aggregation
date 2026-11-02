-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The model (`lazyRandomPermutation`, `lazyRandomPermutationOracles`, `runWithRandomPermutation`,
-- `uniformAvoiding`, `forwardLookup`, `inverseLookup`) is leanerVM's (branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`).
import ZK.Real

/-!
# The lazily sampled permutation is a uniform permutation drawn first

mumbai's random-permutation model answers `π` and `π⁻¹` lazily (`lazyRandomPermutation`): a fresh
forward query draws its answer uniformly outside the range so far, a fresh inverse query its answer
uniformly outside the domain so far. **`prEvent_runWithRandomPermutation`**: a game run so is, for
every event, the average over all permutations `π` of the state of the game run with `π` and `π⁻¹`
answered by `π` (`permImpl π`, the coins as the model draws them):

`Pr[p | runWithRandomPermutation X] = (1 / |Perm|) · Σ_π Pr[p | simulateQ (permImpl π) X]`.

The proof is one induction over the game, for every list of edges `E`, on any finite state type
(`card_mul_prEvent`): `|C(E)| · Pr[p | X run lazily from E] = Σ_{π ∈ C(E)} Pr[p | X run by π]`,
`C(E)` the permutations through every edge of `E` (`cons`). A fresh forward query at `x` splits
`C(E)` by `π x`, which avoids the range of `E` (`mapsTo_fwd`); the parts are the `C((x, y) :: E)`,
all of one size (`card_cons_fwd_eq`: composing with the transposition of `y` and `y'` maps one onto
the other), so each value `y` outside the range has the lazy draw's weight `1 / |outside|`
(`card_cons_fwd`). An inverse query is the same with `π⁻¹ y`, composing on the other side.

So two games that compute the same thing for every permutation but a set `Bad` of them are closer
than the fraction of `Bad` (**`close_of_perm`**): repeated queries, the order of queries and the
queries a game makes that the other does not cost nothing.

The lemmas are stated for any finite state type `S` (the Keccak state's `2^1600` values are never to
be enumerated by the elaborator), then read at the Keccak state.
-/

open OracleComp OracleSpec Common
open scoped ENNReal

namespace PcsQuotient.EndToEnd.Eager

open QuotientZk (Close)

set_option linter.unusedSectionVars false

section Generic

variable {S : Type} [DecidableEq S] [Fintype S] [SampleableType S]

/-- The model's oracles on the state type `S`. -/
abbrev Spec (S : Type) := unifSpec + permutationOracleSpec S

/-- The lazily sampled permutation of `S`, with coins. -/
noncomputable def lazyImpl : QueryImpl (Spec S) (StateT (PermutationEdges S) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr q => lazyRandomPermutation q

/-- **The permutations through the edges `E`.** -/
def cons (E : PermutationEdges S) : Finset (Equiv.Perm S) :=
  Finset.univ.filter fun π ↦ ∀ e ∈ E, π e.1 = e.2

theorem mem_cons {E : PermutationEdges S} {π : Equiv.Perm S} :
    π ∈ cons E ↔ ∀ e ∈ E, π e.1 = e.2 := by
  unfold cons
  rw [Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ π, h⟩⟩

theorem mem_cons_cons {E : PermutationEdges S} {π : Equiv.Perm S} {x y : S} :
    π ∈ cons ((x, y) :: E) ↔ π x = y ∧ π ∈ cons E := by
  rw [mem_cons, mem_cons]
  simp

theorem cons_nil : cons ([] : PermutationEdges S) = Finset.univ := by
  ext π
  rw [mem_cons]
  exact ⟨fun _ ↦ Finset.mem_univ π, fun _ e he ↦ absurd he List.not_mem_nil⟩

/-- **The model's oracles answered by the permutation `π`**: coins as the model draws them, `π x`
and `π⁻¹ y`. -/
def permImpl (π : Equiv.Perm S) : QueryImpl (Spec S) ProbComp
  | .inl n => $[0..n]
  | .inr (.forward x) => pure (π x)
  | .inr (.inverse y) => pure (π.symm y)

/-! ### The lookups -/

theorem forwardLookup_mem {E : PermutationEdges S} {x y : S} (h : forwardLookup E x = some y) :
    (x, y) ∈ E := by
  induction E with
  | nil => simp [forwardLookup] at h
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    simp only [forwardLookup] at h
    split_ifs at h with hax
    · cases h
      subst hax
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem forwardLookup_none {E : PermutationEdges S} {x : S} (h : forwardLookup E x = none) :
    ∀ e ∈ E, e.1 ≠ x := by
  induction E with
  | nil => simp
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    simp only [forwardLookup] at h
    split_ifs at h with hax
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hax
    · exact ih h e he

theorem inverseLookup_mem {E : PermutationEdges S} {x y : S} (h : inverseLookup E y = some x) :
    (x, y) ∈ E := by
  induction E with
  | nil => simp [inverseLookup] at h
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    simp only [inverseLookup] at h
    split_ifs at h with hby
    · cases h
      subst hby
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem inverseLookup_none {E : PermutationEdges S} {y : S} (h : inverseLookup E y = none) :
    ∀ e ∈ E, e.2 ≠ y := by
  induction E with
  | nil => simp
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    simp only [inverseLookup] at h
    split_ifs at h with hby
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hby
    · exact ih h e he

/-! ### Counting the permutations through the edges -/

/-- A permutation through `E` maps a point outside `E`'s domain outside its range. -/
theorem mapsTo_fwd {E : PermutationEdges S} {x : S} (hx : ∀ e ∈ E, e.1 ≠ x)
    {π : Equiv.Perm S} (hπ : π ∈ cons E) : π x ∉ E.map Prod.snd := by
  intro h
  obtain ⟨e, he, hex⟩ := List.mem_map.mp h
  rw [mem_cons] at hπ
  have : π e.1 = π x := (hπ e he).trans hex
  exact hx e he (π.injective this)

/-- A permutation through `E` maps back a point outside `E`'s range outside its domain. -/
theorem mapsTo_inv {E : PermutationEdges S} {y : S} (hy : ∀ e ∈ E, e.2 ≠ y)
    {π : Equiv.Perm S} (hπ : π ∈ cons E) : π.symm y ∉ E.map Prod.fst := by
  intro h
  obtain ⟨e, he, hey⟩ := List.mem_map.mp h
  rw [mem_cons] at hπ
  have h1 : π e.1 = y := by rw [hey, Equiv.apply_symm_apply]
  exact hy e he ((hπ e he).symm.trans h1)

/-- The forward parts are of one size: the transposition of `y` and `y'` after `π`. -/
theorem card_cons_fwd_eq (E : PermutationEdges S) (x : S) {y y' : S}
    (hy : y ∉ E.map Prod.snd) (hy' : y' ∉ E.map Prod.snd) :
    (cons ((x, y) :: E)).card = (cons ((x, y') :: E)).card := by
  have hE : ∀ (z : S), z ∉ E.map Prod.snd → ∀ e ∈ E, e.2 ≠ z := fun z hz e he h ↦
    hz (List.mem_map.mpr ⟨e, he, h⟩)
  refine Finset.card_bij' (fun π _ ↦ Equiv.swap y y' * π) (fun π _ ↦ Equiv.swap y y' * π)
    ?_ ?_ ?_ ?_
  · intro π hπ
    rw [mem_cons_cons] at hπ ⊢
    refine ⟨by rw [Equiv.Perm.mul_apply, hπ.1, Equiv.swap_apply_left], ?_⟩
    rw [mem_cons] at hπ ⊢
    intro e he
    rw [Equiv.Perm.mul_apply, hπ.2 e he]
    exact Equiv.swap_apply_of_ne_of_ne (hE y hy e he) (hE y' hy' e he)
  · intro π hπ
    rw [mem_cons_cons] at hπ ⊢
    refine ⟨by rw [Equiv.Perm.mul_apply, hπ.1, Equiv.swap_apply_right], ?_⟩
    rw [mem_cons] at hπ ⊢
    intro e he
    rw [Equiv.Perm.mul_apply, hπ.2 e he]
    exact Equiv.swap_apply_of_ne_of_ne (hE y hy e he) (hE y' hy' e he)
  · intro π _
    exact Equiv.swap_mul_self_mul _ _ _
  · intro π _
    exact Equiv.swap_mul_self_mul _ _ _

/-- The inverse parts are of one size: the transposition of `x` and `x'` before `π`. -/
theorem card_cons_inv_eq (E : PermutationEdges S) (y : S) {x x' : S}
    (hx : x ∉ E.map Prod.fst) (hx' : x' ∉ E.map Prod.fst) :
    (cons ((x, y) :: E)).card = (cons ((x', y) :: E)).card := by
  have hE : ∀ (z : S), z ∉ E.map Prod.fst → ∀ e ∈ E, e.1 ≠ z := fun z hz e he h ↦
    hz (List.mem_map.mpr ⟨e, he, h⟩)
  refine Finset.card_bij' (fun π _ ↦ π * Equiv.swap x x') (fun π _ ↦ π * Equiv.swap x x')
    ?_ ?_ ?_ ?_
  · intro π hπ
    rw [mem_cons_cons] at hπ ⊢
    refine ⟨by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hπ.1], ?_⟩
    rw [mem_cons] at hπ ⊢
    intro e he
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (hE x hx e he) (hE x' hx' e he), hπ.2 e he]
  · intro π hπ
    rw [mem_cons_cons] at hπ ⊢
    refine ⟨by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hπ.1], ?_⟩
    rw [mem_cons] at hπ ⊢
    intro e he
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (hE x hx e he) (hE x' hx' e he), hπ.2 e he]
  · intro π _
    exact Equiv.mul_swap_mul_self _ _ _
  · intro π _
    exact Equiv.mul_swap_mul_self _ _ _

/-- The points outside a list. -/
def outside (l : List S) : Finset S := Finset.univ.filter (· ∉ l)

theorem mem_outside {l : List S} {y : S} : y ∈ outside l ↔ y ∉ l := by
  unfold outside
  rw [Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ y, h⟩⟩

/-- A sum over the states, zero on `l`, is a sum over the points outside `l`. -/
theorem sum_outside (l : List S) (F : S → ℝ≥0∞) :
    ∑ b, (if b ∈ l then 0 else F b) = ∑ b ∈ outside l, F b := by
  unfold outside
  rw [Finset.sum_filter]
  simp only [ite_not]

/-- The part of `C(E)` with `π x = y`. -/
theorem filter_fwd (E : PermutationEdges S) (x y : S) :
    (cons E).filter (fun π ↦ π x = y) = cons ((x, y) :: E) := by
  ext π
  rw [Finset.mem_filter, mem_cons_cons]
  exact And.comm

/-- The part of `C(E)` with `π⁻¹ y = x`. -/
theorem filter_inv (E : PermutationEdges S) (x y : S) :
    (cons E).filter (fun π ↦ π.symm y = x) = cons ((x, y) :: E) := by
  ext π
  rw [Finset.mem_filter, mem_cons_cons, Equiv.symm_apply_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1.symm⟩

/-- **`|C(E)| = |outside range E| · |C((x, y) :: E)|`** for `x` outside `E`'s domain and `y`
outside its range. -/
theorem card_cons_fwd (E : PermutationEdges S) {x y : S} (hx : ∀ e ∈ E, e.1 ≠ x)
    (hy : y ∉ E.map Prod.snd) :
    (cons E).card = (outside (E.map Prod.snd)).card * (cons ((x, y) :: E)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun π ↦ π x) (t := outside (E.map Prod.snd))
    fun π hπ ↦ mem_outside.mpr (mapsTo_fwd hx hπ)]
  rw [Finset.sum_congr rfl fun y' hy' ↦ by
    rw [filter_fwd, card_cons_fwd_eq E x (mem_outside.mp hy') hy]]
  rw [Finset.sum_const, smul_eq_mul]

/-- **`|C(E)| = |outside domain E| · |C((x, y) :: E)|`** for `x` outside `E`'s domain and `y`
outside its range. -/
theorem card_cons_inv (E : PermutationEdges S) {x y : S} (hy : ∀ e ∈ E, e.2 ≠ y)
    (hx : x ∉ E.map Prod.fst) :
    (cons E).card = (outside (E.map Prod.fst)).card * (cons ((x, y) :: E)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun π ↦ π.symm y) (t := outside (E.map Prod.fst))
    fun π hπ ↦ mem_outside.mpr (mapsTo_inv hy hπ)]
  rw [Finset.sum_congr rfl fun x' hx' ↦ by
    rw [filter_inv, card_cons_inv_eq E y (mem_outside.mp hx') hx]]
  rw [Finset.sum_const, smul_eq_mul]

/-! ### The lazy draw -/

theorem card_outside (l : List S) : Fintype.card {y // y ∉ l} = (outside l).card := by
  rw [Fintype.card_subtype]
  rfl

/-- A uniform draw from any sampler of a finite type. -/
theorem prEvent_sample_singleton {T : Type} [Fintype T] (inst : SampleableType T) (a : T) :
    Pr{let x ← @uniformSample T inst}[x = a] = (Fintype.card T : ℝ≥0∞)⁻¹ :=
  SampleableType.prEvent_uniformSample_eq_singleton a

/-- **The lazy draw outside `l`**: `1 / |outside l|` at each point outside `l`, `0` on `l`. -/
theorem prEvent_uniformAvoiding (l : List S) (h : ∃ y, y ∉ l) (b : S) :
    Pr{let y ← uniformAvoiding l}[y = b] =
      if b ∈ l then 0 else ((outside l).card : ℝ≥0∞)⁻¹ := by
  unfold uniformAvoiding
  rw [dite_eq_left_of_eq_true (eq_true h)]
  rw [prEvent_map]
  split_ifs with hb
  · refine (OracleComp.prEvent_eq_zero_iff _ _).mpr fun z _ hz ↦ ?_
    exact z.2 (hz ▸ hb)
  · rw [prEvent_congr _ _ (fun z ↦ z = ⟨b, hb⟩) fun z ↦ by
      constructor
      · intro hz; exact Subtype.ext hz
      · intro hz; rw [hz]]
    rw [prEvent_sample_singleton, card_outside]

/-! ### The induction -/

theorem run'_query_bind {α : Type} (t : (Spec S).Domain)
    (k : (Spec S).Range t → OracleComp (Spec S) α) (E : PermutationEdges S) :
    (simulateQ lazyImpl (liftM ((Spec S).query t) >>= k)).run' E =
      (lazyImpl t).run E >>= fun z ↦ (simulateQ lazyImpl (k z.1)).run' z.2 := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run'_eq, StateT.run_bind, map_bind]

theorem sim_query_bind {α : Type} (π : Equiv.Perm S) (t : (Spec S).Domain)
    (k : (Spec S).Range t → OracleComp (Spec S) α) :
    simulateQ (permImpl π) (liftM ((Spec S).query t) >>= k) =
      permImpl π t >>= fun u ↦ simulateQ (permImpl π) (k u) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map]

theorem lazy_coin (n : ℕ) (E : PermutationEdges S) :
    (lazyImpl (S := S) (.inl n)).run E = (fun u ↦ (u, E)) <$> $[0..n] := by
  simp only [lazyImpl, StateT.run, liftM, monadLift, MonadLift.monadLift, StateT.lift,
    map_eq_bind_pure_comp]
  rfl

theorem lazy_fwd_some {E : PermutationEdges S} {x y : S} (h : forwardLookup E x = some y) :
    (lazyImpl (.inr (.forward x))).run E = pure (y, E) := by
  simp only [lazyImpl, lazyRandomPermutation, StateT.run_mk, h]

theorem lazy_fwd_none {E : PermutationEdges S} {x : S} (h : forwardLookup E x = none) :
    (lazyImpl (.inr (.forward x))).run E =
      (fun y ↦ (y, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.snd) := by
  simp only [lazyImpl, lazyRandomPermutation, StateT.run_mk, h]

theorem lazy_inv_some {E : PermutationEdges S} {x y : S} (h : inverseLookup E y = some x) :
    (lazyImpl (.inr (.inverse y))).run E = pure (x, E) := by
  simp only [lazyImpl, lazyRandomPermutation, StateT.run_mk, h]

theorem lazy_inv_none {E : PermutationEdges S} {y : S} (h : inverseLookup E y = none) :
    (lazyImpl (.inr (.inverse y))).run E =
      (fun x ↦ (x, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.fst) := by
  simp only [lazyImpl, lazyRandomPermutation, StateT.run_mk, h]

/-- **The lazy permutation, counted**: from the edges `E`, `|C(E)|` times the probability of an
event is the sum over the permutations `π` through `E` of its probability with `π`. -/
theorem card_mul_prEvent {α : Type} (p : α → Prop) (X : OracleComp (Spec S) α) :
    ∀ E : PermutationEdges S, ((cons E).card : ℝ≥0∞) *
        Pr{let a ← (simulateQ lazyImpl X).run' E}[p a] =
      ∑ π ∈ cons E, Pr{let a ← simulateQ (permImpl π) X}[p a] := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro E
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, Finset.sum_const,
      nsmul_eq_mul]
  | query_bind t k ih =>
    intro E
    rw [run'_query_bind]
    simp only [sim_query_bind]
    rcases t with n | (x | y)
    · -- a coin
      rw [lazy_coin, bind_map_left, prEvent_bind_eq_sum_fintype, Finset.mul_sum]
      simp only [show ∀ π, permImpl π (.inl n) = $[0..n] from fun _ ↦ rfl,
        prEvent_bind_eq_sum_fintype]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [mul_left_comm, ih u E, Finset.mul_sum]
      rfl
    · -- a forward query
      simp only [show ∀ π, permImpl π (.inr (.forward x)) = pure (π x) from fun _ ↦ rfl, pure_bind]
      rcases hl : forwardLookup E x with _ | y
      · have hx := forwardLookup_none hl
        rw [lazy_fwd_none hl, bind_map_left]
        by_cases hout : ∃ y, y ∉ E.map Prod.snd
        · rw [prEvent_bind_eq_sum_fintype, Finset.mul_sum]
          simp only [prEvent_uniformAvoiding _ hout, ite_mul, zero_mul, mul_ite, mul_zero]
          rw [sum_outside]
          rw [← Finset.sum_fiberwise_of_maps_to (g := fun π ↦ π x) (t := outside (E.map Prod.snd))
            fun π hπ ↦ mem_outside.mpr (mapsTo_fwd hx hπ)]
          refine Finset.sum_congr rfl fun b hb ↦ ?_
          have hb' := mem_outside.mp hb
          rw [filter_fwd]
          rw [Finset.sum_congr rfl fun π hπ ↦ by rw [(mem_cons_cons.mp hπ).1]]
          rw [← ih b ((x, b) :: E), ← mul_assoc]
          congr 1
          rw [card_cons_fwd E hx hb', Nat.cast_mul, mul_comm ((outside _).card : ℝ≥0∞),
            mul_assoc, ENNReal.mul_inv_cancel, mul_one]
          · exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨b, hb⟩)
          · exact ENNReal.natCast_ne_top _
        · have hE : cons E = ∅ := Finset.eq_empty_of_forall_notMem fun π hπ ↦
            hout ⟨π x, mapsTo_fwd hx hπ⟩
          rw [hE]
          simp
      · have hxy := forwardLookup_mem hl
        rw [lazy_fwd_some hl, pure_bind]
        rw [ih y E]
        refine Finset.sum_congr rfl fun π hπ ↦ ?_
        rw [(mem_cons.mp hπ) _ hxy]
    · -- an inverse query
      simp only [show ∀ π, permImpl π (.inr (.inverse y)) = pure (π.symm y) from fun _ ↦ rfl,
        pure_bind]
      rcases hl : inverseLookup E y with _ | x
      · have hy := inverseLookup_none hl
        rw [lazy_inv_none hl, bind_map_left]
        by_cases hout : ∃ x, x ∉ E.map Prod.fst
        · rw [prEvent_bind_eq_sum_fintype, Finset.mul_sum]
          simp only [prEvent_uniformAvoiding _ hout, ite_mul, zero_mul, mul_ite, mul_zero]
          rw [sum_outside]
          rw [← Finset.sum_fiberwise_of_maps_to (g := fun π ↦ π.symm y)
            (t := outside (E.map Prod.fst)) fun π hπ ↦ mem_outside.mpr (mapsTo_inv hy hπ)]
          refine Finset.sum_congr rfl fun b hb ↦ ?_
          have hb' := mem_outside.mp hb
          rw [filter_inv]
          rw [Finset.sum_congr rfl fun π hπ ↦ by
            rw [(Equiv.symm_apply_eq π).mpr (mem_cons_cons.mp hπ).1.symm]]
          rw [← ih b ((b, y) :: E), ← mul_assoc]
          congr 1
          rw [card_cons_inv E hy hb', Nat.cast_mul, mul_comm ((outside _).card : ℝ≥0∞),
            mul_assoc, ENNReal.mul_inv_cancel, mul_one]
          · exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨b, hb⟩)
          · exact ENNReal.natCast_ne_top _
        · have hE : cons E = ∅ := Finset.eq_empty_of_forall_notMem fun π hπ ↦
            hout ⟨π.symm y, mapsTo_inv hy hπ⟩
          rw [hE]
          simp
      · have hxy := inverseLookup_mem hl
        rw [lazy_inv_some hl, pure_bind]
        rw [ih x E]
        refine Finset.sum_congr rfl fun π hπ ↦ ?_
        rw [(Equiv.symm_apply_eq π).mpr ((mem_cons.mp hπ) _ hxy).symm]

/-- The number of permutations of `S`. -/
abbrev nPerm (S : Type) [DecidableEq S] [Fintype S] : ℕ := Fintype.card (Equiv.Perm S)

theorem nPerm_ne_zero : (nPerm S : ℝ≥0∞) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- **The lazily sampled permutation is a uniform permutation drawn first**, on any finite state
type. -/
theorem prEvent_lazy {α : Type} (p : α → Prop) (X : OracleComp (Spec S) α) :
    Pr{let a ← (simulateQ lazyImpl X).run' []}[p a] =
      (nPerm S : ℝ≥0∞)⁻¹ * ∑ π, Pr{let a ← simulateQ (permImpl π) X}[p a] := by
  have h := card_mul_prEvent p X []
  rw [cons_nil, Finset.card_univ] at h
  rw [← h, ← mul_assoc, ENNReal.inv_mul_cancel nPerm_ne_zero (ENNReal.natCast_ne_top _), one_mul]

/-- The fraction of the permutations in a set `Bad`. -/
noncomputable def frac (Bad : Equiv.Perm S → Prop) [DecidablePred Bad] : ℝ≥0∞ :=
  (nPerm S : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bad).card

theorem card_filter_eq_sum (Bad : Equiv.Perm S → Prop) [DecidablePred Bad] :
    ((Finset.univ.filter Bad).card : ℝ≥0∞) = ∑ π, if Bad π then (1 : ℝ≥0∞) else 0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Two games equal for every permutation but a set `Bad`** are closer than `Bad`'s fraction. -/
theorem close_of_perm_gen (X₁ X₂ : OracleComp (Spec S) Bool)
    (Bad : Equiv.Perm S → Prop) [DecidablePred Bad]
    (h : ∀ π, ¬ Bad π → Pr{let b ← simulateQ (permImpl π) X₁}[b = true] =
      Pr{let b ← simulateQ (permImpl π) X₂}[b = true]) :
    Close ((simulateQ lazyImpl X₁).run' []) ((simulateQ lazyImpl X₂).run' []) (frac Bad) := by
  have key : ∀ (A B : OracleComp (Spec S) Bool),
      (∀ π, ¬ Bad π → Pr{let b ← simulateQ (permImpl π) A}[b = true] =
        Pr{let b ← simulateQ (permImpl π) B}[b = true]) →
      Pr{let b ← (simulateQ lazyImpl A).run' []}[b = true] ≤
        Pr{let b ← (simulateQ lazyImpl B).run' []}[b = true] + frac Bad := by
    intro A B hAB
    rw [prEvent_lazy, prEvent_lazy, frac, ← mul_add]
    refine mul_le_mul' le_rfl ?_
    rw [card_filter_eq_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun π _ ↦ ?_
    by_cases hb : Bad π
    · simp only [hb, ↓reduceIte]
      exact (prEvent_le_one _).trans le_add_self
    · simp only [hb, ↓reduceIte, add_zero, hAB π hb, le_refl]
  exact ⟨key X₁ X₂ h, key X₂ X₁ fun π hπ ↦ (h π hπ).symm⟩

/-- **A deterministic event's fraction**: if a game's event holds with probability `1` exactly on
`Bad` (and `0` elsewhere), its probability is `Bad`'s fraction. -/
theorem prEvent_eq_frac_gen {α : Type} (X : OracleComp (Spec S) α) (p : α → Prop)
    (Bad : Equiv.Perm S → Prop) [DecidablePred Bad]
    (h : ∀ π, Pr{let a ← simulateQ (permImpl π) X}[p a] = if Bad π then 1 else 0) :
    Pr{let a ← (simulateQ lazyImpl X).run' []}[p a] = frac Bad := by
  rw [prEvent_lazy, frac, card_filter_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun π _ ↦ h π

end Generic

/-! ## At the Keccak state -/

/-- The Keccak state. -/
abbrev St := LeanVM.Semantics.KeccakState

theorem lazyImpl_eq : (lazyImpl : QueryImpl (Spec St) _) = lazyRandomPermutationOracles := by
  funext t
  rcases t with n | q <;> rfl

/-- **The lazily sampled permutation is a uniform permutation drawn first**: every event of a game
run in the random-permutation model has the average probability, over all permutations `π`, of the
game with `π` and `π⁻¹` answered by `π`. -/
theorem prEvent_runWithRandomPermutation {α : Type} (p : α → Prop)
    (X : OracleComp RandomPermutationOracles α) :
    Pr{let a ← runWithRandomPermutation X}[p a] =
      (nPerm St : ℝ≥0∞)⁻¹ * ∑ π, Pr{let a ← simulateQ (permImpl π) X}[p a] := by
  unfold runWithRandomPermutation
  rw [← lazyImpl_eq]
  exact prEvent_lazy p X

/-- **Two games of the model equal for every permutation but a set `Bad`** are closer than `Bad`'s
fraction. -/
theorem close_of_perm (X₁ X₂ : OracleComp RandomPermutationOracles Bool)
    (Bad : Equiv.Perm St → Prop) [DecidablePred Bad]
    (h : ∀ π, ¬ Bad π → Pr{let b ← simulateQ (permImpl π) X₁}[b = true] =
      Pr{let b ← simulateQ (permImpl π) X₂}[b = true]) :
    Close (runWithRandomPermutation X₁) (runWithRandomPermutation X₂) (frac Bad) := by
  unfold runWithRandomPermutation
  rw [← lazyImpl_eq]
  exact close_of_perm_gen X₁ X₂ Bad h

/-- **A deterministic event's fraction** in the model. -/
theorem prEvent_eq_frac {α : Type} (X : OracleComp RandomPermutationOracles α) (p : α → Prop)
    (Bad : Equiv.Perm St → Prop) [DecidablePred Bad]
    (h : ∀ π, Pr{let a ← simulateQ (permImpl π) X}[p a] = if Bad π then 1 else 0) :
    Pr{let a ← runWithRandomPermutation X}[p a] = frac Bad := by
  unfold runWithRandomPermutation
  rw [← lazyImpl_eq]
  exact prEvent_eq_frac_gen X p Bad h

end PcsQuotient.EndToEnd.Eager
