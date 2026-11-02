-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s simulator of the sponge's indifferentiability
-- (`Common.simulator`, after Bertoni, Daemen, Peeters and Van Assche), whose fresh draws are read
-- here from a tape drawn in advance; `foldR` follows `common`'s `Common.foldRO`
-- (`common/Common/Fold.lean`).
import QuotientZk.Rom.Main
import Common.Indiff.Main
import Common.Fold

/-!
# The indifferentiability simulator with its coins drawn first

`common`'s simulator `S` (`Common.simulator`) answers a permutation query `π x`, `π⁻¹ y` with
oracle access to the random oracle `H`: a recorded edge from its records; a fresh forward query at
a rooted node whose path pads a message `m` with `H m` completed by uniform bits; any other fresh
query with a uniform state. Its coins are the only coins of a distinguisher that queries `π` and
`π⁻¹` alone, through `S`.

Here the uniform states are drawn **in advance**, as a tape of `m` uniform states, and `S` reads
the next one at each fresh query (`simTape`; at a rooted node padding `m`, the tape value's rest of
the rate and capacity complete `H m`). For a distinguisher with at most `q ≤ m` queries the two
are the same in distribution, from every simulator state and every cache of `H`
(`simulator_tape`): the tape is drawn independently of everything else, and each of its values
is read once. With the tape fixed, the simulated distinguisher has no coins: it is a computation
of the random oracle alone, as the random-oracle-model results need (`zk_rom`'s distinguisher), and
it asks `H` at most once per permutation query (`isTotalQueryBound_simTape`).
-/

open OracleComp OracleSpec Common
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

/-! ## Folding a random oracle into a coin-free implementation -/

section Fold

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {ι' : Type} [DecidableEq ι']
  {hs : OracleSpec.{0, 0} ι'} [∀ t : hs.Domain, SampleableType (hs.Range t)] {σ α : Type}

/-- Fold the random oracle `hs` into the state of a coin-free implementation. -/
noncomputable def foldR (impl : QueryImpl spec (StateT σ (OracleComp hs))) :
    QueryImpl spec (StateT (σ × hs.QueryCache) ProbComp) :=
  (randomOracle.mapStateTBase impl).flattenStateT

theorem foldR_run (impl : QueryImpl spec (StateT σ (OracleComp hs))) (t : spec.Domain) (s : σ)
    (c : hs.QueryCache) :
    ((foldR impl) t).run (s, c) =
      (fun y ↦ (y.1.1, (y.1.2, y.2))) <$> (simulateQ randomOracle ((impl t).run s)).run c :=
  rfl

theorem run_simulateQ_foldR (impl : QueryImpl spec (StateT σ (OracleComp hs)))
    (oa : OracleComp spec α) (s : σ) (c : hs.QueryCache) :
    (simulateQ randomOracle ((simulateQ impl oa).run s)).run c =
      (fun z ↦ ((z.1, z.2.1), z.2.2)) <$> (simulateQ (foldR impl) oa).run (s, c) := by
  rw [foldR, OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run]
  simp

theorem run'_simulateQ_foldR (impl : QueryImpl spec (StateT σ (OracleComp hs)))
    (oa : OracleComp spec α) (s : σ) (c : hs.QueryCache) :
    (simulateQ randomOracle ((simulateQ impl oa).run' s)).run' c =
      (simulateQ (foldR impl) oa).run' (s, c) := by
  have h := congrArg (fun x ↦ (fun z ↦ z.1.1) <$> x) (run_simulateQ_foldR impl oa s c)
  simp only [Functor.map_map] at h
  simpa [StateT.run'_eq, simulateQ_map] using h

end Fold

/-! ## The simulator reading a tape -/

section Tape

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C] [SampleableType Dg] [SampleableType E] [SampleableType C]
  [Inhabited Dg] [Inhabited E] [Inhabited C]
  (P : Padding Msg (Dg × E)) [P.Lawful]

/-- The answer at a fresh rooted node with path `β`, its fresh part the tape value `u`: when `β`
pads a message `m`, the digest `H m` completed by `u`'s rest of the rate and capacity; otherwise
`u`. -/
def rootedTape (β : List (Dg × E)) (u : SpState Dg E C) :
    OracleComp (roSpec Msg Dg) (SpState Dg E C) :=
  match P.unpad β with
  | some m => (fun d ↦ ((d, u.1.2), u.2)) <$> (liftM ((roSpec Msg Dg).query m) :
      OracleComp (roSpec Msg Dg) Dg)
  | none => pure u

/-- **The simulator with a tape**: `Common.simulator`, each fresh draw the tape's next value. -/
def simTape : QueryImpl (permutationOracleSpec (SpState Dg E C))
    (StateT (SimState Dg E C × List (SpState Dg E C)) (OracleComp (roSpec Msg Dg)))
  | .forward x => StateT.mk fun s ↦
      match forwardLookup s.1.edges x with
      | some y => pure (y, s)
      | none =>
        match chainOf s.1.chains x with
        | some (r, β) => do
          let y ← rootedTape P (β ++ [blockTo r x]) s.2.headI
          pure (y, (⟨(x, y) :: s.1.edges, (y, β ++ [blockTo r x]) :: s.1.chains⟩, s.2.tail))
        | none => pure (s.2.headI, (⟨(x, s.2.headI) :: s.1.edges, s.1.chains⟩, s.2.tail))
  | .inverse y => StateT.mk fun s ↦
      match inverseLookup s.1.edges y with
      | some x => pure (x, s)
      | none => pure (s.2.headI, (⟨(s.2.headI, y) :: s.1.edges, s.1.chains⟩, s.2.tail))

/-! ## One step, with and without the tape -/

theorem evalDistEq_bind_const {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    (mx >>= fun _ ↦ my) =ᵈ my := by
  let : MeasurableSpace β := ⊤
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const mx my)

/-- A uniform state's rest of the rate and capacity is uniform. -/
theorem marginal_rest :
    ((fun u : SpState Dg E C ↦ (u.1.2, u.2)) <$> ($ᵗ (SpState Dg E C))) =ᵈ ($ᵗ (E × C)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (Dg × E) C,
    SampleableType.uniformSample_prod_eq_bind Dg E, SampleableType.uniformSample_prod_eq_bind E C]
  simp only [bind_assoc, pure_bind, map_bind, map_pure]
  exact evalDistEq_bind_const _ _

/-- A tape of `m + 1` values is its head and an independent tape of `m`. -/
theorem uniformList_succ_bind {β : Type} (T : Type) [SampleableType T] [Inhabited T] (m : ℕ)
    (G : T → List T → ProbComp β) :
    (uniformList T (m + 1) >>= fun t ↦ G t.headI t.tail) =
      (($ᵗ T) >>= fun u ↦ uniformList T m >>= fun l ↦ G u l) := by
  simp [uniformList, bind_assoc]

variable (σ : SimState Dg E C) (c : (roSpec Msg Dg).QueryCache)

theorem sim_fwd_some {x y : SpState Dg E C} (hx : forwardLookup σ.edges x = some y) :
    ((foldRO (simulator P)) (.forward x)).run (σ, c) = pure (y, (σ, c)) := by
  simp [foldRO_run, simulator, hx]

theorem tape_fwd_some {x y : SpState Dg E C} (hx : forwardLookup σ.edges x = some y)
    (t : List (SpState Dg E C)) :
    ((foldR (simTape P)) (.forward x)).run ((σ, t), c) = pure (y, ((σ, t), c)) := by
  simp [foldR_run, simTape, hx]

theorem sim_fwd_free {x : SpState Dg E C} (hx : forwardLookup σ.edges x = none)
    (hch : chainOf σ.chains x = none) :
    ((foldRO (simulator P)) (.forward x)).run (σ, c) =
      (fun y ↦ (y, (⟨(x, y) :: σ.edges, σ.chains⟩, c))) <$> ($ᵗ (SpState Dg E C)) := by
  simp [foldRO_run, simulator, hx, hch]
  rw [OracleSpec.simulateQ_romImpl_liftM_run, Functor.map_map]

theorem tape_fwd_free {x : SpState Dg E C} (hx : forwardLookup σ.edges x = none)
    (hch : chainOf σ.chains x = none) (t : List (SpState Dg E C)) :
    ((foldR (simTape P)) (.forward x)).run ((σ, t), c) =
      pure (t.headI, ((⟨(x, t.headI) :: σ.edges, σ.chains⟩, t.tail), c)) := by
  simp [foldR_run, simTape, hx, hch]

theorem sim_fwd_nf {x r : SpState Dg E C} {β : List (Dg × E)}
    (hx : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hp : P.unpad (β ++ [blockTo r x]) = none) :
    ((foldRO (simulator P)) (.forward x)).run (σ, c) =
      (fun y ↦ (y, (⟨(x, y) :: σ.edges, (y, β ++ [blockTo r x]) :: σ.chains⟩, c))) <$>
        ($ᵗ (SpState Dg E C)) := by
  simp [foldRO_run, simulator, hx, hch, rootedAnswer, hp]
  rw [OracleSpec.simulateQ_romImpl_liftM_run, Functor.map_map]

theorem tape_fwd_nf {x r : SpState Dg E C} {β : List (Dg × E)}
    (hx : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hp : P.unpad (β ++ [blockTo r x]) = none) (t : List (SpState Dg E C)) :
    ((foldR (simTape P)) (.forward x)).run ((σ, t), c) =
      pure (t.headI, ((⟨(x, t.headI) :: σ.edges, (t.headI, β ++ [blockTo r x]) :: σ.chains⟩,
        t.tail), c)) := by
  simp [foldR_run, simTape, hx, hch, rootedTape, hp]

theorem sim_fwd_final {x r : SpState Dg E C} {β : List (Dg × E)} {msg : Msg}
    (hx : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hp : P.unpad (β ++ [blockTo r x]) = some msg) :
    ((foldRO (simulator P)) (.forward x)).run (σ, c) =
      (Common.roStep (hs := roSpec Msg Dg) msg c >>= fun dc ↦ ($ᵗ (E × C)) >>= fun ec ↦
        pure (((dc.1, ec.1), ec.2), (⟨(x, ((dc.1, ec.1), ec.2)) :: σ.edges,
          (((dc.1, ec.1), ec.2), β ++ [blockTo r x]) :: σ.chains⟩, dc.2))) := by
  simp only [foldRO_run, simulator, StateT.run_mk, hx, hch]
  rw [simulateQ_bind, StateT.run_bind, rootedAnswer_run_some P hp]
  simp

/-- A query of the random oracle alone is one random-oracle step. -/
theorem ro_query_run (m : Msg) :
    (simulateQ randomOracle (liftM ((roSpec Msg Dg).query m) : OracleComp (roSpec Msg Dg) Dg)).run c =
      Common.roStep (hs := roSpec Msg Dg) m c := by
  rw [simulateQ_spec_query, randomOracle.run_eq]
  rfl

theorem tape_fwd_final {x r : SpState Dg E C} {β : List (Dg × E)} {msg : Msg}
    (hx : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hp : P.unpad (β ++ [blockTo r x]) = some msg) (t : List (SpState Dg E C)) :
    ((foldR (simTape P)) (.forward x)).run ((σ, t), c) =
      (Common.roStep (hs := roSpec Msg Dg) msg c >>= fun dc ↦
        pure (((dc.1, t.headI.1.2), t.headI.2), ((⟨(x, ((dc.1, t.headI.1.2), t.headI.2)) :: σ.edges,
          (((dc.1, t.headI.1.2), t.headI.2), β ++ [blockTo r x]) :: σ.chains⟩, t.tail), dc.2))) := by
  simp only [foldR_run, simTape, StateT.run_mk, hx, hch, simulateQ_bind, StateT.run_bind,
    rootedTape, hp, simulateQ_map, StateT.run_map, ro_query_run]
  simp

theorem sim_inv_some {x y : SpState Dg E C} (hy : inverseLookup σ.edges y = some x) :
    ((foldRO (simulator P)) (.inverse y)).run (σ, c) = pure (x, (σ, c)) := by
  simp [foldRO_run, simulator, hy]

theorem tape_inv_some {x y : SpState Dg E C} (hy : inverseLookup σ.edges y = some x)
    (t : List (SpState Dg E C)) :
    ((foldR (simTape P)) (.inverse y)).run ((σ, t), c) = pure (x, ((σ, t), c)) := by
  simp [foldR_run, simTape, hy]

theorem sim_inv_free {y : SpState Dg E C} (hy : inverseLookup σ.edges y = none) :
    ((foldRO (simulator P)) (.inverse y)).run (σ, c) =
      (fun x ↦ (x, (⟨(x, y) :: σ.edges, σ.chains⟩, c))) <$> ($ᵗ (SpState Dg E C)) := by
  simp [foldRO_run, simulator, hy]
  rw [OracleSpec.simulateQ_romImpl_liftM_run, Functor.map_map]

theorem tape_inv_free {y : SpState Dg E C} (hy : inverseLookup σ.edges y = none)
    (t : List (SpState Dg E C)) :
    ((foldR (simTape P)) (.inverse y)).run ((σ, t), c) =
      pure (t.headI, ((⟨(t.headI, y) :: σ.edges, σ.chains⟩, t.tail), c)) := by
  simp [foldR_run, simTape, hy]

/-- Drawing the head of a tape of `m + 1` first. -/
theorem tape_cons {β : Type} (T : Type) [SampleableType T] [Inhabited T] (m : ℕ)
    (G₁ : T → ProbComp β) (G₂ : T → List T → ProbComp β)
    (h : ∀ u, G₁ u =ᵈ (uniformList T m >>= fun l ↦ G₂ u l)) :
    (($ᵗ T) >>= G₁) =ᵈ (uniformList T (m + 1) >>= fun t ↦ G₂ t.headI t.tail) := by
  rw [uniformList_succ_bind]
  exact EvalDistEq.bind_congr_of_support _ fun u _ ↦ h u

/-- **One step.** The simulator's step from `(σ, c)` followed by `F₁`, and the tape's step from
a tape of `m + 1` uniform states followed by `F₂`, are the same in distribution, when after any
step `F₁` is `F₂` with a tape of `m + 1` or of `m` uniform states. -/
theorem step_tape {γ : Type} (qq : PermutationQuery (SpState Dg E C)) (m : ℕ)
    (F₁ : SpState Dg E C × (SimState Dg E C × (roSpec Msg Dg).QueryCache) → ProbComp γ)
    (F₂ : SpState Dg E C × ((SimState Dg E C × List (SpState Dg E C)) ×
      (roSpec Msg Dg).QueryCache) → ProbComp γ)
    (h0 : ∀ y σ' c', F₁ (y, (σ', c')) =ᵈ
      (uniformList (SpState Dg E C) (m + 1) >>= fun t ↦ F₂ (y, ((σ', t), c'))))
    (h1 : ∀ y σ' c', F₁ (y, (σ', c')) =ᵈ
      (uniformList (SpState Dg E C) m >>= fun t ↦ F₂ (y, ((σ', t), c')))) :
    (((foldRO (simulator P)) qq).run (σ, c) >>= F₁) =ᵈ
      (uniformList (SpState Dg E C) (m + 1) >>= fun t ↦
        ((foldR (simTape P)) qq).run ((σ, t), c) >>= F₂) := by
  cases qq with
  | forward x =>
    rcases hx : forwardLookup σ.edges x with _ | y
    · rcases hch : chainOf σ.chains x with _ | ⟨r, β⟩
      · rw [sim_fwd_free P σ c hx hch, bind_map_left]
        simp only [tape_fwd_free P σ c hx hch, pure_bind]
        exact tape_cons _ m _
          (fun u l ↦ F₂ (u, ((⟨(x, u) :: σ.edges, σ.chains⟩, l), c))) fun u ↦ h1 _ _ _
      · rcases hp : P.unpad (β ++ [blockTo r x]) with _ | msg
        · rw [sim_fwd_nf P σ c hx hch hp, bind_map_left]
          simp only [tape_fwd_nf P σ c hx hch hp, pure_bind]
          exact tape_cons _ m _
            (fun u l ↦ F₂ (u, ((⟨(x, u) :: σ.edges, (u, β ++ [blockTo r x]) :: σ.chains⟩, l), c)))
            fun u ↦ h1 _ _ _
        · rw [sim_fwd_final P σ c hx hch hp]
          simp only [tape_fwd_final P σ c hx hch hp, bind_assoc, pure_bind]
          set K : (roSpec Msg Dg).Range msg × (roSpec Msg Dg).QueryCache → SpState Dg E C →
              ProbComp γ := fun dc u ↦
            F₁ (((dc.1, u.1.2), u.2), (⟨(x, ((dc.1, u.1.2), u.2)) :: σ.edges,
              (((dc.1, u.1.2), u.2), β ++ [blockTo r x]) :: σ.chains⟩, dc.2)) with hK
          set L : (roSpec Msg Dg).Range msg × (roSpec Msg Dg).QueryCache → SpState Dg E C →
              List (SpState Dg E C) → ProbComp γ := fun dc u l ↦
            F₂ (((dc.1, u.1.2), u.2), ((⟨(x, ((dc.1, u.1.2), u.2)) :: σ.edges,
              (((dc.1, u.1.2), u.2), β ++ [blockTo r x]) :: σ.chains⟩, l), dc.2)) with hL
          refine EvalDistEq.trans ?_ (tape_cons _ m
            (fun u ↦ Common.roStep (hs := roSpec Msg Dg) msg c >>= fun dc ↦
              uniformList (SpState Dg E C) m >>= fun l ↦ L dc u l)
            (fun u l ↦ Common.roStep (hs := roSpec Msg Dg) msg c >>= fun dc ↦ L dc u l)
            fun u ↦ EvalDistEq.bind_bind_swap _ _ _)
          refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _)
          refine EvalDistEq.bind_congr_of_support _ fun dc _ ↦ ?_
          calc (($ᵗ (E × C)) >>= fun ec ↦ K dc ((dc.1, ec.1), ec.2))
              =ᵈ (((fun u : SpState Dg E C ↦ (u.1.2, u.2)) <$> ($ᵗ (SpState Dg E C))) >>=
                  fun ec ↦ K dc ((dc.1, ec.1), ec.2)) :=
                EvalDistEq.bind_left (marginal_rest).symm _
            _ = (($ᵗ (SpState Dg E C)) >>= fun u ↦ K dc u) := by
                rw [bind_map_left]
            _ =ᵈ _ := EvalDistEq.bind_congr_of_support _ fun u _ ↦ h1 _ _ _
    · rw [sim_fwd_some P σ c hx, pure_bind]
      simp only [tape_fwd_some P σ c hx, pure_bind]
      exact h0 _ _ _
  | inverse y =>
    rcases hy : inverseLookup σ.edges y with _ | x
    · rw [sim_inv_free P σ c hy, bind_map_left]
      simp only [tape_inv_free P σ c hy, pure_bind]
      exact tape_cons _ m _
        (fun u l ↦ F₂ (u, ((⟨(u, y) :: σ.edges, σ.chains⟩, l), c))) fun u ↦ h1 _ _ _
    · rw [sim_inv_some P σ c hy, pure_bind]
      simp only [tape_inv_some P σ c hy, pure_bind]
      exact h0 _ _ _

omit σ c in
/-- **The simulator with its coins drawn first**, folded: for a distinguisher with at most
`q ≤ m` permutation queries. -/
theorem foldRO_simulator_tape {α : Type} (X : OracleComp (permutationOracleSpec (SpState Dg E C)) α) :
    ∀ (q : ℕ), IsTotalQueryBound X q → ∀ (m : ℕ), q ≤ m → ∀ σ c,
      (simulateQ (foldRO (simulator P)) X).run' (σ, c) =ᵈ
        (uniformList (SpState Dg E C) m >>= fun t ↦
          (simulateQ (foldR (simTape P)) X).run' ((σ, t), c)) := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro q _ m _ σ c
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact (evalDistEq_bind_const _ _).symm
  | query_bind qq k ih =>
    intro q hq m hm σ c
    rw [isTotalQueryBound_query_bind_iff] at hq
    obtain ⟨hq0, hk⟩ := hq
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run'_eq, StateT.run_bind, map_bind]
    exact step_tape P σ c qq m'
      (fun z ↦ Prod.fst <$> (simulateQ (foldRO (simulator P)) (k z.1)).run z.2)
      (fun z ↦ Prod.fst <$> (simulateQ (foldR (simTape P)) (k z.1)).run z.2)
      (fun y σ' c' ↦ ih y (q - 1) (hk y) (m' + 1) (by omega) σ' c')
      (fun y σ' c' ↦ ih y (q - 1) (hk y) m' (by omega) σ' c')

omit σ c in
/-- **The simulator with its coins drawn first**: for a distinguisher `X` with at most `q`
permutation queries, from any simulator state `σ` and any cache `c` of the random oracle, `X`
against the simulator (with coins) and the random oracle is `X` against the simulator reading a
tape of `q` uniform states drawn first, and the random oracle. -/
theorem simulator_tape {α : Type} (X : OracleComp (permutationOracleSpec (SpState Dg E C)) α)
    (q : ℕ) (hX : IsTotalQueryBound X q) (σ : SimState Dg E C) (c : (roSpec Msg Dg).QueryCache) :
    (simulateQ (roSpec Msg Dg).romImpl ((simulateQ (simulator P) X).run' σ)).run' c =ᵈ
      (uniformList (SpState Dg E C) q >>= fun t ↦
        (simulateQ randomOracle ((simulateQ (simTape P) X).run' (σ, t))).run' c) := by
  rw [run'_simulateQ_foldRO]
  simp only [run'_simulateQ_foldR]
  exact foldRO_simulator_tape P X q hX q le_rfl σ c

omit σ c in
/-- The simulator with a tape asks the random oracle at most once per permutation query. -/
theorem isTotalQueryBound_simTape_step (qq : PermutationQuery (SpState Dg E C))
    (s : SimState Dg E C × List (SpState Dg E C)) :
    IsTotalQueryBound ((simTape P qq).run s) 1 := by
  cases qq with
  | forward x =>
    simp only [simTape, StateT.run_mk]
    rcases forwardLookup s.1.edges x with _ | y
    · rcases chainOf s.1.chains x with _ | ⟨r, β⟩
      · trivial
      · simp only [rootedTape]
        rcases P.unpad (β ++ [blockTo r x]) with _ | msg
        · trivial
        · simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
          exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ ↦ trivial⟩
    · trivial
  | inverse y =>
    simp only [simTape, StateT.run_mk]
    rcases inverseLookup s.1.edges y with _ | x <;> trivial

omit σ c in
theorem isTotalQueryBound_simTape {α : Type}
    (X : OracleComp (permutationOracleSpec (SpState Dg E C)) α) (q : ℕ)
    (hX : IsTotalQueryBound X q) (s : SimState Dg E C × List (SpState Dg E C)) :
    IsTotalQueryBound ((simulateQ (simTape P) X).run' s) q := by
  rw [StateT.run'_eq]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (IsTotalQueryBound.simulateQ_run_of_step hX (isTotalQueryBound_simTape_step P) s)

end Tape

end QuotientZk
