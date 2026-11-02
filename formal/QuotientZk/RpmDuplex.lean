-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s two-oracle model (`common/Common/Indiff2/`,
-- `common/Common/Transfer2.lean`); `transfer2_game` is the chain of `Common.transfer2`'s proof for
-- any game whose direct calls follow the duplex discipline, and `simTape2` reads
-- `Common.simulator2`'s fresh draws from a tape, as `RpmTape.lean` does for `Common.simulator`.
import QuotientZk.RpmTape
import Common.Transfer2

/-!
# The two-oracle model for any single-stage game, and its simulator with a tape

leanVM's Fiat–Shamir duplex calls the permutation directly. `common`'s two-oracle model
(`Common.Indiff2`) has a hash `H` and a random function `F` for the direct calls; in the
random-permutation model `H` is the sponge over `π` and `F = π` (`Common.realGame2`).

* `transfer2_game`: `Common.transfer2`'s chain (indifferentiability of the game with its direct
  calls read as permutation queries; the simulator drawing from `F`; the shadow world, where a
  direct call is `F`'s answer, the edge recorded in the simulator's state; the worlds disagree only
  on a capacity collision) holds for **any** game whose direct calls follow the duplex discipline
  (`Common.DuplexOK`), whoever makes them and in whatever order: in particular for a zero-knowledge
  game, the prover's direct calls coming before the distinguisher's queries. The real world and
  the shadow world are within `indiffBound2` (`Q² / 2^508` for Keccak-256).
* `simTape2`: the two-oracle simulator `Common.simulator2` with its coins (the completion of a
  digest at the end of a sponge path, the answer of a fresh inverse query) read from a tape drawn
  first (`simulator2_tape`); it asks `H` or `F` at most once per permutation query.
-/

open OracleComp OracleSpec Common
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

section Setting

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C] [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-! ## The two-oracle transfer for any game -/

/-- **The shadow world** of a two-oracle game: `H` and `F` lazily sampled random oracles, a direct
call `F`'s answer with its edge recorded in the simulator's state, `π` and `π⁻¹` the simulator
`Common.simulator2` from that state (`Common.shadowImpl`). -/
noncomputable def shadowGame {α : Type} (G : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) :
    ProbComp α :=
  (simulateQ (foldRO (shadowImpl P)) G).run' (SimState.init iv, ∅)

/-- **The two-oracle transfer for any game.** For a game whose direct calls follow the duplex
discipline for a block predicate `NF` that no padding ends with, of total cost at most `q`, every
event has probabilities in the random-permutation model (`realGame2`) and in the shadow world
within `indiffBound2 |S| |C| q`. -/
theorem transfer2_game (NF : (Dg × E) → Prop) [DecidablePred NF]
    (hNF : ∀ m β B, P.pad m = β ++ [B] → ¬ NF B) {α : Type}
    (G : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) (hG : DuplexOK iv NF G []) (q : ℕ)
    (hq : QueryCostAtMost G (queryCost2 (Dg := Dg) P) q) (p : α → Prop) :
    Pr{let a ← realGame2 P iv G}[p a] ≤ Pr{let a ← shadowGame P iv G}[p a] +
        indiffBound2 (Fintype.card (SpState Dg E C)) (Fintype.card C) q ∧
      Pr{let a ← shadowGame P iv G}[p a] ≤ Pr{let a ← realGame2 P iv G}[p a] +
        indiffBound2 (Fintype.card (SpState Dg E C)) (Fintype.card C) q := by
  obtain ⟨h1, h1'⟩ := indifferentiability P iv (simulateQ (toOne (E := E) (C := C)) G) q
    (isWeightBound_toOne P G q hq) p
  have h2 := (ideal1_evalDistEq_ideal1F P iv G).prEvent_eq p
  obtain ⟨h3, h3'⟩ := ideal1F_le_shadow P iv NF G p
  have h4 := prEvent_disagree_le P iv NF hNF G hG q hq
  rw [h2] at h3 h3'
  exact ⟨add_chain_le h1 h3 h4, add_chain_le' h1' h3' h4⟩

/-! ## The two-oracle simulator reading a tape -/

variable [Inhabited Dg] [Inhabited E] [Inhabited C]

/-- The answer at a fresh rooted node `x` with path `β`, read from the tape value `u`: when `β`
pads a message `m`, `H m` completed by `u`'s rest of the rate and capacity; otherwise `F x`. -/
def rootedTape2 (β : List (Dg × E)) (x u : SpState Dg E C) :
    OracleComp (hfSpec Msg Dg (SpState Dg E C)) (SpState Dg E C) :=
  match P.unpad β with
  | some m => (fun d ↦ ((d, u.1.2), u.2)) <$>
      (liftM ((hfSpec Msg Dg (SpState Dg E C)).query (.inl m)) : OracleComp _ Dg)
  | none => liftM ((hfSpec Msg Dg (SpState Dg E C)).query (.inr x))

/-- **The two-oracle simulator with a tape**: `Common.simulator2`, each draw of coins the tape's
next value. -/
def simTape2 : QueryImpl (permutationOracleSpec (SpState Dg E C))
    (StateT (SimState Dg E C × List (SpState Dg E C)) (OracleComp (hfSpec Msg Dg (SpState Dg E C))))
  | .forward x => StateT.mk fun s ↦
      match forwardLookup s.1.edges x with
      | some y => pure (y, s)
      | none =>
        match chainOf s.1.chains x with
        | some (r, β) => do
          let y ← rootedTape2 P (β ++ [blockTo r x]) x s.2.headI
          let t := if (P.unpad (β ++ [blockTo r x])).isSome then s.2.tail else s.2
          pure (y, (⟨(x, y) :: s.1.edges, (y, β ++ [blockTo r x]) :: s.1.chains⟩, t))
        | none => do
          let y ← liftM ((hfSpec Msg Dg (SpState Dg E C)).query (.inr x))
          pure (y, (⟨(x, y) :: s.1.edges, s.1.chains⟩, s.2))
  | .inverse y => StateT.mk fun s ↦
      match inverseLookup s.1.edges y with
      | some x => pure (x, s)
      | none => pure (s.2.headI, (⟨(s.2.headI, y) :: s.1.edges, s.1.chains⟩, s.2.tail))

/-- A query of a random oracle alone is one random-oracle step. -/
theorem ro_query_run' {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] (t : ι) (c : hs.QueryCache) :
    (simulateQ randomOracle (liftM (hs.query t) : OracleComp hs (hs.Range t))).run c =
      Common.roStep (hs := hs) t c := by
  rw [simulateQ_spec_query, randomOracle.run_eq]
  rfl

/-! ### One step, with and without the tape -/

section Steps

variable (σ : SimState Dg E C) (c : (hfSpec Msg Dg (SpState Dg E C)).QueryCache)

theorem sim2_fwd_some {x y : SpState Dg E C} (hx : forwardLookup σ.edges x = some y) :
    ((foldRO (simulator2 P)) (.forward x)).run (σ, c) = pure (y, (σ, c)) := by
  rw [Common.foldRO_run, simulator2_fwd_run P x (σ, c)]
  simp [fwdStep2, hx]

theorem sim2_fwd_free {x : SpState Dg E C} (hx : forwardLookup σ.edges x = none)
    (hch : chainOf σ.chains x = none) :
    ((foldRO (simulator2 P)) (.forward x)).run (σ, c) =
      (fun w ↦ (w.1, (⟨(x, w.1) :: σ.edges, σ.chains⟩, w.2))) <$>
        Common.roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x) c := by
  rw [Common.foldRO_run, simulator2_fwd_run P x (σ, c)]
  simp [fwdStep2, fStep, hx, hch, replayStep]

theorem sim2_fwd_nf {x r : SpState Dg E C} {β : List (Dg × E)}
    (hx : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hp : P.unpad (β ++ [blockTo r x]) = none) :
    ((foldRO (simulator2 P)) (.forward x)).run (σ, c) =
      (fun w ↦ (w.1, (⟨(x, w.1) :: σ.edges, (w.1, β ++ [blockTo r x]) :: σ.chains⟩, w.2))) <$>
        Common.roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x) c := by
  rw [Common.foldRO_run, simulator2_fwd_run P x (σ, c)]
  simp [fwdStep2, fStep, hx, hch, hp, replayStep]

theorem sim2_fwd_final {x r : SpState Dg E C} {β : List (Dg × E)} {msg : Msg}
    (hx : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hp : P.unpad (β ++ [blockTo r x]) = some msg) :
    ((foldRO (simulator2 P)) (.forward x)).run (σ, c) =
      (Common.roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl msg) c >>= fun w ↦
        ($ᵗ (E × C)) >>= fun ec ↦
          pure (((w.1, ec.1), ec.2), (⟨(x, ((w.1, ec.1), ec.2)) :: σ.edges,
            (((w.1, ec.1), ec.2), β ++ [blockTo r x]) :: σ.chains⟩, w.2))) := by
  rw [Common.foldRO_run, simulator2_fwd_run P x (σ, c)]
  simp [fwdStep2, hx, hch, hp, replayStep]

theorem sim2_inv_some {x y : SpState Dg E C} (hy : inverseLookup σ.edges y = some x) :
    ((foldRO (simulator2 P)) (.inverse y)).run (σ, c) = pure (x, (σ, c)) := by
  rw [Common.foldRO_run, simulator2_inv_run P y (σ, c)]
  simp [invStep2, hy]

theorem sim2_inv_free {y : SpState Dg E C} (hy : inverseLookup σ.edges y = none) :
    ((foldRO (simulator2 P)) (.inverse y)).run (σ, c) =
      (fun x ↦ (x, (⟨(x, y) :: σ.edges, σ.chains⟩, c))) <$> ($ᵗ (SpState Dg E C)) := by
  rw [Common.foldRO_run, simulator2_inv_run P y (σ, c)]
  simp [invStep2, hy, replayStep]

theorem tape2_fwd_some {x y : SpState Dg E C} (hx : forwardLookup σ.edges x = some y)
    (t : List (SpState Dg E C)) :
    ((foldR (simTape2 P)) (.forward x)).run ((σ, t), c) = pure (y, ((σ, t), c)) := by
  simp [foldR_run, simTape2, hx]

theorem tape2_fwd_free {x : SpState Dg E C} (hx : forwardLookup σ.edges x = none)
    (hch : chainOf σ.chains x = none) (t : List (SpState Dg E C)) :
    ((foldR (simTape2 P)) (.forward x)).run ((σ, t), c) =
      (fun w ↦ (w.1, ((⟨(x, w.1) :: σ.edges, σ.chains⟩, t), w.2))) <$>
        Common.roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x) c := by
  simp only [foldR_run, simTape2, StateT.run_mk, hx, hch, simulateQ_bind, StateT.run_bind,
    ro_query_run', simulateQ_pure, StateT.run_pure]
  simp [map_eq_bind_pure_comp]

theorem tape2_fwd_nf {x r : SpState Dg E C} {β : List (Dg × E)}
    (hx : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hp : P.unpad (β ++ [blockTo r x]) = none) (t : List (SpState Dg E C)) :
    ((foldR (simTape2 P)) (.forward x)).run ((σ, t), c) =
      (fun w ↦ (w.1, ((⟨(x, w.1) :: σ.edges, (w.1, β ++ [blockTo r x]) :: σ.chains⟩, t), w.2))) <$>
        Common.roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x) c := by
  simp only [foldR_run, simTape2, StateT.run_mk, hx, hch, simulateQ_bind, StateT.run_bind,
    rootedTape2, hp, ro_query_run', simulateQ_pure, StateT.run_pure]
  simp [map_eq_bind_pure_comp]

theorem tape2_fwd_final {x r : SpState Dg E C} {β : List (Dg × E)} {msg : Msg}
    (hx : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (r, β))
    (hp : P.unpad (β ++ [blockTo r x]) = some msg) (t : List (SpState Dg E C)) :
    ((foldR (simTape2 P)) (.forward x)).run ((σ, t), c) =
      (Common.roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl msg) c >>= fun w ↦
        pure (((w.1, t.headI.1.2), t.headI.2), ((⟨(x, ((w.1, t.headI.1.2), t.headI.2)) :: σ.edges,
          (((w.1, t.headI.1.2), t.headI.2), β ++ [blockTo r x]) :: σ.chains⟩, t.tail), w.2))) := by
  simp only [foldR_run, simTape2, StateT.run_mk, hx, hch, simulateQ_bind, StateT.run_bind,
    rootedTape2, hp, simulateQ_map, StateT.run_map, ro_query_run', simulateQ_pure, StateT.run_pure]
  simp

theorem tape2_inv_some {x y : SpState Dg E C} (hy : inverseLookup σ.edges y = some x)
    (t : List (SpState Dg E C)) :
    ((foldR (simTape2 P)) (.inverse y)).run ((σ, t), c) = pure (x, ((σ, t), c)) := by
  simp [foldR_run, simTape2, hy]

theorem tape2_inv_free {y : SpState Dg E C} (hy : inverseLookup σ.edges y = none)
    (t : List (SpState Dg E C)) :
    ((foldR (simTape2 P)) (.inverse y)).run ((σ, t), c) =
      pure (t.headI, ((⟨(t.headI, y) :: σ.edges, σ.chains⟩, t.tail), c)) := by
  simp [foldR_run, simTape2, hy]

end Steps

/-! ### The tape lemma -/

/-- **One step** of the two-oracle simulator and of its tape version (`step_tape`'s analogue). -/
theorem step_tape2 {γ : Type} (σ : SimState Dg E C) (c : (hfSpec Msg Dg (SpState Dg E C)).QueryCache)
    (qq : PermutationQuery (SpState Dg E C)) (m : ℕ)
    (F₁ : SpState Dg E C × (SimState Dg E C × (hfSpec Msg Dg (SpState Dg E C)).QueryCache) →
      ProbComp γ)
    (F₂ : SpState Dg E C × ((SimState Dg E C × List (SpState Dg E C)) ×
      (hfSpec Msg Dg (SpState Dg E C)).QueryCache) → ProbComp γ)
    (h0 : ∀ y σ' c', F₁ (y, (σ', c')) =ᵈ
      (uniformList (SpState Dg E C) (m + 1) >>= fun t ↦ F₂ (y, ((σ', t), c'))))
    (h1 : ∀ y σ' c', F₁ (y, (σ', c')) =ᵈ
      (uniformList (SpState Dg E C) m >>= fun t ↦ F₂ (y, ((σ', t), c')))) :
    (((foldRO (simulator2 P)) qq).run (σ, c) >>= F₁) =ᵈ
      (uniformList (SpState Dg E C) (m + 1) >>= fun t ↦
        ((foldR (simTape2 P)) qq).run ((σ, t), c) >>= F₂) := by
  cases qq with
  | forward x =>
    rcases hx : forwardLookup σ.edges x with _ | y
    · rcases hch : chainOf σ.chains x with _ | ⟨r, β⟩
      · rw [sim2_fwd_free P σ c hx hch, bind_map_left]
        simp only [tape2_fwd_free P σ c hx hch, bind_map_left]
        refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _).symm
        exact EvalDistEq.bind_congr_of_support _ fun w _ ↦ h0 _ _ _
      · rcases hp : P.unpad (β ++ [blockTo r x]) with _ | msg
        · rw [sim2_fwd_nf P σ c hx hch hp, bind_map_left]
          simp only [tape2_fwd_nf P σ c hx hch hp, bind_map_left]
          refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _).symm
          exact EvalDistEq.bind_congr_of_support _ fun w _ ↦ h0 _ _ _
        · rw [sim2_fwd_final P σ c hx hch hp]
          simp only [tape2_fwd_final P σ c hx hch hp, bind_assoc, pure_bind]
          set K : (hfSpec Msg Dg (SpState Dg E C)).Range (.inl msg) ×
              (hfSpec Msg Dg (SpState Dg E C)).QueryCache → SpState Dg E C → ProbComp γ :=
            fun dc u ↦ F₁ (((dc.1, u.1.2), u.2), (⟨(x, ((dc.1, u.1.2), u.2)) :: σ.edges,
              (((dc.1, u.1.2), u.2), β ++ [blockTo r x]) :: σ.chains⟩, dc.2)) with hK
          set L : (hfSpec Msg Dg (SpState Dg E C)).Range (.inl msg) ×
              (hfSpec Msg Dg (SpState Dg E C)).QueryCache → SpState Dg E C →
              List (SpState Dg E C) → ProbComp γ := fun dc u l ↦
            F₂ (((dc.1, u.1.2), u.2), ((⟨(x, ((dc.1, u.1.2), u.2)) :: σ.edges,
              (((dc.1, u.1.2), u.2), β ++ [blockTo r x]) :: σ.chains⟩, l), dc.2)) with hL
          refine EvalDistEq.trans ?_ (tape_cons _ m
            (fun u ↦ Common.roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl msg) c >>=
              fun dc ↦ uniformList (SpState Dg E C) m >>= fun l ↦ L dc u l)
            (fun u l ↦ Common.roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl msg) c >>=
              fun dc ↦ L dc u l)
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
    · rw [sim2_fwd_some P σ c hx, pure_bind]
      simp only [tape2_fwd_some P σ c hx, pure_bind]
      exact h0 _ _ _
  | inverse y =>
    rcases hy : inverseLookup σ.edges y with _ | x
    · rw [sim2_inv_free P σ c hy, bind_map_left]
      simp only [tape2_inv_free P σ c hy, pure_bind]
      exact tape_cons _ m _
        (fun u l ↦ F₂ (u, ((⟨(u, y) :: σ.edges, σ.chains⟩, l), c))) fun u ↦ h1 _ _ _
    · rw [sim2_inv_some P σ c hy, pure_bind]
      simp only [tape2_inv_some P σ c hy, pure_bind]
      exact h0 _ _ _

/-- The two-oracle simulator with its coins drawn first, folded. -/
theorem foldRO_simulator2_tape {α : Type}
    (X : OracleComp (permutationOracleSpec (SpState Dg E C)) α) :
    ∀ (q : ℕ), IsTotalQueryBound X q → ∀ (m : ℕ), q ≤ m → ∀ σ c,
      (simulateQ (foldRO (simulator2 P)) X).run' (σ, c) =ᵈ
        (uniformList (SpState Dg E C) m >>= fun t ↦
          (simulateQ (foldR (simTape2 P)) X).run' ((σ, t), c)) := by
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
    exact step_tape2 P σ c qq m'
      (fun z ↦ Prod.fst <$> (simulateQ (foldRO (simulator2 P)) (k z.1)).run z.2)
      (fun z ↦ Prod.fst <$> (simulateQ (foldR (simTape2 P)) (k z.1)).run z.2)
      (fun y σ' c' ↦ ih y (q - 1) (hk y) (m' + 1) (by omega) σ' c')
      (fun y σ' c' ↦ ih y (q - 1) (hk y) m' (by omega) σ' c')

/-- **The two-oracle simulator with its coins drawn first**: for a distinguisher `X` with at most
`q` permutation queries, from any simulator state `σ` and any cache `c` of `H` and `F`. -/
theorem simulator2_tape {α : Type} (X : OracleComp (permutationOracleSpec (SpState Dg E C)) α)
    (q : ℕ) (hX : IsTotalQueryBound X q) (σ : SimState Dg E C)
    (c : (hfSpec Msg Dg (SpState Dg E C)).QueryCache) :
    (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl
      ((simulateQ (simulator2 P) X).run' σ)).run' c =ᵈ
      (uniformList (SpState Dg E C) q >>= fun t ↦
        (simulateQ randomOracle ((simulateQ (simTape2 P) X).run' (σ, t))).run' c) := by
  rw [run'_simulateQ_foldRO]
  simp only [run'_simulateQ_foldR]
  exact foldRO_simulator2_tape P X q hX q le_rfl σ c

/-- The two-oracle simulator with a tape asks `H` or `F` at most once per permutation query. -/
theorem isTotalQueryBound_simTape2_step (qq : PermutationQuery (SpState Dg E C))
    (s : SimState Dg E C × List (SpState Dg E C)) :
    IsTotalQueryBound ((simTape2 P qq).run s) 1 := by
  cases qq with
  | forward x =>
    simp only [simTape2, StateT.run_mk]
    rcases forwardLookup s.1.edges x with _ | y
    · rcases chainOf s.1.chains x with _ | ⟨r, β⟩
      · exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ ↦ trivial⟩
      · simp only [rootedTape2]
        rcases P.unpad (β ++ [blockTo r x]) with _ | msg
        · exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ ↦ trivial⟩
        · simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
          exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ ↦ trivial⟩
    · trivial
  | inverse y =>
    simp only [simTape2, StateT.run_mk]
    rcases inverseLookup s.1.edges y with _ | x <;> trivial

theorem isTotalQueryBound_simTape2 {α : Type}
    (X : OracleComp (permutationOracleSpec (SpState Dg E C)) α) (q : ℕ)
    (hX : IsTotalQueryBound X q) (s : SimState Dg E C × List (SpState Dg E C)) :
    IsTotalQueryBound ((simulateQ (simTape2 P) X).run' s) q := by
  rw [StateT.run'_eq]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (IsTotalQueryBound.simulateQ_run_of_step hX (isTotalQueryBound_simTape2_step P) s)

end Setting

end QuotientZk
