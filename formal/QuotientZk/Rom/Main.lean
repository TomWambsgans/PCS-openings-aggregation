-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s state projection (`Common.run'_simulateQ_evalDistEq_of_inv`).
import QuotientZk.Rom.MerkleBound

/-!
# Zero knowledge of the non-interactive proof in the random-oracle model

**`zk_rom`**: for every distinguisher `D` making at most `QD` oracle queries after it sees the
proof, the real game (`realGame`: honest proof, then `D` with the random oracle) and the simulated
game (`simGame`: `sim`'s proof, then `D` with the random oracle from `sim`'s cache) output `true`
with probabilities within

  `ε = εFS + εhv + N (|c₀| + QP + QD) δ + N² δ₂`

of each other, where

* `εFS` bounds the probability that one of the honest prover's Fiat–Shamir queries finds its
  input already answered (`hFS`, a property of the honest prover's oracle use);
* `εhv` bounds the probability of the challenges at which the honest-verifier simulator `simV`
  is not exact (`hzk`, `hgood`: the interactive layer's zero knowledge, F1 and F3);
* `δ`, `δ₂`: each unopened row, and the equality of two unopened rows, given the view
  (`hent`, `hent₂`: F3's `unopened_row_le`);
* `N` positions of the secret tables, `QP` operations of the prover, `QD` queries of `D`, `c₀`
  the oracle's entries before the proof.

The chain of games: real → fresh challenges (until the flag, `εFS`) → challenges drawn first (the
same) → unopened leaves apart (the same) → simulator's implementation with the honest view (until
`MBad`, the entropy bound) → simulated view (`εhv`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

/-! ## Closeness of games that output a bit -/

/-- Two games that output a bit are `ε`-close. -/
def Close (A B : ProbComp Bool) (ε : ℝ≥0∞) : Prop :=
  Pr{let b ← A}[b = true] ≤ Pr{let b ← B}[b = true] + ε ∧
    Pr{let b ← B}[b = true] ≤ Pr{let b ← A}[b = true] + ε

namespace Close

theorem of_evalDistEq {A B : ProbComp Bool} (h : A =ᵈ B) : Close A B 0 := by
  constructor <;> simp [h.prEvent_eq]

theorem symm {A B : ProbComp Bool} {ε : ℝ≥0∞} (h : Close A B ε) : Close B A ε := ⟨h.2, h.1⟩

theorem mono {A B : ProbComp Bool} {ε ε' : ℝ≥0∞} (h : Close A B ε) (hε : ε ≤ ε') :
    Close A B ε' :=
  ⟨h.1.trans (add_le_add le_rfl hε), h.2.trans (add_le_add le_rfl hε)⟩

theorem trans {A B C : ProbComp Bool} {ε₁ ε₂ : ℝ≥0∞} (h₁ : Close A B ε₁) (h₂ : Close B C ε₂) :
    Close A C (ε₁ + ε₂) :=
  ⟨h₁.1.trans ((add_le_add h₂.1 le_rfl).trans (by rw [add_assoc, add_comm ε₂])),
    h₂.2.trans ((add_le_add h₁.2 le_rfl).trans (by rw [add_assoc]))⟩

/-- Averaging: games close at each value of a first draw are close after it. -/
theorem bind {α : Type} (μ : ProbComp α) (f g : α → ProbComp Bool) (ε : α → ℝ≥0∞)
    (h : ∀ x, Close (f x) (g x) (ε x)) :
    Close (μ >>= f) (μ >>= g) (∑' x, Pr{let y ← μ}[y = x] * ε x) := by
  constructor
  · rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← mul_add]
    exact mul_le_mul_right (h x).1 _
  · rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← mul_add]
    exact mul_le_mul_right (h x).2 _

end Close

/-! ## The distinguisher inside the game -/

section Distinguisher

variable {S I O M K X Pf : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
  [DecidableEq K] [DecidableEq X] [Inhabited I]

/-- The distinguisher's queries as `pub` operations. -/
def liftPub {α : Type} (D : OracleComp (I →ₒ O) α) : OracleComp (OpSpec I O M K X) α :=
  simulateQ (pubImpl (M := M) (K := K) (X := X)) D

/-- The proof, then the distinguisher, as one computation of operations. -/
def game (skel : OracleComp (OpSpec I O M K X) Pf) (D : Pf → OracleComp (I →ₒ O) Bool) :
    OracleComp (OpSpec I O M K X) Bool :=
  skel >>= fun π => liftPub (D π)

theorem isTotalQueryBound_liftPub {α : Type} (D : OracleComp (I →ₒ O) α) (n : ℕ)
    (h : IsTotalQueryBound D n) : IsTotalQueryBound (liftPub (M := M) (K := K) (X := X) D) n := by
  induction D using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    simp only [liftPub, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, pubImpl]
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨h.1, fun u => ih u (n - 1) (h.2 u)⟩

/-- An implementation that answers `pub` as the random oracle. -/
def PubIsRo (impl : QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp)) : Prop :=
  ∀ t, impl (.pub t) = roStep t

theorem roStep_proj_ro (t : I) (st : St I O K X) :
    Prod.map id St.cache <$> (roStep t).run st = (randomOracle t).run st.cache := by
  rw [randomOracle.run_eq]
  simp only [StateT.run, roStep]
  cases st.cache t <;> simp

/-- **The distinguisher sees the random oracle**: run after any state, its `pub` operations are
the random oracle on the state's cache. -/
theorem liftPub_evalDistEq {α : Type} (impl : QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp))
    (himpl : PubIsRo impl) (D : OracleComp (I →ₒ O) α) (st : St I O K X) :
    (simulateQ impl (liftPub D)).run' st =ᵈ (simulateQ randomOracle D).run' st.cache := by
  unfold liftPub
  rw [← QueryImpl.simulateQ_compose]
  refine Common.run'_simulateQ_evalDistEq_of_inv _ _ (fun _ => True) St.cache
    (fun _ _ _ _ _ => trivial) (fun t st _ => ?_) D st trivial
  have : (impl ∘ₛ pubImpl (M := M) (K := K) (X := X)) t = roStep t := by
    simp only [QueryImpl.apply_compose, pubImpl, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact himpl t
  rw [this, roStep_proj_ro]

/-- The flag after the distinguisher is the flag before it. -/
theorem liftPub_fs {α : Type} (impl : QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp))
    (himpl : PubIsRo impl) (D : OracleComp (I →ₒ O) α) (st : St I O K X) :
    ∀ z ∈ support ((simulateQ impl (liftPub D)).run st), z.2.fs = st.fs := by
  unfold liftPub
  rw [← QueryImpl.simulateQ_compose]
  have := Common.inv_of_mem_support_run (impl ∘ₛ pubImpl (M := M) (K := K) (X := X))
    (fun s => s.fs = st.fs) (fun t s hs z hz => by
      have h : (impl ∘ₛ pubImpl (M := M) (K := K) (X := X)) t = roStep t := by
        simp only [QueryImpl.apply_compose, pubImpl, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map]
        exact himpl t
      rw [h] at hz
      exact (roStep_fs t s z hz).1.trans hs) D (s := st) rfl
  exact this

/-- The game run with an implementation is the proof's run, then `D` with the random oracle. -/
theorem game_evalDistEq (impl : QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp))
    (himpl : PubIsRo impl) (skel : OracleComp (OpSpec I O M K X) Pf)
    (D : Pf → OracleComp (I →ₒ O) Bool) (st : St I O K X) :
    (simulateQ impl (game skel D)).run' st =ᵈ
      (do let z ← (simulateQ impl skel).run st
          (simulateQ randomOracle (D z.1)).run' z.2.cache) := by
  simp only [game, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  exact EvalDistEq.bind_congr_of_support _ fun z _ => by
    simpa [StateT.run'_eq] using liftPub_evalDistEq impl himpl (D z.1) z.2

end Distinguisher

/-! ## The theorem -/

section Main

variable {S I O M K X Pf : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
  [DecidableEq K] [DecidableEq X] [Inhabited I] [SampleableType S]
variable (P : Proto S I O M K X)

theorem implReal_pub (s : S) : PubIsRo (implReal P s) := fun _ => rfl
theorem implView_pub (σ : List O) (v : View M I K X) : PubIsRo (implView P σ v) := fun _ => rfl

theorem prEvent_run'_eq {α σ' : Type} (A : StateT σ' ProbComp α) (st : σ') (p : α → Prop) :
    Pr{let b ← A.run' st}[p b] = Pr{let z ← A.run st}[p z.1] := by
  rw [StateT.run'_eq, prEvent_map]

/-- **Zero knowledge in the random-oracle model.** -/
theorem zk_rom [Fintype (K × X)] (skel : OracleComp (OpSpec I O M K X) Pf) (c₀ : List (I × O))
    (simV : List O → ProbComp (View M I K X)) (good : List O → Prop)
    (εFS εhv δ δ₂ : ℝ≥0∞) (QP QD : ℕ)
    (hQP : IsTotalQueryBound skel QP)
    (hFS : Pr{let x ← (do
        let s ← $ᵗ S
        let z ← (simulateQ (implReal P s) skel).run (St.init c₀)
        return z.2.fs)}[x = true] ≤ εFS)
    (hzk : ∀ σ, good σ → (fun s => P.view s σ) <$> ($ᵗ S) =ᵈ simV σ)
    (hgood : Pr{let σ ← uniformList O P.n}[¬ good σ] ≤ εhv)
    (hent : ∀ σ k x, P.opened σ k x = false → ∀ v y,
      Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = y] ≤
        δ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hent₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') → ∀ v,
        Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = P.rows s σ k' x'] ≤
          δ₂ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (D : Pf → OracleComp (I →ₒ O) Bool) (hD : ∀ π, IsTotalQueryBound (D π) QD) :
    Close (realGame P skel c₀ D) (simGame P simV skel c₀ D)
      (εFS + εhv + ((Fintype.card (K × X) * (c₀.length + (QP + QD)) : ℕ) * δ +
        (Fintype.card (K × X) ^ 2 : ℕ) * δ₂)) := by
  classical
  set G := game skel D
  set st₀ : St I O K X := St.init c₀
  set εM := ((Fintype.card (K × X) * (c₀.length + (QP + QD)) : ℕ) * δ +
    (Fintype.card (K × X) ^ 2 : ℕ) * δ₂)
  have hG : IsTotalQueryBound G (QP + QD) :=
    isTotalQueryBound_bind hQP fun π => isTotalQueryBound_liftPub (D π) QD (hD π)
  -- the real game and the simulated game are the combined runs
  have hreal : realGame P skel c₀ D =ᵈ
      (do let s ← $ᵗ S; (simulateQ (implReal P s) G).run' st₀) := by
    unfold realGame prove
    refine EvalDistEq.bind_congr_of_support _ fun s _ => ?_
    refine EvalDistEq.symm ((game_evalDistEq _ (implReal_pub P s) skel D st₀).trans ?_)
    simp only [map_bind, bind_map_left]
    exact EvalDistEq.rfl
  have hsim : simGame P simV skel c₀ D =ᵈ
      (do let σ ← uniformList O P.n; let v ← simV σ;
          (simulateQ (implView P σ v) G).run' st₀) := by
    unfold simGame sim
    simp only [bind_assoc, pure_bind]
    refine EvalDistEq.bind_congr_of_support _ fun σ _ => ?_
    refine EvalDistEq.bind_congr_of_support _ fun v _ => ?_
    exact (game_evalDistEq _ (implView_pub P σ v) skel D st₀).symm
  -- step 1: fresh challenges, until the flag
  have h1 : Close (do let s ← $ᵗ S; (simulateQ (implReal P s) G).run' st₀)
      (do let s ← $ᵗ S; (simulateQ (implFresh P s) G).run' st₀) εFS := by
    refine (Close.bind _ _ _ (fun s =>
      Pr{let z ← (simulateQ (implReal P s) G).run st₀}[z.2.fs = true]) fun s => ?_).mono ?_
    · constructor
      · rw [prEvent_run'_eq, prEvent_run'_eq]
        exact prEvent_real_le_fresh P s G st₀ (· = true)
      · rw [prEvent_run'_eq, prEvent_run'_eq]
        exact prEvent_fresh_le_real P s G st₀ (· = true)
    · -- the flag after the game is the flag after the proof
      refine le_trans (le_of_eq ?_) hFS
      rw [prEvent_bind_eq_tsum]
      refine tsum_congr fun s => ?_
      congr 1
      simp only [G, game, simulateQ_bind, StateT.run_bind, bind_map_left, map_bind]
      rw [prEvent_bind_eq_tsum_prEvent, prEvent_bind_eq_tsum_prEvent]
      refine tsum_congr fun z => ?_
      by_cases hz : z ∈ support ((simulateQ (implReal P s) skel).run st₀)
      · congr 1
        have hfs := liftPub_fs (implReal P s) (implReal_pub P s) (D z.1) z.2
        rw [prEvent_congr_of_support _ _ (fun _ => z.2.fs = true) fun y hy => by
          rw [hfs y hy]]
        rw [prEvent_pure]
        by_cases h : z.2.fs = true
        · simp [h, prEvent_const_of_lossless]
        · simp [h]
      · simp [prEvent_eq_zero_of_not_mem_support _ hz]
  -- step 2: the challenges drawn first
  have h2 : (do let s ← $ᵗ S; (simulateQ (implFresh P s) G).run' st₀) =ᵈ
      (do let s ← $ᵗ S; let σ ← uniformList O P.n; (simulateQ (implUp P σ s) G).run' st₀) := by
    refine EvalDistEq.bind_congr_of_support _ fun s _ => ?_
    have := (tape_evalDistEq P s G st₀ (by simp [st₀, St.init])).map Prod.fst
    simpa [st₀, St.init, StateT.run'_eq, map_bind] using this
  -- step 3: the unopened leaves apart
  have h3 : (do let s ← $ᵗ S; let σ ← uniformList O P.n; (simulateQ (implUp P σ s) G).run' st₀) =ᵈ
      (do let s ← $ᵗ S; let σ ← uniformList O P.n; (simulateQ (implSplit P σ s) G).run' st₀) :=
    EvalDistEq.bind_congr_of_support _ fun s _ => EvalDistEq.bind_congr_of_support _ fun σ _ =>
      implUp_evalDistEq_implSplit P σ s G st₀ rfl
  -- step 4: the simulator's implementation with the honest view, until `MBad`
  have h4 : Close
      (do let σ ← uniformList O P.n; let s ← $ᵗ S; (simulateQ (implSplit P σ s) G).run' st₀)
      (do let σ ← uniformList O P.n; let s ← $ᵗ S;
          (simulateQ (implView P σ (P.view s σ)) G).run' st₀) εM := by
    refine (Close.bind _ _ _ _ fun σ => (Close.bind _ _ _ (fun s =>
      Pr{let z ← (simulateQ (implView P σ (P.view s σ)) G).run st₀}[MBad (P.rows s σ) z.2])
      fun s => ?_)).mono ?_
    · constructor
      · rw [prEvent_run'_eq, prEvent_run'_eq]
        exact prEvent_split_le_view P σ s G st₀ (· = true)
      · rw [prEvent_run'_eq, prEvent_run'_eq]
        exact prEvent_view_le_split P σ s G st₀ (· = true)
    · refine le_trans (ENNReal.tsum_le_tsum fun σ => mul_le_mul_right (?_ : _ ≤ εM) _) ?_
      · have hb := prEvent_mBad_le P σ c₀ G (QP + QD) hG δ δ₂ (hent σ) (hent₂ σ)
        refine le_trans (le_of_eq ?_) hb
        rw [prEvent_bind_eq_tsum]
        refine tsum_congr fun s => ?_
        congr 1
        have hm : ((simulateQ (implView P σ (P.view s σ)) G).run (St.init c₀) >>= fun z =>
              (pure (s, z) : ProbComp (S × Bool × St I O K X))) =
            (fun z => (s, z)) <$> (simulateQ (implView P σ (P.view s σ)) G).run (St.init c₀) := by
          simp [map_eq_bind_pure_comp]
        rw [hm, prEvent_map]
      · rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]
  -- step 5: the simulated view
  have h5 : Close
      (do let σ ← uniformList O P.n; let v ← (fun s => P.view s σ) <$> ($ᵗ S);
          (simulateQ (implView P σ v) G).run' st₀)
      (do let σ ← uniformList O P.n; let v ← simV σ; (simulateQ (implView P σ v) G).run' st₀)
      εhv := by
    refine (Close.bind _ _ _ (fun σ => if good σ then 0 else 1) fun σ => ?_).mono ?_
    · by_cases hσ : good σ
      · simp only [hσ, ite_true]
        exact Close.of_evalDistEq ((hzk σ hσ).bind_left _)
      · simp only [hσ, ite_false]
        constructor <;> exact le_add_left (prEvent_le_one _)
    · refine le_trans (le_of_eq ?_) hgood
      rw [prEvent_eq_tsum_ite]
      refine tsum_congr fun σ => ?_
      by_cases hσ : good σ <;> simp [hσ]
  -- the swaps of the two first draws
  have hswapS : (($ᵗ S) >>= fun s => uniformList O P.n >>= fun σ =>
        (simulateQ (implSplit P σ s) G).run' st₀) =ᵈ
      (uniformList O P.n >>= fun σ => ($ᵗ S) >>= fun s =>
        (simulateQ (implSplit P σ s) G).run' st₀) :=
    EvalDistEq.bind_bind_swap _ _ _
  have hview : (uniformList O P.n >>= fun σ => ($ᵗ S) >>= fun s =>
        (simulateQ (implView P σ (P.view s σ)) G).run' st₀) =ᵈ
      (uniformList O P.n >>= fun σ => ((fun s => P.view s σ) <$> ($ᵗ S)) >>= fun v =>
        (simulateQ (implView P σ v) G).run' st₀) := by
    refine EvalDistEq.bind_congr_of_support _ fun σ _ => ?_
    rw [bind_map_left]
  -- the chain
  have hchain := ((((Close.of_evalDistEq hreal).trans h1).trans
    (Close.of_evalDistEq (h2.trans (h3.trans hswapS)))).trans h4).trans
      ((Close.of_evalDistEq hview).trans (h5.trans (Close.of_evalDistEq hsim.symm)))
  refine hchain.mono (le_of_eq ?_)
  simp only [add_zero, zero_add]
  ring

end Main

end QuotientZk
