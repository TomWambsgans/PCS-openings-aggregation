-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s indifferentiability of the sponge and its Keccak-256 transfer
-- (`Common.keccak256_transfer`), the statement's model read with a hash oracle and on bytes
-- (`Common.runK_expand`, `Common.runK_relabel`), applied as F4a's `QuotientRpm/Rpm.lean` applies
-- them.
import QuotientZk.RpmProver
import Common.Keccak
import Common.PiOnly

/-!
# Zero knowledge in the random-permutation model

## The random-oracle game with a distinguisher of the permutation

In the random-permutation model the distinguisher queries `π` and `π⁻¹`, not a hash. Read in the
random-oracle model through the indifferentiability simulator `S` (`Common.simulator`), its
permutation queries are answered by `S` from the random oracle's cache (`runS`). The real game
(`realGameS`: honest proof, then `D` through `S` from the prover's cache) and the simulated game
(`simGameS`: `sim`'s proof, then `D` through `S` from `sim`'s programmed cache) are `zk_rom`'s
games for the distinguisher `D` through `S`; `S` has coins, which `simulator_tape` draws first,
so that for each tape it is a coin-free distinguisher of the random oracle with at most as many
queries as `D` (`zk_rom_perm`).
-/

open OracleComp OracleSpec Common
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

/-! ## Closeness averaged over a first draw -/

/-- Games `ε`-close at every value of a first draw are `ε`-close after it. -/
theorem Close.bind_const {T : Type} (τ : ProbComp T) (R Sm : T → ProbComp Bool) (ε : ℝ≥0∞)
    (h : ∀ t, Close (R t) (Sm t) ε) : Close (τ >>= R) (τ >>= Sm) ε := by
  refine (Close.bind τ R Sm (fun _ ↦ ε) h).mono (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

/-! ## The random-oracle game with a distinguisher of the permutation -/

section PermRom

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C] [SampleableType Dg] [SampleableType E] [SampleableType C]
  [Inhabited Dg] [Inhabited E] [Inhabited C] [Inhabited Msg]
  (Pd : Padding Msg (Dg × E)) [Pd.Lawful] (iv : SpState Dg E C)

/-- **A distinguisher of the permutation in the random-oracle model**: its queries of `π` and
`π⁻¹` answered by the simulator `S` from its initial state, `S`'s hash queries by the random
oracle from the cache `c`. -/
noncomputable def runS (D : OracleComp (permutationOracleSpec (SpState Dg E C)) Bool)
    (c : (roSpec Msg Dg).QueryCache) : ProbComp Bool :=
  (simulateQ (roSpec Msg Dg).romImpl ((simulateQ (simulator Pd) D).run' (SimState.init iv))).run' c

/-- `D` through `S` with the simulator's tape `t`: a coin-free computation of the random oracle. -/
noncomputable def throughTape (t : List (SpState Dg E C))
    (D : OracleComp (permutationOracleSpec (SpState Dg E C)) Bool) :
    OracleComp (roSpec Msg Dg) Bool :=
  (simulateQ (simTape Pd) D).run' (SimState.init iv, t)

theorem runS_tape (D : OracleComp (permutationOracleSpec (SpState Dg E C)) Bool) (q : ℕ)
    (hD : IsTotalQueryBound D q) (c : (roSpec Msg Dg).QueryCache) :
    runS Pd iv D c =ᵈ (uniformList (SpState Dg E C) q >>= fun t ↦
      (simulateQ randomOracle (throughTape Pd iv t D)).run' c) :=
  simulator_tape Pd D q hD _ c

variable {S M K X Pf : Type} [DecidableEq K] [DecidableEq X] [SampleableType S]
  (P : Proto S Msg Dg M K X)

/-- **The real game, the distinguisher querying the permutation**: uniform randomness `s`, the
honest proof, then `D` with `π` and `π⁻¹` answered by `S` from the oracle's cache after the
proof. -/
noncomputable def realGameS (skel : OracleComp (OpSpec Msg Dg M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec (SpState Dg E C)) Bool) : ProbComp Bool := do
  let s ← $ᵗ S
  let z ← prove P s skel []
  runS Pd iv (D z.1) z.2

/-- **The simulated game, the distinguisher querying the permutation**: the simulator's proof,
then `D` with `π` and `π⁻¹` answered by `S` from the simulator's programmed cache. -/
noncomputable def simGameS (simV : List Dg → ProbComp (View M Msg K X))
    (skel : OracleComp (OpSpec Msg Dg M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec (SpState Dg E C)) Bool) : ProbComp Bool := do
  let z ← sim P simV skel []
  runS Pd iv (D z.1) z.2

theorem realGameS_tape (skel : OracleComp (OpSpec Msg Dg M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec (SpState Dg E C)) Bool) (q : ℕ)
    (hD : ∀ pf, IsTotalQueryBound (D pf) q) :
    realGameS Pd iv P skel D =ᵈ (uniformList (SpState Dg E C) q >>= fun t ↦
      realGame P skel [] fun pf ↦ throughTape Pd iv t (D pf)) := by
  unfold realGameS realGame
  calc (($ᵗ S) >>= fun s ↦ prove P s skel [] >>= fun z ↦ runS Pd iv (D z.1) z.2)
      =ᵈ (($ᵗ S) >>= fun s ↦ prove P s skel [] >>= fun z ↦
          uniformList (SpState Dg E C) q >>= fun t ↦
            (simulateQ randomOracle (throughTape Pd iv t (D z.1))).run' z.2) :=
        EvalDistEq.bind_congr_of_support _ fun s _ ↦ EvalDistEq.bind_congr_of_support _
          fun z _ ↦ runS_tape Pd iv (D z.1) q (hD z.1) z.2
    _ =ᵈ (($ᵗ S) >>= fun s ↦ uniformList (SpState Dg E C) q >>= fun t ↦
          prove P s skel [] >>= fun z ↦
            (simulateQ randomOracle (throughTape Pd iv t (D z.1))).run' z.2) :=
        EvalDistEq.bind_congr_of_support _ fun s _ ↦ EvalDistEq.bind_bind_swap _ _ _
    _ =ᵈ _ := EvalDistEq.bind_bind_swap _ _ _

theorem simGameS_tape (simV : List Dg → ProbComp (View M Msg K X))
    (skel : OracleComp (OpSpec Msg Dg M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec (SpState Dg E C)) Bool) (q : ℕ)
    (hD : ∀ pf, IsTotalQueryBound (D pf) q) :
    simGameS Pd iv P simV skel D =ᵈ (uniformList (SpState Dg E C) q >>= fun t ↦
      simGame P simV skel [] fun pf ↦ throughTape Pd iv t (D pf)) := by
  unfold simGameS simGame
  calc (sim P simV skel [] >>= fun z ↦ runS Pd iv (D z.1) z.2)
      =ᵈ (sim P simV skel [] >>= fun z ↦ uniformList (SpState Dg E C) q >>= fun t ↦
            (simulateQ randomOracle (throughTape Pd iv t (D z.1))).run' z.2) :=
        EvalDistEq.bind_congr_of_support _ fun z _ ↦ runS_tape Pd iv (D z.1) q (hD z.1) z.2
    _ =ᵈ _ := EvalDistEq.bind_bind_swap _ _ _

/-- **Zero knowledge in the random-oracle model against a distinguisher of the permutation.**
`zk_rom`'s bound, for a distinguisher `D` with at most `QD` queries of `π` and `π⁻¹`, answered by
the indifferentiability simulator from the random oracle (`S` asks the oracle at most once per
query). -/
theorem zk_rom_perm [Fintype (K × X)] (skel : OracleComp (OpSpec Msg Dg M K X) Pf)
    (simV : List Dg → ProbComp (View M Msg K X)) (good : List Dg → Prop)
    (εFS εhv δ δ₂ : ℝ≥0∞) (QP QD : ℕ)
    (hQP : IsTotalQueryBound skel QP)
    (hFS : Pr{let x ← (do
        let s ← $ᵗ S
        let z ← (simulateQ (implReal P s) skel).run (St.init [])
        return z.2.fs)}[x = true] ≤ εFS)
    (hzk : ∀ σ, good σ → (fun s ↦ P.view s σ) <$> ($ᵗ S) =ᵈ simV σ)
    (hgood : Pr{let σ ← uniformList Dg P.n}[¬ good σ] ≤ εhv)
    (hent : ∀ σ k x, P.opened σ k x = false → ∀ v y,
      Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = y] ≤
        δ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hent₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') → ∀ v,
        Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = P.rows s σ k' x'] ≤
          δ₂ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (D : Pf → OracleComp (permutationOracleSpec (SpState Dg E C)) Bool)
    (hD : ∀ pf, IsTotalQueryBound (D pf) QD) :
    Close (realGameS Pd iv P skel D) (simGameS Pd iv P simV skel D)
      (εFS + εhv + ((Fintype.card (K × X) * (QP + QD) : ℕ) * δ +
        (Fintype.card (K × X) ^ 2 : ℕ) * δ₂)) := by
  refine Close.trans (Close.of_evalDistEq (realGameS_tape Pd iv P skel D QD hD)) ?_ |>.mono
    (le_of_eq (zero_add _))
  refine Close.trans ?_ (Close.of_evalDistEq (simGameS_tape Pd iv P simV skel D QD hD).symm)
    |>.mono (le_of_eq (add_zero _))
  refine Close.bind_const _ _ _ _ fun t ↦ ?_
  refine (zk_rom P skel [] simV good εFS εhv δ δ₂ QP QD hQP hFS hzk hgood hent hent₂ _
    fun pf ↦ isTotalQueryBound_simTape Pd (D pf) QD (hD pf) _).mono (le_of_eq ?_)
  simp

end PermRom

end QuotientZk
