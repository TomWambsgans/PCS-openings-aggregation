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

leanerVM's model (`Statement/RandomPermutation.lean`): one uniformly random permutation `π` of the
Keccak-f[1600] state, queried forward and inverse; Keccak-256 is the sponge over `π`
(`Common.keccak256OverPermutation`).

**The games.** The real game (`realGameRpm`): uniform randomness `s`; the prover of `zk_rom` (the
skeleton `skel` with the honest messages and rows), every hash Keccak-256 over `π` (`proverWith`
with `keccak256OverPermutation`); then the distinguisher `D`, which sees the proof and queries `π`
and `π⁻¹` (`zkGameRpm`, run with `Common.runWithRandomPermutation`). The simulated game
(`simGameRpm`): the simulator, without `s`, runs `zk_rom`'s `sim` (the challenges programmed into
the random oracle, the simulated view, fresh private digests at the unopened leaves), which gives
the proof and the programmed cache; then it answers `D`'s queries of `π` and `π⁻¹` itself, with
the indifferentiability simulator `S` of Bertoni, Daemen, Peeters and Van Assche
(`Common.simulator`, through the lanes-to-bytes bijection: `simPerm`), whose Keccak-256 queries
are answered by the random oracle from the programmed cache. A forward query that ends a sponge
path padding a message `m` gets `H m` (programmed or fresh) completed by uniform bits; any other
fresh query a uniform state.

**The simulator's cost.** No query of the real `π` (it emulates `π`, as `sim` programs the random
oracle); `sim`'s cost (`n` uniform challenges, `simV`, the skeleton's `QP` operations, each a
cache lookup or a uniform digest); and per query of `D` one step of `S`: lookups in at most `QD`
edges and `QD + 1` rooted states, the unpadding of one path, at most one random-oracle lookup or
uniform digest and one uniform state.

**The theorem** (`zk_rpm`). The two games output `true` with probabilities within
`εFS + εhv + N (QP + QD) δ + N² δ₂ + Q² / 2^509`: `zk_rom`'s bound (empty cache before the
proof; `D` through `S` asks the random oracle at most `QD` times) plus `common`'s
indifferentiability term for the `Q` permutation calls of the real game.

**The proof.** ZK is a single-stage game: the real game, prover and distinguisher together, is one
distinguisher of the indifferentiability game (the prover's hashes are its queries of `H`, `D`'s
queries are its queries of `π`), so `common`'s transfer (`Common.keccak256_transfer`, after the
statement's model is read with a Keccak-256 oracle, `Common.runK_expand`, and on bytes,
`Common.runK_relabel`) moves it to the random-oracle model with `D`'s queries answered by `S`
(`realGameRpm_close`). There it is `zk_rom`'s real game for the distinguisher `D` through `S`
(`realGameS`; the prover asking the random oracle is `implReal`, `romImpl_proverWith`), and the
simulated game is `zk_rom`'s simulated game for the same distinguisher (`simGameS`), equal to
`simGameRpm` by definition: the indifferentiability term is paid once, on the real side. `S` has
coins and `zk_rom`'s distinguisher has none: `simulator_tape` draws `S`'s `QD` uniform states
first, and for each tape `D` through `S` is a coin-free distinguisher of the random oracle with
at most `QD` queries (`zk_rom_perm`), the bound averaged over the tape.

**Scope.** Here every hash of the prover is Keccak-256 over `π` (one oracle `List UInt8 →ₒ 32
bytes`); the deployed prover, whose openings' duplex calls Keccak-f[1600] directly, on
`zk_deployed`'s oracle, is `RpmDeployed.lean` / `RpmJoint.lean` (see the end of this file). `D` has
no coins (statistical zero knowledge: a distinguisher with coins is an average of coin-free ones
over its coin tape).
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

/-! ## The random-oracle game with a distinguisher of the permutation

In the random-permutation model the distinguisher queries `π` and `π⁻¹`, not a hash. Read in the
random-oracle model through `S`, its permutation queries are answered by `S` from the random
oracle's cache (`runS`). The real game (`realGameS`: honest proof, then `D` through `S` from the
prover's cache) and the simulated game (`simGameS`: `sim`'s proof, then `D` through `S` from
`sim`'s programmed cache) are `zk_rom`'s games for the distinguisher `D` through `S`, once `S`'s
coins are drawn first (`zk_rom_perm`). -/

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

/-! ## Keccak-256 over a random permutation -/

section Keccak

open LeanVM.Rpm

/-- The statement's Keccak state, `25` lanes (`Common.KState` is the bytes'). -/
local notation "LState" => LeanVM.Semantics.KeccakState

variable {S M K X Pf : Type} [DecidableEq K] [DecidableEq X] [SampleableType S]
  (P : Proto S (List UInt8) DigestBytes M K X)

/-- A query of `π` or `π⁻¹` in the statement's model. -/
def permQuery : QueryImpl (permutationOracleSpec LState) (OracleComp RandomPermutationOracles) :=
  fun q ↦ liftM (RandomPermutationOracles.query (.inr q))

/-- **The real game for the secret `s`, in the random-permutation model**: the prover's proof,
every hash Keccak-256 over `π` (`keccak256OverPermutation`), then the distinguisher `D` with `π`
and `π⁻¹`. -/
noncomputable def zkGameRpm (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool) (s : S) :
    OracleComp RandomPermutationOracles Bool :=
  proverWith P keccak256OverPermutation s skel >>= fun pf ↦ simulateQ permQuery (D pf)

/-- **The real game in the random-permutation model**: uniform randomness `s`, then `zkGameRpm`
against the lazily sampled random permutation (`runWithRandomPermutation`). -/
noncomputable def realGameRpm (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool) : ProbComp Bool := do
  let s ← $ᵗ S
  runWithRandomPermutation (zkGameRpm P skel D s)

/-- A permutation query on lanes, asked on bytes (`Common.Lanes`: byte `8i + k` is byte `k` of
lane `i`), its answer read back on lanes. -/
def laneToByte :
    QueryImpl (permutationOracleSpec LState) (OracleComp (permutationOracleSpec KState)) :=
  fun q ↦ KState.ofRpm <$> liftM ((permutationOracleSpec KState).query (mapQ stateEquiv q))

/-- **The simulator's permutation**: `π` and `π⁻¹` on lanes answered by the indifferentiability
simulator `S` (`Common.simulator`) on bytes, which asks Keccak-256 of the random oracle. -/
noncomputable def simPerm : QueryImpl (permutationOracleSpec LState)
    (StateT (SimState DigestBytes KRest KCap) (OracleComp (unifSpec + roSpec (List UInt8) DigestBytes))) :=
  (simulator keccakPadding) ∘ₛ laneToByte

/-- **The simulated game in the random-permutation model.** The simulator, without the secret:
the random-oracle simulator `sim` (the challenges programmed, the simulated view, fresh private
digests at the unopened leaves) gives the proof and the random oracle's programmed cache; then
it answers the distinguisher's queries of `π` and `π⁻¹` with `S` (`simPerm`), from its initial
state, `S`'s Keccak-256 queries answered by the random oracle from that cache. -/
noncomputable def simGameRpm (simV : List DigestBytes → ProbComp (View M (List UInt8) K X))
    (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool) : ProbComp Bool := do
  let z ← sim P simV skel []
  (simulateQ (roSpec (List UInt8) DigestBytes).romImpl
    ((simulateQ simPerm (D z.1)).run' (SimState.init KState.zero))).run' z.2

theorem simGameRpm_eq (simV : List DigestBytes → ProbComp (View M (List UInt8) K X))
    (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool) :
    simGameRpm P simV skel D =
      simGameS keccakPadding KState.zero P simV skel fun pf ↦ simulateQ laneToByte (D pf) := by
  simp only [simGameRpm, simGameS, runS, simPerm, QueryImpl.simulateQ_compose]

theorem isTotalQueryBound_laneToByte {α : Type} (D : OracleComp (permutationOracleSpec LState) α)
    (q : ℕ) (hD : IsTotalQueryBound D q) : IsTotalQueryBound (simulateQ laneToByte D) q :=
  IsTotalQueryBound.simulateQ_of_step hD fun _ ↦ by
    rw [laneToByte, map_eq_bind_pure_comp]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ ↦ trivial⟩

/-! ### The real game read with a Keccak-256 oracle, then on bytes -/

/-- A Keccak-256 query, in the model with a hash oracle (`Common.KSpecH`). -/
def hashH (m : List UInt8) : OracleComp KSpecH DigestBytes := liftM (KSpecH.query (.inr (.inl m)))

/-- A permutation query, in the model with a hash oracle. -/
def permH : QueryImpl (permutationOracleSpec LState) (OracleComp KSpecH) :=
  fun q ↦ liftM (KSpecH.query (.inr (.inr q)))

/-- A permutation query on bytes, among the distinguisher's oracles (`Common.KSpecB`). -/
def permB : QueryImpl (permutationOracleSpec KState) (OracleComp KSpecB) :=
  fun q ↦ liftM (KSpecB.query (.inr (.inr q)))

/-- The real game for `s` with a Keccak-256 oracle. -/
noncomputable def gameH (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool) (s : S) : OracleComp KSpecH Bool :=
  proverWith P hashH s skel >>= fun pf ↦ simulateQ permH (D pf)

theorem expand_gameH (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool) (s : S) :
    simulateQ expand (gameH P skel D s) = zkGameRpm P skel D s := by
  have h1 : (fun t ↦ simulateQ expand (hashH t)) = keccak256OverPermutation := by
    funext t
    simp only [hashH, simulateQ_spec_query]
    rfl
  have h2 : expand ∘ₛ permH = permQuery := by
    funext q
    simp only [QueryImpl.apply_compose, permH, simulateQ_spec_query]
    rfl
  simp only [gameH, zkGameRpm, simulateQ_bind, simulateQ_proverWith, h1,
    ← QueryImpl.simulateQ_compose, h2]

theorem relabel_gameH (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool) (s : S) :
    simulateQ relabel (gameH P skel D s) =
      Common.rpmGame (proverWith P roHash s skel)
        (fun pf ↦ simulateQ permB (simulateQ laneToByte (D pf))) (fun _ b ↦ pure b) := by
  have h1 : (fun t ↦ simulateQ relabel (hashH t)) =
      (fun t ↦ simulateQ (hEmbed (E := KRest) (C := KCap)) (roHash (O := DigestBytes) t)) := by
    funext t
    simp only [hashH, roHash, Common.hq, simulateQ_spec_query]
    rfl
  have h2 : relabel ∘ₛ permH = permB ∘ₛ laneToByte := by
    funext q
    simp only [QueryImpl.apply_compose, permH, simulateQ_spec_query, laneToByte, simulateQ_map]
    rfl
  simp only [gameH, Common.rpmGame, liftH, simulateQ_bind, simulateQ_proverWith, h1,
    ← QueryImpl.simulateQ_compose, h2, simulateQ_pure, bind_pure]

/-- **The real games, in the random-permutation model and in the random-oracle model with the
distinguisher through `S`, are `Q² / 2^509`-close** (`common`'s transfer), for a real game of at
most `Q` permutation calls on every path. -/
theorem realGameRpm_close (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool) (Q : ℕ)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpm P skel D s) permutationCallCost Q) :
    Close (realGameRpm P skel D)
      (realGameS keccakPadding KState.zero P skel fun pf ↦ simulateQ laneToByte (D pf))
      ((Q ^ 2 : ℝ≥0∞) / 2 ^ 509) := by
  unfold realGameRpm realGameS
  refine Close.bind_const _ _ _ _ fun s ↦ ?_
  set pre := proverWith P roHash s skel
  set A := fun pf ↦ simulateQ permB (simulateQ laneToByte (D pf))
  have hQH : QueryCostAtMost (gameH P skel D s) permCallsH Q :=
    (isWeightBound_expand_iff _ _).mp (by rw [expand_gameH]; exact hQ s)
  have hQB : QueryCostAtMost (Common.rpmGame pre A fun _ b ↦ pure b)
      (queryCost (Dg := DigestBytes) keccakPadding) Q := by
    rw [← SufCma.permCallsB_eq, ← relabel_gameH]
    exact isWeightBound_relabel hQH
  obtain ⟨h1, h2⟩ := keccak256_transfer pre A (fun _ b ↦ pure b) Q hQB (· = true)
  have hL : runWithRandomPermutation (zkGameRpm P skel D s) =ᵈ
      Common.realGame keccakPadding KState.zero (Common.rpmGame pre A fun _ b ↦ pure b) := by
    rw [← expand_gameH, runK_expand, ← relabel_gameH]
    exact runK_relabel _
  have hR : romRun (pre >>= fun x ↦ advS keccakPadding KState.zero (A x) >>= fun a ↦ pure a) =ᵈ
      (prove P s skel [] >>= fun z ↦
        runS keccakPadding KState.zero (simulateQ laneToByte (D z.1)) z.2) := by
    simp only [romRun, bind_pure, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    refine EvalDistEq.bind_left (romImpl_proverWith P s skel) _ |>.trans ?_
    refine EvalDistEq.bind_congr_of_support _ fun z _ ↦ ?_
    simp only [A, advS, runS, StateT.run'_eq, ← QueryImpl.simulateQ_compose]
    exact EvalDistEq.rfl
  constructor
  · rw [hL.prEvent_eq, ← hR.prEvent_eq]; exact h1
  · rw [hL.prEvent_eq, ← hR.prEvent_eq]; exact h2

/-- **Zero knowledge in the random-permutation model.** For every distinguisher `D` that sees the
proof and then makes at most `QD` queries of `π` and `π⁻¹` (no coins), if the real game makes at
most `Q` permutation calls on every path (the prover's Keccak-256 hashes, `⌊n / 136⌋ + 1` calls
for `n` bytes, and `D`'s queries), the real game (`realGameRpm`: the prover hashing with
Keccak-256 over the random permutation, then `D`) and the simulated game (`simGameRpm`: `sim`'s
proof and programmed cache, then `D` with `π` and `π⁻¹` answered by the indifferentiability
simulator `S` over that cache) output `true` with probabilities within

  `εFS + εhv + N (QP + QD) δ + N² δ₂ + Q² / 2^509`,

`zk_rom`'s bound (the empty cache before the proof, `QD` queries of the random oracle by `D`
through `S`) and `common`'s indifferentiability term. `zk_rom`'s hypotheses are kept as they are. -/
theorem zk_rpm [Fintype (K × X)] (skel : OracleComp (OpSpec (List UInt8) DigestBytes M K X) Pf)
    (simV : List DigestBytes → ProbComp (View M (List UInt8) K X)) (good : List DigestBytes → Prop)
    (εFS εhv δ δ₂ : ℝ≥0∞) (QP QD Q : ℕ)
    (hQP : IsTotalQueryBound skel QP)
    (hFS : Pr{let x ← (do
        let s ← $ᵗ S
        let z ← (simulateQ (implReal P s) skel).run (St.init [])
        return z.2.fs)}[x = true] ≤ εFS)
    (hzk : ∀ σ, good σ → (fun s ↦ P.view s σ) <$> ($ᵗ S) =ᵈ simV σ)
    (hgood : Pr{let σ ← uniformList DigestBytes P.n}[¬ good σ] ≤ εhv)
    (hent : ∀ σ k x, P.opened σ k x = false → ∀ v y,
      Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = y] ≤
        δ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hent₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') → ∀ v,
        Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = P.rows s σ k' x'] ≤
          δ₂ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (D : Pf → OracleComp (permutationOracleSpec LState) Bool)
    (hD : ∀ pf, IsTotalQueryBound (D pf) QD)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpm P skel D s) permutationCallCost Q) :
    Close (realGameRpm P skel D) (simGameRpm P simV skel D)
      (εFS + εhv + ((Fintype.card (K × X) * (QP + QD) : ℕ) * δ +
        (Fintype.card (K × X) ^ 2 : ℕ) * δ₂) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509) := by
  rw [simGameRpm_eq]
  refine ((realGameRpm_close P skel D Q hQ).trans (zk_rom_perm keccakPadding KState.zero P skel
    simV good εFS εhv δ δ₂ QP QD hQP hFS hzk hgood hent hent₂ _
    fun pf ↦ isTotalQueryBound_laneToByte (D pf) QD (hD pf))).mono (le_of_eq ?_)
  rw [add_comm]

end Keccak

/-! ## The openings' duplex

The openings' Fiat–Shamir duplex (`crates/fiat_shamir`) calls Keccak-f[1600] directly; the
verifier, hence `D`, recomputes it from the proof, so a simulator that programs its challenges must
answer `D`'s queries of `π` on the duplex states with the programmed outputs. That is
`RpmDeployed.lean` (`zk_rpm_deployed`, and `RpmJoint.lean` for the end statements): `common`'s
two-oracle model for the whole game (`transfer2_game`, `Q² / 2^508`), the shadow world's record of
the prover's permutation calls replayed by the simulator (`skelRec`), on `zk_deployed`'s oracle. -/

end QuotientZk
