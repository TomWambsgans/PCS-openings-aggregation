-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s two-oracle model (`Common.Indiff2`, `Common.Transfer2`,
-- `Common.keccak_indiffBound2_le`, `Common.not_keccakNF_of_pad`) and the statement's model read
-- with a Keccak-256 oracle and on bytes (`Common.runK_expand`, `Common.runK_relabel`), applied as
-- F4a's `QuotientRpm/Rpm.lean` applies them.
import QuotientZk.RpmDuplexProver
import QuotientZk.RpmMain
import QuotientZk.JointDeployed

/-!
# Zero knowledge of the deployed proof in the random-permutation model

leanerVM's model (`Statement/RandomPermutation.lean`): one uniformly random permutation `π` of the
Keccak-f[1600] state, queried forward and inverse. **The deployed prover** hashes as the Rust
does: Keccak-256 over `π` (`Common.keccak256OverPermutation`: the reduction's chain, the Merkle
trees, the openings' IVs) and the duplex's permutations as calls of `π` (`Common.queryPermutation`),
on `zk_deployed`'s skeleton `Deployed.skel` (`proverJ`; its private completions of the oracle's
answers drawn with its coins, which the skeleton never reads).

* **The real game** (`realGameRpmD`): uniform randomness `s`; the proof; then the distinguisher
  `D`, which sees the proof and queries `π` and `π⁻¹`.
* **The simulated game** (`simGameRpmD`). The simulator, without `s`: `zk_rom`'s `sim` on the
  skeleton with the duplex's bookkeeping (`skelRec`): the challenges programmed into `G`, the
  simulated view, fresh private digests at the unopened leaves; it gives the proof, the
  bookkeeping `σ` of the skeleton's permutation calls (the duplex's states and programmed outputs,
  on bytes) and `G`'s programmed cache. Then it answers `D`'s queries of `π` and `π⁻¹` with
  `common`'s two-oracle simulator `S₂` (`Common.simulator2`) from `σ`, its `H` and `F` the cache's
  digests and permutation answers (`hfOf`). `S₂` answers a recorded edge from `σ` (so the duplex
  `D` recomputes from the proof meets the programmed challenges), a fresh forward query ending a
  sponge path padding `m` with `H m` completed by uniform bits, any other fresh forward query with
  `F`, a fresh inverse query uniformly.
* **The simulator's cost**: no query of a real `π`; `sim`'s (the `n` uniform challenges, `simV`,
  the skeleton's at most `skelBound sh ≤ 2^70` operations, each a cache lookup, a programmed
  answer or a uniform digest, and the replay of its permutation calls); per query of `D` one step of
  `S₂`: lookups in its edges and rooted states, the unpadding of one path, at most one lookup or
  uniform answer of the cache and one uniform state.

**`zk_rpm_deployed`**: within `εFS + εhv + 2^24 (skelBound sh + QD) δ + 2^48 δ₂ + Q² / 2^508`;
**`zk_rpm_deployed_bits`**: `εFS + εhv + 2^-2200 + Q² / 2^508`; **`zk_rpm_deployed_joint`** (the
joint honest-verifier zero knowledge of `JointDeployed.lean`): `εFS + 2^-165 + 2^-2200 + Q² / 2^508`.
`Q` bounds the real game's calls of `π` and `π⁻¹` on every path (the prover's Keccak-256 hashes,
`⌊n / 136⌋ + 1` calls for `n` bytes, its permutation calls, `D`'s queries).

**The proof.** ZK is a single-stage game: the real game, prover and distinguisher together, is one
game of `common`'s two-oracle model (`H` for Keccak-256, `F` for the prover's permutation calls,
`π` and `π⁻¹` for `D`'s), so `transfer2_game` moves it to the shadow world at `indiffBound2`
(`Q² / 2^508`) once the prover's permutation calls follow the duplex discipline (`hduplex`). In the
shadow world the prover's permutation calls are recorded in the simulator's state
(`recImpl_implHF`): that is `skelRec`'s bookkeeping; with `H` and `F` lazily sampled the prover is
`zk_rom`'s `implReal` for `G` (`romImpl_proverHF`), and `D` through `S₂` from the bookkeeping is,
once `S₂`'s coins are drawn first (`simulator2_tape`) and `H`, `F` read on `G` (`ro_enc`), a
coin-free distinguisher of `G` with at most `QD` queries: `zk_rom` (or `zk_deployed`'s
instantiation of it) applies to `skelRec (skel sh)`, and the simulated game is its simulated game,
the indifferentiability term paid once.

**New hypotheses** beyond `zk_deployed`'s: `hrow` (the secret tables' rows are byte strings, as
`Deployed.leafH` reads them), `hduplex` (each permutation call of the prover absorbs a non-final
block into the zero state or an earlier permutation answer, keeping its capacity: the overwrite
duplex, `Common.keccakNF_blockTo`), `hQ` (the permutation budget); `D` has no coins.
-/

open OracleComp OracleSpec Common LeanVM.Rpm
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec Proof)
open scoped ENNReal

namespace QuotientZk.DRpm

set_option linter.unusedSectionVars false

/-! ## The two-oracle game's duplex discipline and cost -/

/-- The game's oracles of the two-oracle model on Keccak's byte states. -/
abbrev DS2 := dSpec2 (List UInt8) DigestBytes KState

/-- The prover's direct calls are the game's; after them a computation without direct calls. -/
theorem duplexOK_hfEmbed_bind (NF : KBlock → Prop) {α δ : Type} (f : α → OracleComp DS2 δ)
    (hf : ∀ a h, DuplexOK KState.zero NF (f a) h) (X : OracleComp (unifSpec + HF) α) :
    ∀ hist, Duplex KState.zero NF X hist →
      DuplexOK KState.zero NF (simulateQ (hfEmbed (Msg := List UInt8)) X >>= f) hist := by
  induction X using OracleComp.inductionOn with
  | pure a => intro hist _; simpa using hf a hist
  | query_bind t k ih =>
    intro hist hX
    rw [simulateQ_query_bind, bind_assoc]
    rcases t with n | m | x
    · exact (duplexOK_query_bind_other KState.zero NF (.inl n) (by simp) _ hist).mpr
        fun u ↦ ih u hist (hX u)
    · exact (duplexOK_query_bind_other KState.zero NF (.inr (.inl m)) (by simp) _ hist).mpr
        fun u ↦ ih u hist (hX u)
    · exact (duplexOK_query_bind_F KState.zero NF x _ hist).mpr
        ⟨hX.1, fun y ↦ ih y (y :: hist) (hX.2 y)⟩

/-- The distinguisher's queries of `π` and `π⁻¹` in the game. -/
def permD2 : QueryImpl (permutationOracleSpec KState) (OracleComp DS2) :=
  fun q ↦ liftM (DS2.query (.inr (.inr (.inl q))))

theorem duplexOK_permD2 (NF : KBlock → Prop) {α : Type}
    (Y : OracleComp (permutationOracleSpec KState) α) :
    ∀ hist, DuplexOK KState.zero NF (simulateQ permD2 Y) hist := by
  induction Y using OracleComp.inductionOn with
  | pure a => intro hist; trivial
  | query_bind q k ih =>
    intro hist
    rw [simulateQ_query_bind]
    exact (duplexOK_query_bind_other KState.zero NF (.inr (.inr (.inl q))) (by simp) _ hist).mpr
      fun u ↦ ih u hist

/-- A game of the two-oracle model weighs what it weighs with its direct calls read as
permutation queries. -/
theorem isWeightBound_of_toOne {α : Type} (G : OracleComp DS2 α) :
    ∀ q, QueryCostAtMost (simulateQ (toOne (E := KRest) (C := KCap)) G)
      (queryCost (Dg := DigestBytes) keccakPadding) q →
      QueryCostAtMost G (queryCost2 (Dg := DigestBytes) keccakPadding) q := by
  induction G using OracleComp.inductionOn with
  | pure a => intro q _; trivial
  | query_bind t k ih =>
    intro q h
    rw [simulateQ_query_bind] at h
    rw [isWeightBound_query_bind_iff]
    rcases t with n | m | qq | x
    · change QueryCostAtMost (liftM (KSpecB.query (.inl n)) >>= fun u ↦
        simulateQ (toOne (E := KRest) (C := KCap)) (k u)) _ q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inl m))) >>= fun u ↦
        simulateQ (toOne (E := KRest) (C := KCap)) (k u)) _ q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inr qq))) >>= fun u ↦
        simulateQ (toOne (E := KRest) (C := KCap)) (k u)) _ q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inr (.forward x)))) >>= fun u ↦
        simulateQ (toOne (E := KRest) (C := KCap)) (k u)) _ q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩

/-! ## The games -/

variable {S : Type} [SampleableType S] (P : Proto S Inp Out Msg Tbl Pos)

/-- Coins in the statement's model. -/
noncomputable abbrev coinR (α : Type) [SampleableType α] : OracleComp RandomPermutationOracles α :=
  liftM ($ᵗ α)

/-- **The real game for the secret `s`, in the random-permutation model**: the deployed prover's
proof (Keccak-256 over `π`, the duplex's permutations calls of `π`, its coins for the
completions), then `D` with `π` and `π⁻¹`. -/
noncomputable def zkGameRpmD (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (s : S) :
    OracleComp RandomPermutationOracles Bool :=
  proverJ P keccak256OverPermutation queryPermutation (coinR KSt) (coinR DigestBytes) s skel >>=
    fun pf ↦ simulateQ permQuery (D pf)

/-- **The real game in the random-permutation model.** -/
noncomputable def realGameRpmD (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) : ProbComp Bool := do
  let s ← $ᵗ S
  runWithRandomPermutation (zkGameRpmD P skel D s)

/-- `D` through `S₂` from the bookkeeping `σ`, `S₂`'s `H` and `F` lazily sampled from `c₂`. -/
noncomputable def runS2 (D : OracleComp (permutationOracleSpec KSt) Bool) (σ : SimSt)
    (c₂ : HF.QueryCache) : ProbComp Bool :=
  (simulateQ HF.romImpl ((simulateQ (simulator2 (Msg := List UInt8) keccakPadding)
    (simulateQ laneToByte D)).run' σ)).run' c₂

/-- **The simulated game in the random-permutation model.** The simulator: `zk_rom`'s `sim` on the
skeleton with the duplex's bookkeeping, giving the proof, the bookkeeping `σ` and `G`'s programmed
cache `c`; then `D`'s queries of `π` and `π⁻¹` answered by `S₂` from `σ`, with `H` and `F` the
cache read through `hfOf`. -/
noncomputable def simGameRpmD (simV : List Out → ProbComp (View Msg Inp Tbl Pos))
    (skel : OracleComp DSpec Proof) (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) :
    ProbComp Bool := do
  let z ← sim P simV (skelRec skel) []
  runS2 (D z.1.1) z.1.2 (hfOf z.2)

/-! ## The real game read with a Keccak-256 oracle, on bytes, in the two-oracle model -/

/-- The real game with a Keccak-256 oracle. -/
noncomputable def gameHD (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (s : S) : OracleComp KSpecH Bool :=
  proverJ P hashH (fun x ↦ permH (.forward x)) (liftM ($ᵗ KSt)) (liftM ($ᵗ DigestBytes)) s skel >>=
    fun pf ↦ simulateQ permH (D pf)

/-- The real game in the two-oracle model: the prover with `H` and `F`, embedded; `D` through
`π`, `π⁻¹` on bytes. -/
noncomputable def game2D (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (s : S) : OracleComp DS2 Bool :=
  simulateQ (hfEmbed (Msg := List UInt8)) (proverJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s skel)
    >>= fun pf ↦ simulateQ permD2 (simulateQ laneToByte (D pf))

theorem expand_gameHD (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (s : S) :
    simulateQ expand (gameHD P skel D s) = zkGameRpmD P skel D s := by
  have h1 : (fun t ↦ simulateQ expand (hashH t)) = keccak256OverPermutation := by
    funext t
    simp only [hashH, simulateQ_spec_query]
    rfl
  have h2 : (fun x ↦ simulateQ expand (permH (.forward x))) = queryPermutation := by
    funext x
    simp only [permH, simulateQ_spec_query]
    rfl
  have h3 : expand ∘ₛ permH = permQuery := by
    funext q
    simp only [QueryImpl.apply_compose, permH, simulateQ_spec_query]
    rfl
  have hc : ∀ (α : Type) [SampleableType α],
      simulateQ expand (liftM ($ᵗ α) : OracleComp KSpecH α) = coinR α := fun α _ ↦
    simulateQ_liftM_of_coins expand (fun _ ↦ rfl) _
  simp only [gameHD, zkGameRpmD, simulateQ_bind, simulateQ_proverJ, h1, h2, hc,
    ← QueryImpl.simulateQ_compose, h3]

theorem relabel_gameHD (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (s : S) :
    simulateQ relabel (gameHD P skel D s) = simulateQ (toOne (E := KRest) (C := KCap))
      (game2D P skel D s) := by
  have hH : (fun t ↦ simulateQ relabel (hashH t)) =
      (fun t ↦ simulateQ (toOne (E := KRest) (C := KCap))
        (simulateQ (hfEmbed (Msg := List UInt8)) (hH2 t))) := by
    funext t
    simp only [hashH, hH2, hQuery, simulateQ_spec_query, simulateQ_hq]
    rfl
  have hF : (fun x ↦ simulateQ relabel (permH (.forward x))) =
      (fun x ↦ simulateQ (toOne (E := KRest) (C := KCap))
        (simulateQ (hfEmbed (Msg := List UInt8)) (hF2 x))) := by
    funext x
    simp only [permH, hF2, fQuery, simulateQ_spec_query, simulateQ_map, simulateQ_hq]
    rfl
  have hc : ∀ (α : Type) [SampleableType α],
      simulateQ relabel (liftM ($ᵗ α) : OracleComp KSpecH α) =
        simulateQ (toOne (E := KRest) (C := KCap))
          (simulateQ (hfEmbed (Msg := List UInt8)) (coin2 α)) := fun α _ ↦ by
    rw [simulateQ_liftM_of_coins relabel (fun _ ↦ rfl),
      simulateQ_liftM_of_coins (hfEmbed (Msg := List UInt8)) (fun _ ↦ rfl),
      simulateQ_liftM_of_coins (toOne (E := KRest) (C := KCap)) (fun _ ↦ rfl)]
  have hD : relabel ∘ₛ permH = toOne (E := KRest) (C := KCap) ∘ₛ (permD2 ∘ₛ laneToByte) := by
    funext q
    simp only [QueryImpl.apply_compose, permH, simulateQ_spec_query, laneToByte, simulateQ_map,
      permD2]
    rfl
  simp only [gameHD, game2D, simulateQ_bind, simulateQ_proverJ, hH, hF, hc,
    ← QueryImpl.simulateQ_compose, hD]

/-- **The real game is the two-oracle model's real world**, in distribution. -/
theorem runRpm_gameD (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (s : S) :
    runWithRandomPermutation (zkGameRpmD P skel D s) =ᵈ
      realGame2 keccakPadding KState.zero (game2D P skel D s) := by
  rw [← expand_gameHD, runK_expand]
  refine (runK_relabel _).trans ?_
  rw [relabel_gameHD]
  exact EvalDistEq.rfl

/-! ## The shadow world of the real game -/

theorem shadow_permD2 : shadowImpl keccakPadding ∘ₛ permD2 = simulator2 (Msg := List UInt8) keccakPadding := by
  funext q
  simp only [QueryImpl.apply_compose, permD2, simulateQ_spec_query]
  rfl

theorem shadow_permD2_lanes : shadowImpl keccakPadding ∘ₛ (permD2 ∘ₛ laneToByte) =
    simulator2 (Msg := List UInt8) keccakPadding ∘ₛ laneToByte := by
  funext q
  simp only [QueryImpl.apply_compose]
  rw [← QueryImpl.simulateQ_compose, shadow_permD2]

/-- The prover with its permutation calls recorded is the skeleton with its bookkeeping. -/
theorem recImpl_proverJ (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (s : S)
    (skel : OracleComp DSpec Proof) :
    (simulateQ recImpl (proverJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s skel)).run
        (SimState.init KState.zero) =
      proverJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s (skelRec skel) := by
  unfold proverJ skelRec
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, recImpl_implHF P hrow s skel, StateT.run'_eq,
    Functor.map_map]

/-- **The real game's shadow world** is the prover's run on the skeleton with its bookkeeping,
then `D` through `S₂` from the bookkeeping. -/
theorem shadow_game2D (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (s : S)
    (skel : OracleComp DSpec Proof) (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) :
    shadowGame keccakPadding KState.zero (game2D P skel D s) =
      ((simulateQ HF.romImpl (proverJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s
        (skelRec skel))).run ∅ >>= fun w ↦ runS2 (D w.1.1) w.1.2 w.2) := by
  have hin : (simulateQ (shadowImpl keccakPadding)
      (simulateQ (hfEmbed (Msg := List UInt8)) (proverJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s
        skel) >>= fun pf ↦ simulateQ permD2 (simulateQ laneToByte (D pf)))).run'
        (SimState.init KState.zero) =
      (proverJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s (skelRec skel) >>= fun p ↦
        (simulateQ (simulator2 (Msg := List UInt8) keccakPadding)
          (simulateQ laneToByte (D p.1))).run' p.2) := by
    rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, ← QueryImpl.simulateQ_compose
      (shadowImpl keccakPadding) (hfEmbed (Msg := List UInt8)), recImpl_proverJ P hrow s skel,
      map_bind]
    simp only [← QueryImpl.simulateQ_compose, shadow_permD2_lanes, StateT.run'_eq]
  unfold shadowGame game2D
  rw [← run'_simulateQ_foldRO, hin]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-! ## From the random-permutation model to `zk_rom`'s games -/

/-- **The prover's permutation calls follow the duplex discipline** (`Common.Duplex`): each absorbs
a non-final block into the zero state or into an earlier permutation answer, keeping its capacity
(the overwrite duplex keeps lanes `16 .. 24`: `Common.keccakNF_blockTo`). -/
def DuplexDiscipline (skel : OracleComp DSpec Proof) : Prop :=
  ∀ s, Duplex KState.zero keccakNF (proverJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s skel) []

/-- **The real game in the random-oracle model, the distinguisher querying the permutation**:
`zk_rom`'s prover on `skelRec skel`, then `D` through `S₂` from the bookkeeping, `H` and `F` read
on `G`'s cache. -/
noncomputable def realGameS2 (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) : ProbComp Bool := do
  let s ← $ᵗ S
  let z ← prove P s (skelRec skel) []
  runS2 (D z.1.1) z.1.2 (hfOf z.2)

/-- **The real games, in the random-permutation model and in the random-oracle model, are
`Q² / 2^508`-close** (`transfer2_game`), for a real game of at most `Q` permutation calls on every
path whose prover follows the duplex discipline. -/
theorem realGameRpmD_close (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m)
    (skel : OracleComp DSpec Proof)
    (hduplex : DuplexDiscipline P skel)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (Q : ℕ)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpmD P skel D s) permutationCallCost Q) :
    Close (realGameRpmD P skel D) (realGameS2 P skel D) ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508) := by
  unfold realGameRpmD realGameS2
  refine Close.bind_const _ _ _ _ fun s ↦ ?_
  have hG : DuplexOK KState.zero keccakNF (game2D P skel D s) [] :=
    duplexOK_hfEmbed_bind keccakNF _ (fun pf h ↦ duplexOK_permD2 keccakNF _ h) _ [] (hduplex s)
  have hq2 : QueryCostAtMost (game2D P skel D s) (queryCost2 (Dg := DigestBytes) keccakPadding) Q := by
    apply isWeightBound_of_toOne
    rw [← relabel_gameHD, ← SufCma.permCallsB_eq]
    exact isWeightBound_relabel ((isWeightBound_expand_iff _ _).mp (by rw [expand_gameHD]; exact hQ s))
  obtain ⟨h1, h2⟩ := transfer2_game keccakPadding KState.zero keccakNF not_keccakNF_of_pad
    (game2D P skel D s) hG Q hq2 (· = true)
  have hb := keccak_indiffBound2_le Q
  have hL := runRpm_gameD P skel D s
  have hR : shadowGame keccakPadding KState.zero (game2D P skel D s) =ᵈ
      (prove P s (skelRec skel) [] >>= fun z ↦ runS2 (D z.1.1) z.1.2 (hfOf z.2)) := by
    rw [shadow_game2D P hrow s skel D]
    refine (EvalDistEq.bind_left (romImpl_proverHF P s (skelRec skel)) _).trans ?_
    rw [bind_map_left]
  constructor
  · rw [hL.prEvent_eq, ← hR.prEvent_eq]; exact h1.trans (add_le_add le_rfl hb)
  · rw [hL.prEvent_eq, ← hR.prEvent_eq]; exact h2.trans (add_le_add le_rfl hb)

/-- `D` through `S₂` reading a tape `t`, its `H` and `F` read on `G`: a coin-free distinguisher of
`G`. -/
noncomputable def throughTape2 (t : List KState)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (z : Proof × SimSt) :
    OracleComp (Inp →ₒ Out) Bool :=
  simulateQ enc ((simulateQ (simTape2 (Msg := List UInt8) keccakPadding)
    (simulateQ laneToByte (D z.1))).run' (z.2, t))

theorem runS2_tape (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (q : ℕ)
    (hD : ∀ pf, IsTotalQueryBound (D pf) q) (z : Proof × SimSt) (c : (Inp →ₒ Out).QueryCache) :
    runS2 (D z.1) z.2 (hfOf c) =ᵈ (uniformList KState q >>= fun t ↦
      (simulateQ randomOracle (throughTape2 t D z)).run' c) :=
  (simulator2_tape keccakPadding (simulateQ laneToByte (D z.1)) q
    (isTotalQueryBound_laneToByte _ q (hD z.1)) z.2 (hfOf c)).trans
    (EvalDistEq.bind_congr_of_support _ fun _ _ ↦ ro_enc _ c)

theorem isTotalQueryBound_throughTape2 (t : List KState)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (q : ℕ)
    (hD : ∀ pf, IsTotalQueryBound (D pf) q) (z : Proof × SimSt) :
    IsTotalQueryBound (throughTape2 t D z) q :=
  isTotalQueryBound_enc _ q (isTotalQueryBound_simTape2 keccakPadding _ q
    (isTotalQueryBound_laneToByte _ q (hD z.1)) _)

theorem realGameS2_tape (skel : OracleComp DSpec Proof)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool) (q : ℕ)
    (hD : ∀ pf, IsTotalQueryBound (D pf) q) :
    realGameS2 P skel D =ᵈ (uniformList KState q >>= fun t ↦
      QuotientZk.realGame P (skelRec skel) [] (throughTape2 t D)) := by
  unfold realGameS2 QuotientZk.realGame
  calc (($ᵗ S) >>= fun s ↦ prove P s (skelRec skel) [] >>= fun z ↦ runS2 (D z.1.1) z.1.2 (hfOf z.2))
      =ᵈ (($ᵗ S) >>= fun s ↦ prove P s (skelRec skel) [] >>= fun z ↦
          uniformList KState q >>= fun t ↦
            (simulateQ randomOracle (throughTape2 t D z.1)).run' z.2) :=
        EvalDistEq.bind_congr_of_support _ fun s _ ↦ EvalDistEq.bind_congr_of_support _
          fun z _ ↦ runS2_tape D q hD z.1 z.2
    _ =ᵈ (($ᵗ S) >>= fun s ↦ uniformList KState q >>= fun t ↦
          prove P s (skelRec skel) [] >>= fun z ↦
            (simulateQ randomOracle (throughTape2 t D z.1)).run' z.2) :=
        EvalDistEq.bind_congr_of_support _ fun s _ ↦ EvalDistEq.bind_bind_swap _ _ _
    _ =ᵈ _ := EvalDistEq.bind_bind_swap _ _ _

theorem simGameRpmD_tape (simV : List Out → ProbComp (View Msg Inp Tbl Pos))
    (skel : OracleComp DSpec Proof) (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (q : ℕ) (hD : ∀ pf, IsTotalQueryBound (D pf) q) :
    simGameRpmD P simV skel D =ᵈ (uniformList KState q >>= fun t ↦
      QuotientZk.simGame P simV (skelRec skel) [] (throughTape2 t D)) := by
  unfold simGameRpmD QuotientZk.simGame
  calc (sim P simV (skelRec skel) [] >>= fun z ↦ runS2 (D z.1.1) z.1.2 (hfOf z.2))
      =ᵈ (sim P simV (skelRec skel) [] >>= fun z ↦ uniformList KState q >>= fun t ↦
            (simulateQ randomOracle (throughTape2 t D z.1)).run' z.2) :=
        EvalDistEq.bind_congr_of_support _ fun z _ ↦ runS2_tape D q hD z.1 z.2
    _ =ᵈ _ := EvalDistEq.bind_bind_swap _ _ _

/-- The honest prover's Fiat–Shamir flag on the skeleton with its bookkeeping is the flag on the
skeleton. -/
theorem fs_skelRec (skel : OracleComp DSpec Proof) (s : S) :
    ((simulateQ (implReal P s) (skelRec skel)).run (St.init []) >>= fun z ↦ pure z.2.fs) =
      ((simulateQ (implReal P s) skel).run (St.init []) >>= fun z ↦ pure z.2.fs) := by
  rw [← run_recOps (implReal P s) skel (SimState.init KState.zero) (St.init []), bind_map_left]
  rfl

/-! ## The theorems -/

/-- **Zero knowledge in the random-permutation model, for any skeleton of the deployed oracle, the
honest-verifier simulator within `εz`** (`VClose`): `zk_rom_approx`'s bound on `skelRec skel` plus
`Q² / 2^508`. -/
theorem zk_rpm_skel_approx [Fintype (Tbl × Pos)] (skel : OracleComp DSpec Proof)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εFS εhv εz δ δ₂ : ℝ≥0∞) (QP QD Q : ℕ) (hQP : IsTotalQueryBound skel QP)
    (hFS : Deployed.FSFresh P skel [] εFS)
    (hzk : ∀ σ, good σ → VClose ((fun s ↦ P.view s σ) <$> ($ᵗ S)) (simV σ) εz)
    (hgood : Pr{let σ ← uniformList Out P.n}[¬ good σ] ≤ εhv)
    (hent : ∀ σ k x, P.opened σ k x = false → ∀ v y,
      Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = y] ≤
        δ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hent₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') → ∀ v,
        Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = P.rows s σ k' x'] ≤
          δ₂ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m)
    (hduplex : DuplexDiscipline P skel)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ pf, IsTotalQueryBound (D pf) QD)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpmD P skel D s) permutationCallCost Q) :
    Close (realGameRpmD P skel D) (simGameRpmD P simV skel D)
      (εFS + (εhv + εz) + ((Fintype.card (Tbl × Pos) * (QP + QD) : ℕ) * δ +
        (Fintype.card (Tbl × Pos) ^ 2 : ℕ) * δ₂) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) := by
  have hFS' : Deployed.FSFresh P (skelRec skel) [] εFS := by
    unfold Deployed.FSFresh at hFS ⊢
    rw [bind_congr (x := ($ᵗ S)) fun s ↦ fs_skelRec P skel s]
    exact hFS
  have hrom : ∀ t : List KState, Close (QuotientZk.realGame P (skelRec skel) [] (throughTape2 t D))
      (QuotientZk.simGame P simV (skelRec skel) [] (throughTape2 t D))
      (εFS + (εhv + εz) + ((Fintype.card (Tbl × Pos) * (QP + QD) : ℕ) * δ +
        (Fintype.card (Tbl × Pos) ^ 2 : ℕ) * δ₂)) := fun t ↦
    (zk_rom_approx P (skelRec skel) [] simV good εFS εhv εz δ δ₂ QP QD
      (isTotalQueryBound_skelRec skel QP hQP)
      hFS' hzk hgood hent hent₂ _ (isTotalQueryBound_throughTape2 t D QD hD)).mono
      (le_of_eq (by simp))
  have h := (realGameRpmD_close P hrow skel hduplex D Q hQ).trans
    ((Close.of_evalDistEq (realGameS2_tape P skel D QD hD)).trans
      ((Close.bind_const _ _ _ _ hrom).trans
        (Close.of_evalDistEq (simGameRpmD_tape P simV skel D QD hD).symm)))
  refine h.mono (le_of_eq ?_)
  simp only [zero_add, add_zero]
  rw [add_comm]

/-- **Zero knowledge in the random-permutation model, for any skeleton of the deployed oracle**:
`zk_rom`'s bound on `skelRec skel` plus `Q² / 2^508`. -/
theorem zk_rpm_skel [Fintype (Tbl × Pos)] (skel : OracleComp DSpec Proof)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εFS εhv δ δ₂ : ℝ≥0∞) (QP QD Q : ℕ) (hQP : IsTotalQueryBound skel QP)
    (hFS : Deployed.FSFresh P skel [] εFS)
    (hzk : ∀ σ, good σ → (fun s ↦ P.view s σ) <$> ($ᵗ S) =ᵈ simV σ)
    (hgood : Pr{let σ ← uniformList Out P.n}[¬ good σ] ≤ εhv)
    (hent : ∀ σ k x, P.opened σ k x = false → ∀ v y,
      Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = y] ≤
        δ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hent₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') → ∀ v,
        Pr{let s ← $ᵗ S}[P.view s σ = v ∧ P.rows s σ k x = P.rows s σ k' x'] ≤
          δ₂ * Pr{let s ← $ᵗ S}[P.view s σ = v])
    (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m)
    (hduplex : DuplexDiscipline P skel)
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ pf, IsTotalQueryBound (D pf) QD)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpmD P skel D s) permutationCallCost Q) :
    Close (realGameRpmD P skel D) (simGameRpmD P simV skel D)
      (εFS + εhv + ((Fintype.card (Tbl × Pos) * (QP + QD) : ℕ) * δ +
        (Fintype.card (Tbl × Pos) ^ 2 : ℕ) * δ₂) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) :=
  (zk_rpm_skel_approx P skel simV good εFS εhv 0 δ δ₂ QP QD Q hQP hFS
    (fun σ hσ ↦ VClose.of_evalDistEq (hzk σ hσ)) hgood hent hent₂ hrow hduplex D hD hQ).mono
    (le_of_eq (by rw [add_zero]))

end QuotientZk.DRpm
