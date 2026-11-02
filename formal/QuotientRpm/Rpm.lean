-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The derandomization (`exists_det_of`, `stepCache`, `snd_eq_stepCache`) is adapted from leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0),
-- `lean_vm/LeanVM/Protocol/Rpm/Coins.lean`; the transfer is `common`'s (`Common.keccak256_transfer`,
-- `Common.runK_expand`, `Common.runK_relabel`), applied as `common/Common/Signature.lean` applies it.
import QuotientRpm.ChainRom
import QuotientSecurity.Statement
import Common.PiOnly
import Common.Rerun

/-!
# Knowledge soundness with the Keccak-256 chain, in the random-permutation model

leanerVM's model (`Statement/RandomPermutation.lean`): one uniformly random permutation `π` of the
Keccak-f[1600] state, queried forward and inverse; Keccak-256 is the sponge over `π`
(`Common.keccak256OverPermutation`). The adversary has coins, `π` and `π⁻¹`
(`Common.RandomPermutationOracles`); the verifier hashes with Keccak-256 over the same `π`
(`rpmExperiment`). The commitments are ideal, as in `Chain.lean`.

The proof moves the game to the random-oracle model with `common`'s indifferentiability of the
sponge: the game read with a Keccak-256 oracle (`Common.runK_expand`), its permutation queries on
bytes (`Common.runK_relabel`), then `Common.keccak256_transfer` (`Q² / 2^509` for `Q` permutation
calls in all). There the adversary is `Common.advS` of the adversary, with coins of the
simulator's; coins do not help against a lazily sampled oracle (`exists_det`, leanerVM's
derandomization), and the coin-free adversary makes at most as many hash queries as the original
made calls (`Common.SufCma.isWeightBound_idealImpl`). `knowledgeSoundness_chain` bounds it.

**`knowledgeSoundness_rpm`**: if the whole game (the adversary and the verifier's hashing) makes
at most `Q` calls of `π` and `π⁻¹` on every path, the verifier accepts a proof whose cells do not
satisfy the relation with probability at most
`(Q + 8) (roundError + 3 (Q + 8) / 2^256) + Q² / 2^509`; at the sizes of `quotient::protocol`,
`(Q + 8) (2^-128 + 3 (Q + 8) / 2^256) + Q² / 2^509` (`knowledgeSoundness_rpm_bits`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace QuotientRpm

open QuotientSecurity

/-! ## The verifier through a simulation -/

section Simulate

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B)

/-- The verifier commutes with a simulation of its hash. -/
theorem simulateQ_verifyWith {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) (H : List UInt8 → OracleComp spec Bytes32)
    (π : ChainProof P B) :
    simulateQ impl (W.verifyWith H π) = W.verifyWith (fun x => simulateQ impl (H x)) π := by
  simp only [Wire.verifyWith, simulateQ_bind, simulateQ_pure]

end Simulate

/-! ## Coins do not help against a lazily sampled oracle -/

section Coins

/-- The cache after a random-oracle step answering `u` at `t` from `c`. -/
def stepCache (c : HashSpec.QueryCache) (t : List UInt8) (u : Bytes32) : HashSpec.QueryCache :=
  match c t with
  | some _ => c
  | none => c.cacheQuery t u

theorem snd_eq_stepCache {c : HashSpec.QueryCache} {t : List UInt8}
    {z : Bytes32 × HashSpec.QueryCache} (hz : z ∈ support ((HashSpec.randomOracle t).run c)) :
    z.2 = stepCache c t z.1 := by
  rw [randomOracle.run_eq] at hz
  unfold stepCache
  cases h : c t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    rfl

/-- **Derandomization**, for a stateful oracle that answers a coin uniformly, the state unchanged,
and a query with a new state that the old state, the query and the answer determine (`next`): an
adversary with coins does no better than some deterministic adversary of the same query budget,
coins not counted, for any continuation and any event. At a coin, the best of the finitely many
continuations; at an oracle query, the query followed by the best continuation at each answer. -/
theorem exists_det_of {ι σ α γ : Type} {spec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl (unifSpec + spec) (StateT σ ProbComp)) (next : σ → (t : ι) → spec t → σ)
    (hcoin : ∀ n s, ∀ z ∈ support ((impl (.inl n)).run s), z.2 = s)
    (hnext : ∀ t s, ∀ z ∈ support ((impl (.inr t)).run s), z.2 = next s t z.1)
    (w : (unifSpec + spec).Domain → ℕ) (hw0 : ∀ n, w (.inl n) = 0) (hw1 : ∀ t, w (.inr t) = 1)
    (g : α × σ → ProbComp γ) (E : γ → Prop) (X : OracleComp (unifSpec + spec) α) :
    ∀ (Q : ℕ), Common.QueryCostAtMost X w Q → ∀ s : σ,
      ∃ A : OracleComp spec α, IsTotalQueryBound A Q ∧
        Pr{let y ← (simulateQ impl X).run s >>= g}[E y] ≤
          Pr{let y ← (simulateQ (fun t ↦ impl (.inr t)) A).run s >>= g}[E y] := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro Q _ s
    exact ⟨pure a, trivial, by simp⟩
  | query_bind t k ih =>
    intro Q hX s
    rw [Common.isWeightBound_query_bind_iff] at hX
    obtain ⟨ht, hk⟩ := hX
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
    rcases t with n | t
    · have hk' : ∀ u, Common.QueryCostAtMost (k u) w Q := fun u ↦ by
        simpa [hw0] using hk u
      choose A hA hle using fun u ↦ ih u Q (hk' u) s
      let f : Fin (n + 1) → ℝ≥0∞ := fun u ↦
        Pr{let y ← (simulateQ (fun t ↦ impl (.inr t)) (A u)).run s >>= g}[E y]
      obtain ⟨u₀, hu₀⟩ := Finite.exists_max f
      refine ⟨A u₀, hA u₀, ?_⟩
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz ↦ ?_
      rw [hcoin n s z hz]
      exact (hle z.1).trans (hu₀ z.1)
    · have hQ : 1 ≤ Q := hw1 t ▸ ht
      have hk' : ∀ u, Common.QueryCostAtMost (k u) w (Q - 1) := fun u ↦ hw1 t ▸ hk u
      choose A hA hle using fun u ↦ ih u (Q - 1) (hk' u) (next s t u)
      refine ⟨liftM (spec.query t) >>= A, ?_, ?_⟩
      · exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, hA⟩
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
        refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun z hz ↦ ?_
        rw [hnext t s z hz]
        exact hle z.1

theorem romImpl_inl_run (n : ℕ) (c : HashSpec.QueryCache) :
    (HashSpec.romImpl (.inl n)).run c = (fun x => (x, c)) <$> (unifSpec.query n : ProbComp _) := by
  simp [unifFwdImpl]

/-- **Derandomization against the random oracle on bytes.** -/
theorem exists_det {α γ : Type} (g : α × HashSpec.QueryCache → ProbComp γ) (E : γ → Prop)
    (X : OracleComp (unifSpec + HashSpec) α) :
    ∀ (Q : ℕ), Common.QueryCostAtMost X Common.SufCma.romCalls Q → ∀ c : HashSpec.QueryCache,
      ∃ A : OracleComp HashSpec α, IsTotalQueryBound A Q ∧
        Pr{let y ← (simulateQ HashSpec.romImpl X).run c >>= g}[E y] ≤
          Pr{let y ← (simulateQ HashSpec.randomOracle A).run c >>= g}[E y] :=
  exists_det_of HashSpec.romImpl stepCache
    (fun n c z hz ↦ by
      rw [romImpl_inl_run, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      rfl)
    (fun _ _ _ hz ↦ snd_eq_stepCache hz) Common.SufCma.romCalls (fun _ ↦ rfl) (fun _ ↦ rfl) g E X

end Coins

/-! ## The random-oracle game of the transfer -/

section Rom

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B)

/-- A hash query in the transfer's random-oracle model (coins and the hash). -/
def hashR (m : List UInt8) : OracleComp Common.SufCma.KRom Bytes32 :=
  liftM (Common.SufCma.KRom.query (.inr m))

/-- The verifier in the transfer's random-oracle model. -/
noncomputable def postR (π : ChainProof P B) :
    OracleComp Common.SufCma.KRom (ChainProof P B × Bool) :=
  W.verifyWith hashR π >>= fun b => pure (π, b)

theorem simulateQ_romImpl_postR (π : ChainProof P B) :
    simulateQ HashSpec.romImpl (postR W π) =
      simulateQ HashSpec.randomOracle (W.verifyWith hashQuery π >>= fun b => pure (π, b)) := by
  simp only [postR, simulateQ_bind, simulateQ_pure, simulateQ_verifyWith, hashR, hashQuery,
    simulateQ_spec_query]
  rfl

/-- **Knowledge soundness against an adversary with coins**, in the random-oracle model of the
transfer: at most `Q` hash queries (coins free) on every path. -/
theorem knowledgeSoundness_chain_coins (A : OracleComp Common.SufCma.KRom (ChainProof P B)) (Q : ℕ)
    (hA : Common.QueryCostAtMost A Common.SufCma.romCalls Q) :
    Pr{let r ← Common.romRun (A >>= postR W)}[Wins W r] ≤
      ((Q + 8 : ℕ) : ℝ≥0∞) * ((roundError P B : ℝ≥0∞) + 3 * ((Q + 8 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hrun : Common.romRun (A >>= postR W) = (simulateQ HashSpec.romImpl A).run ∅ >>=
      fun z => (simulateQ HashSpec.romImpl (postR W z.1)).run' z.2 := by
    simp only [Common.romRun, StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [hrun]
  obtain ⟨A₀, hA₀, hle⟩ := exists_det (fun z => (simulateQ HashSpec.romImpl (postR W z.1)).run' z.2)
    (Wins W) A Q hA ∅
  refine hle.trans (le_of_eq_of_le ?_ (knowledgeSoundness_chain W A₀ Q hA₀))
  have hexp : (simulateQ HashSpec.randomOracle A₀).run ∅ >>=
      (fun z => (simulateQ HashSpec.romImpl (postR W z.1)).run' z.2) =
      (simulateQ randomOracle (chainExperiment W A₀)).run' ∅ := by
    simp only [simulateQ_romImpl_postR, chainExperiment, StateT.run'_eq, simulateQ_bind,
      StateT.run_bind, map_bind]
  rw [hexp]

end Rom

/-! ## The random-permutation model -/

section Rpm

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B)

/-- **The experiment in the random-permutation model** (`Statement/RandomPermutation.lean`): the
adversary, with coins, `π` and `π⁻¹`, outputs a statement and a proof; the verifier hashes with
Keccak-256 over the same `π`. -/
noncomputable def rpmExperiment (A : OracleComp Common.RandomPermutationOracles (ChainProof P B)) :
    OracleComp Common.RandomPermutationOracles (ChainProof P B × Bool) :=
  A >>= fun π => W.verifyWith Common.keccak256OverPermutation π >>= fun b => pure (π, b)

/-- A Keccak-256 query, in the model with a hash oracle (`Common.KSpecH`). -/
def hashH (m : List UInt8) : OracleComp Common.KSpecH Bytes32 :=
  liftM (Common.KSpecH.query (.inr (.inl m)))

/-- The experiment with a Keccak-256 oracle. -/
noncomputable def gameH (A : OracleComp Common.RandomPermutationOracles (ChainProof P B)) :
    OracleComp Common.KSpecH (ChainProof P B × Bool) :=
  simulateQ Common.embed A >>= fun π => W.verifyWith hashH π >>= fun b => pure (π, b)

/-- The experiment is the game with the Keccak-256 oracle, each hash expanded into its
permutation calls. -/
theorem expand_gameH (A : OracleComp Common.RandomPermutationOracles (ChainProof P B)) :
    simulateQ Common.expand (gameH W A) = rpmExperiment W A := by
  simp only [gameH, rpmExperiment, simulateQ_bind, Common.simulateQ_expand_embed,
    simulateQ_verifyWith, simulateQ_pure, hashH, simulateQ_spec_query]
  rfl

/-- The game with its permutation queries on bytes is a game of the transfer's shape: no honest
part before, the adversary read on bytes, the verifier after. -/
theorem relabel_gameH (A : OracleComp Common.RandomPermutationOracles (ChainProof P B)) :
    simulateQ Common.relabel (gameH W A) =
      Common.rpmGame (pure ()) (fun _ => simulateQ Common.relabel (simulateQ Common.embed A))
        (fun _ π => postR W π) := by
  simp only [gameH, Common.rpmGame, Common.liftH, postR, simulateQ_bind, simulateQ_pure,
    simulateQ_verifyWith, hashH, hashR, simulateQ_spec_query, pure_bind]
  rfl

/-- **Knowledge soundness with the deployed transcript, in the random-permutation model.** For
every adversary (coins, `π`, `π⁻¹`) whose experiment, the verifier's Keccak-256 hashing included,
makes at most `Q` calls of `π` and `π⁻¹` on every path: the verifier accepts its proof while the
cells read off the proof's first message do not satisfy the relation for the statement its bytes
stand for, with probability at most `(Q + 8) (roundError + 3 (Q + 8) / 2^256) + Q² / 2^509`.
The commitments are ideal (`Chain.lean`). -/
theorem knowledgeSoundness_rpm (A : OracleComp Common.RandomPermutationOracles (ChainProof P B))
    (Q : ℕ) (hQ : Common.QueryCostAtMost (rpmExperiment W A) Common.permutationCallCost Q) :
    Pr{let r ← Common.runWithRandomPermutation (rpmExperiment W A)}[Wins W r] ≤
      ((Q + 8 : ℕ) : ℝ≥0∞) * ((roundError P B : ℝ≥0∞) + 3 * ((Q + 8 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        (Q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
  set A' := simulateQ Common.relabel (simulateQ Common.embed A)
  -- The game with a Keccak-256 oracle, then on bytes.
  have hQH : Common.QueryCostAtMost (gameH W A) Common.permCallsH Q :=
    (Common.isWeightBound_expand_iff _ _).mp (by rwa [expand_gameH])
  have hQB0 := Common.isWeightBound_relabel hQH
  have hQB : Common.QueryCostAtMost (Common.rpmGame (pure ()) (fun _ => A') (fun _ π => postR W π))
      (Common.queryCost (Dg := Common.DigestBytes) Common.keccakPadding) Q := by
    rw [← Common.SufCma.permCallsB_eq, ← relabel_gameH]
    exact hQB0
  rw [← expand_gameH, Common.runK_expand, (Common.runK_relabel (gameH W A)).prEvent_eq,
    relabel_gameH]
  obtain ⟨ht, -⟩ := Common.keccak256_transfer (pure ()) (fun _ => A') (fun _ π => postR W π) Q hQB
    (Wins W)
  refine ht.trans (add_le_add ?_ le_rfl)
  -- The random-oracle side: the adversary with the simulator, at most `Q` hash queries.
  have hA' : Common.QueryCostAtMost A' Common.SufCma.oracleCallsB Q := by
    rw [gameH, simulateQ_bind] at hQB0
    exact (Common.QueryCostAtMost.of_bind hQB0).mono_weight Common.SufCma.oracleCallsB_le_permCallsB
  have hadv : Common.QueryCostAtMost (Common.advS Common.keccakPadding Common.KState.zero A')
      Common.SufCma.romCalls Q := by
    unfold Common.advS
    rw [StateT.run'_eq]
    exact Common.isWeightBound_map _ (Common.isWeightBound_run_simulateQ _ _ _
      (fun t s => Common.SufCma.isWeightBound_idealImpl t s) hA' _)
  simp only [pure_bind]
  exact knowledgeSoundness_chain_coins W _ Q hadv

theorem div_le_two_pow' {a q k : ℕ} (hq : 0 < q) (h : a * 2 ^ k ≤ q) :
    ((a : ℝ≥0) / (q : ℝ≥0)) ≤ 1 / 2 ^ k := by
  have hq' : (0 : ℝ≥0) < (q : ℝ≥0) := by exact_mod_cast hq
  rw [div_le_div_iff₀ hq' (by positivity), one_mul]
  exact_mod_cast h

/-- At the sizes of `quotient::protocol` (a field of `2^192` elements, `2^24` cells, eight
words, identities of degree at most `2^29`), every round's error is at most `2^-163`: the copy
argument's `(4 N + 8) / q`, the identities' `2^29 / q`, the last `3 / q`. -/
theorem roundError_le (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24) (hw : P.words = 8)
    (hd : B.identity ≤ 2 ^ 29) : roundError P B ≤ 1 / 2 ^ 163 := by
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have key : ∀ a : ℕ, a ≤ 2 ^ 29 → ((a : ℝ≥0) / (Fintype.card F : ℝ≥0)) ≤ 1 / 2 ^ 163 :=
    fun a ha => div_le_two_pow' hpos (by
      rw [hq]
      calc a * 2 ^ 163 ≤ 2 ^ 29 * 2 ^ 163 := Nat.mul_le_mul_right _ ha
        _ = 2 ^ 192 := by norm_num)
  unfold roundError
  exact max_le (max_le (key _ (by rw [hN, hw]; norm_num)) (key _ hd)) (key _ (by norm_num))

/-- **At the sizes of `quotient::protocol`**: `(Q + 8) (2^-163 + 3 (Q + 8) / 2^256) + Q² / 2^509`
for `Q` permutation calls in all. -/
theorem knowledgeSoundness_rpm_bits (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 29)
    (A : OracleComp Common.RandomPermutationOracles (ChainProof P B)) (Q : ℕ)
    (hQ : Common.QueryCostAtMost (rpmExperiment W A) Common.permutationCallCost Q) :
    Pr{let r ← Common.runWithRandomPermutation (rpmExperiment W A)}[Wins W r] ≤
      ((Q + 8 : ℕ) : ℝ≥0∞) * (1 / 2 ^ 163 + 3 * ((Q + 8 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        (Q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
  refine (knowledgeSoundness_rpm W A Q hQ).trans ?_
  gcongr
  have h := roundError_le (P := P) (B := B) hq hN hw hd
  have : ((roundError P B : ℝ≥0) : ℝ≥0∞) ≤ ((1 / 2 ^ 163 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast h
  refine this.trans (le_of_eq ?_)
  push_cast
  rfl

end Rpm

/-! ## For a circuit -/

section Instance

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]

/-- **Knowledge soundness of `quotient::protocol` with its Keccak-256 chain, in the
random-permutation model**, for every circuit (`Instance`, `Setup.lean`) and every way the chain
reads its statement, field elements and messages (`Wire`): for every adversary (coins, `π`,
`π⁻¹`) whose experiment, the verifier's hashing included, makes at most `Q` calls of `π` and
`π⁻¹` on every path, the probability that the verifier accepts while the cells of the proof's
first message do not satisfy the circuit's relation for the statement its bytes stand for is at
most `(Q + 8) (2^-163 + 3 (Q + 8) / 2^256) + Q² / 2^509`. -/
theorem Instance.soundness_rpm (I : Instance F) (hq : Fintype.card F = 2 ^ 192)
    (W : Wire I.params I.bounds)
    (A : OracleComp Common.RandomPermutationOracles (ChainProof I.params I.bounds)) (Q : ℕ)
    (hQ : Common.QueryCostAtMost (rpmExperiment W A) Common.permutationCallCost Q) :
    Pr{let r ← Common.runWithRandomPermutation (rpmExperiment W A)}[
        r.2 = true ∧ ¬ I.Relation (W.decode r.1.stmt) (I.cellsOf r.1.g.1)] ≤
      ((Q + 8 : ℕ) : ℝ≥0∞) * (1 / 2 ^ 163 + 3 * ((Q + 8 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        (Q ^ 2 : ℝ≥0∞) / 2 ^ 509 := by
  have hid : I.bounds.identity ≤ 2 ^ 29 :=
    Params.ofCantor_identity I.basis le24 I.wiring _ _ I.pub_hPub
      (natDegree_membershipPub_le _ I.c)
  refine le_trans (prEvent_mono _ _ _ fun r hr =>
    ⟨hr.1, fun hsat => hr.2 (I.relation_of_sat _ _ hsat)⟩)
    (knowledgeSoundness_rpm_bits W hq I.nCells rfl hid A Q hQ)

end Instance

end QuotientRpm
