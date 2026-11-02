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
    · change QueryCostAtMost (liftM (KSpecB.query (.inl n)) >>= fun u ↦ simulateQ (toOne (E := KRest) (C := KCap)) (k u)) _ q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inl m))) >>= fun u ↦ simulateQ (toOne (E := KRest) (C := KCap)) (k u)) _ q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inr qq))) >>= fun u ↦ simulateQ (toOne (E := KRest) (C := KCap)) (k u)) _ q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inr (.forward x)))) >>= fun u ↦ simulateQ (toOne (E := KRest) (C := KCap)) (k u)) _ q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩

end QuotientZk.DRpm
