-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the two calls and their random-permutation model, `rpmError`, the duplex
-- discipline `DuplexVm` and the block cost `hashBlocks`.
import E2ECompleteness.Chain
import E2ECompleteness.Transfer
import E2ECompleteness.Regular
import Completeness
import PcsQuotient.Security

/-!
# `PcsQuotient.Completeness`, from the staged two-call experiment

The end statement `PcsQuotient.Completeness δ` (`formal/Statement`, `Security.lean`) is about the
completeness experiment in one random permutation: the setup, uniform coins (masks and padding),
the Statement's honest `prover` and its `verifier`, all over `π`.

**What is proved here** (`completeness_of_staged`): if the experiment is, in distribution, the
coins then a two-call computation of the chain's shape (`Staged`, `Staged.Holds`: the code-level
bridge of the Statement's prover and verifier to the proof layers), then

  `δ = (17 · 2^24 + 8) / 2^192 + 2 / 2^256 + εpow + N² / 2^508`:

* `N² / 2^508` (`rpmError N`): the random permutation is two random oracles to an honest
  computation of at most `N` block calls following the duplex discipline (`rpm_le_rom`, mumbai's
  indifferentiability transfer);
* `(17 · 2^24 + 8) / 2^192 + 2 / 2^256`: the chain's challenges `(α, β, t)` fall in the
  degenerate set of `formal/Completeness` (`completeness_deployed_concrete`: at most a
  `(17 · 2^24 + 8) / 2^192` fraction of the triples, for the secret and the masks) with
  probability at most its density plus `2 / 2^256` (`prEvent_staged_le`: the challenge queries
  are fresh by their lengths but for two `2^-256` repetitions);
* `εpow`: the honest proof is rejected at non-degenerate challenges (`Staged.Holds.rejectGood`,
  in the two-call random-oracle model; `formal/Completeness`'s `completeness_deployed_concrete`
  says it is accepted for every hash and permutation when the proofs of work succeed, and
  `ours_romComplete` bounds a failed proof of work by `2^-277` per opening).

**`completeness_deployed`**: at `N = 2^48` block calls and `εpow = 3 · 2^-277`,
`δ < 2^-162` (`deltaDeployed_lt`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

/-! ## The degenerate challenges of a witness -/

/-- The Statement's secret as `formal/Completeness`'s (`Fin 32 → UInt8` bytes, `Fin 32` paths). -/
def secretOf (w : PcsQuotient.Secret) : Completeness.Secret where
  x i := w.x[i]
  siblings i j := (w.siblings.get ⟨i, by simp [PcsQuotient.depth]⟩)[j]
  directions i := w.directions.get ⟨i, by simp [PcsQuotient.depth]⟩

/-- The honest first message of a witness and masks on the deployed instance
(`formal/Completeness`'s `honestG`). -/
noncomputable def honestMsg (w : PcsQuotient.Secret) (m : PcsQuotient.Masks) :
    Fin 4 → Polynomial E :=
  Completeness.honestG QuotientSecurity.deployedBasis Completeness.deployedMembership (secretOf w) m

open Classical in
/-- **The degenerate challenges** of a witness and masks: `formal/Completeness`'s set
(`completeness_bad_set`'s, on the deployed instance): a denominator of the sum vanishes at a cell
(`BadAB`), or the Rust's check fails at `t` (`Degenerate`). Outside it the honest proof is accepted
for every hash function and permutation whenever its proofs of work succeed
(`completeness_deployed_concrete`). -/
noncomputable def badSet (w : PcsQuotient.Secret) (m : PcsQuotient.Masks) : Finset (E × E × E) :=
  Finset.univ.filter fun z : E × E × E ↦
    Completeness.Reduction.BadAB Completeness.deployedInstanceE (honestMsg w m) z.1 z.2.1 ∨
      Completeness.Reduction.Degenerate Completeness.deployedInstanceE (honestMsg w m) z.1 z.2.1
        z.2.2

theorem badSet_density (w : PcsQuotient.Secret) (m : PcsQuotient.Masks) :
    ((badSet w m).card : ℝ≥0∞) / 2 ^ 576 ≤ (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 := by
  have h := Completeness.Reduction.bad_fraction_le Completeness.deployedInstanceE
    LeanVM.Protocol.card_E (honestMsg w m) fun j ↦
      (Completeness.natDegree_witnessOfTable_le (algebraMap K E) QuotientSecurity.deployedBasis
        (Completeness.cellBitsK Completeness.deployedMembership (secretOf w)) m j).trans
        (by norm_num)
  have hc : (Fintype.card (E × E × E) : ℝ≥0∞) = 2 ^ 576 := by
    rw [Fintype.card_prod, Fintype.card_prod, LeanVM.Protocol.card_E, ← pow_add, ← pow_add,
      Nat.cast_pow, Nat.cast_ofNat]
  calc ((badSet w m).card : ℝ≥0∞) / 2 ^ 576
      = ((badSet w m).card : ℝ≥0∞) / (Fintype.card (E × E × E) : ℝ≥0∞) := by rw [hc]
    _ ≤ _ := h

/-! ## The staged experiment -/

/-- **The experiment's stages**: the coins (with their masks), and, for each draw, the honest run
of the setup, the prover and the verifier as a two-call computation of the chain's shape
(`staged`): `A` up to the seeded chain state and the witness root (the setup's tree, the index
tree, the witness tree, the label's hash), `B` from `α, β, γ` to the quotient root (the quotient
tree), `C` the rest (`t`'s chain, the values, `ρ`, the three openings, the verifier), its output
the verdict. -/
structure Staged where
  Coins : Type
  α : Type
  β : Type
  coins : ProbComp Coins
  masks : Coins → PcsQuotient.Masks
  A : Coins → OracleComp KeccakCalls (α × Digest × (E × E))
  B : Coins → α → Digest → Digest → Digest → OracleComp KeccakCalls (β × (E × E))
  C : Coins → α → β → Digest → Digest → Digest → Digest → OracleComp KeccakCalls Bool

/-- The two-call run of a draw: the chain's challenges `(α, β, t)` the transcript's
(`challengeOf`). -/
def Staged.run (S : Staged) (c : S.Coins) : OracleComp KeccakCalls (Bool × (E × E × E)) :=
  staged PcsQuotient.Transcript.challengeOf (S.A c) (S.B c) (S.C c)

/-- **The code-level bridge** of the Statement's experiment for `(stmt, w)`, at `N` block calls and
a proof-of-work error `εpow`. -/
structure Staged.Holds (S : Staged) (stmt : PcsQuotient.Statement) (w : PcsQuotient.Secret)
    (N : ℕ) (εpow : ℝ≥0∞) : Prop where
  /-- The experiment is the coins, then the two-call run against the random permutation. -/
  experiment : PcsQuotient.completenessExperiment stmt w =ᵈ
    (S.coins >>= fun c ↦ (fun z ↦ z.1) <$>
      (simulateQ keccakCallsOverRandomPermutation (S.run c)).run' [])
  /-- Every permutation call continues a duplex or starts one (`DuplexVm`). -/
  duplex : ∀ c, DuplexVm (S.run c) []
  /-- At most `N` block calls (`hashBlocks`). -/
  cost : ∀ c, Common.QueryCostAtMost (S.run c) hashBlocks N
  /-- Before `α`, nothing of the chain's lengths is hashed (512-byte leaves, 64-byte nodes, the
  112-byte label). -/
  hashA : ∀ c, HashOK Good (S.A c)
  /-- Between `γ` and `t`, the same (the quotient tree). -/
  hashB : ∀ c a s₁ s₂ s₃, HashOK Good (S.B c a s₁ s₂ s₃)
  /-- **Grinding**: in the two-call random-oracle model the honest proof is rejected at
  non-degenerate challenges with probability at most `εpow`. -/
  rejectGood : ∀ c,
    Pr{let z ← (simulateQ ro (S.run c)).run' ∅}[z.1 = false ∧ z.2 ∉ badSet w (S.masks c)] ≤ εpow

/-! ## The bound -/

/-- **One draw of the coins**: the run is rejected with probability at most the degenerate
challenges' density, `2 / 2^256`, `εpow` and the transfer's `rpmError N`. -/
theorem prEvent_run_false_le (S : Staged)
    {stmt : PcsQuotient.Statement} {w : PcsQuotient.Secret} {N : ℕ} {εpow : ℝ≥0∞}
    (h : S.Holds stmt w N εpow) (c : S.Coins) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation (S.run c)).run' []}[z.1 = false] ≤
      ((17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 + 2 / 2 ^ 256 + εpow) + rpmError N := by
  refine rpm_le_rom (S.run c) (h.duplex c) (h.cost c) (fun z ↦ z.1 = false) ?_
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _
    (fun z : Bool × (E × E × E) ↦ z.2 ∈ badSet w (S.masks c))).trans ?_
  refine add_le_add ?_ (h.rejectGood c)
  have hc : Pr{let z ← (simulateQ ro (S.run c)).run' ∅}[z.2 ∈ badSet w (S.masks c)] =
      Pr{let z ← (simulateQ ro (S.run c)).run ∅}[z.1.2 ∈ badSet w (S.masks c)] := by
    rw [StateT.run'_eq, prEvent_map]
  rw [hc]
  refine (prEvent_staged_le _ challengeOf_regular _ _ _ _ (h.hashA c) (h.hashB c) ∅ fun m hm ↦
    absurd rfl hm).trans ?_
  rw [add_comm]
  exact add_le_add (badSet_density w (S.masks c)) le_rfl

/-- **Completeness in the random-permutation model, from the staged experiment.** -/
theorem completeness_of_staged {N : ℕ}
    {εpow : ℝ≥0∞}
    (hS : ∀ stmt w, PcsQuotient.Relation stmt w → ∃ S : Staged, S.Holds stmt w N εpow) :
    PcsQuotient.Completeness
      ((17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 + 2 / 2 ^ 256 + εpow + rpmError N) := by
  intro stmt w hrel
  obtain ⟨S, h⟩ := hS stmt w hrel
  rw [h.experiment.prEvent_eq]
  refine prEvent_bind_le_of_forall_le _ _ _ fun c ↦ ?_
  rw [prEvent_map]
  exact prEvent_run_false_le S h c

/-! ## The numbers -/

/-- **The deployed bound**: `N = 2^48` block calls (the setup's, the prover's with `2^25` nonces
per proof of work, and the verifier's, far fewer), `εpow = 3 · 2^-277`. -/
noncomputable def deltaDeployed : ℝ≥0∞ :=
  (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 + 2 / 2 ^ 256 + 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 +
    rpmError (2 ^ 48)

/-- `2^k · 2^-(n + k) = 2^-n`. -/
theorem two_pow_mul_inv_pow (k n : ℕ) : (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ (n + k) =
    (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [pow_add, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ n), ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

theorem inv_pow_le_inv_pow {m n : ℕ} (h : m ≤ n) : (2 : ℝ≥0∞)⁻¹ ^ n ≤ (2 : ℝ≥0∞)⁻¹ ^ m :=
  pow_le_pow_of_le_one (by simp) (by simp) h

theorem deltaDeployed_lt : deltaDeployed < (2 : ℝ≥0∞)⁻¹ ^ 162 := by
  have h1 : (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 < (2 : ℝ≥0∞)⁻¹ ^ 163 :=
    Completeness.Reduction.bad_bound_lt
  have h2 : (2 : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 := by
    calc (2 : ℝ≥0∞) / 2 ^ 256 = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (255 + 1) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm, pow_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 255 := two_pow_mul_inv_pow 1 255
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 := inv_pow_le_inv_pow (by norm_num)
  have h3 : 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 := by
    calc 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 ≤ 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (275 + 2) := by
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 275 := two_pow_mul_inv_pow 2 275
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 := inv_pow_le_inv_pow (by norm_num)
  have h4 : rpmError (2 ^ 48) ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 := by
    calc rpmError (2 ^ 48) = 2 ^ (48 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (412 + 48 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul,
            ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 412 := two_pow_mul_inv_pow _ 412
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 := inv_pow_le_inv_pow (by norm_num)
  have hrest : 2 / 2 ^ 256 + 3 * (2 : ℝ≥0∞)⁻¹ ^ 277 + rpmError (2 ^ 48) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 163 := by
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 + (2 : ℝ≥0∞)⁻¹ ^ 165 + (2 : ℝ≥0∞)⁻¹ ^ 165 :=
          add_le_add (add_le_add h2 h3) h4
      _ ≤ 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (163 + 2) := by
          have : (2 : ℝ≥0∞)⁻¹ ^ 165 + (2 : ℝ≥0∞)⁻¹ ^ 165 + (2 : ℝ≥0∞)⁻¹ ^ 165 =
              3 * (2 : ℝ≥0∞)⁻¹ ^ (163 + 2) := by ring
          rw [this]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 163 := two_pow_mul_inv_pow 2 163
  have e2 : (2 : ℝ≥0∞)⁻¹ ^ 163 + (2 : ℝ≥0∞)⁻¹ ^ 163 = (2 : ℝ≥0∞)⁻¹ ^ 162 := by
    calc (2 : ℝ≥0∞)⁻¹ ^ 163 + (2 : ℝ≥0∞)⁻¹ ^ 163 = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (162 + 1) := by
          rw [← two_mul, pow_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 162 := two_pow_mul_inv_pow 1 162
  have hrest' : 2 / 2 ^ 256 + (3 * (2 : ℝ≥0∞)⁻¹ ^ 277 + rpmError (2 ^ 48)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 163 := by rwa [← add_assoc]
  unfold deltaDeployed
  rw [add_assoc, add_assoc, ← e2]
  exact ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top (by simp) hrest') h1 hrest'

/-- **`PcsQuotient.Completeness` at the deployed bound**, from the staged experiment at `2^48`
block calls and a proof-of-work error of `3 · 2^-277`. -/
theorem completeness_deployed
    (hS : ∀ stmt w, PcsQuotient.Relation stmt w →
      ∃ S : Staged, S.Holds stmt w (2 ^ 48) (3 * (2 : ℝ≥0∞)⁻¹ ^ 277)) :
    PcsQuotient.Completeness deltaDeployed :=
  completeness_of_staged hS

end E2ECompleteness
