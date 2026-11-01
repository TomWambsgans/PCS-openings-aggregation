/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

Fiat-Shamir soundness, in the random-oracle model, of the opening check with leanVM's transcript
shape, from leanerVM `mumbai`'s random-oracle theorem (`Compile.Rom.romSound`). The construction
(the program, its specification and certificate, the seeding, the cost and the doom after the
root) is adapted from mumbai's assembly of leanVM's verifier
(https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0:
`lean_vm/LeanVM/Protocol/EndToEnd/Sound/{Assemble,Theorem,Statements}.lean`,
`lean_vm/LeanVM/Protocol/Verifier/Cost.lean`).
-/
import WhirBridge.Table
import LeanVM.Protocol.EndToEnd.Sound.Assemble
import LeanVM.Protocol.EndToEnd.Sound.Runs
import LeanVM.Protocol.Verifier.Cost
import LeanVM.Protocol.Compile.Rom.Sound

/-!
# The opening with leanVM's transcript shape

mumbai's random-oracle theorem covers a verifier program whose commitments are **read from the
proof** (`Prog.commit`: the root's two halves absorbed into the duplex, `verifier.py`'s
`Digest.from_halves(*next_scalars(2))`), run from a seed of hash steps and one permutation whose
root history has no commitment (`Compile.Rom.RootOk`). `opening.rs` instead hashes the root, with
the claims, into the seed's public-input digest and never absorbs it (`Gaps.lean`). This file
proves the theorem for the opening **with mumbai's shape**:

* `variantProg L R claims`: read the stack's root as commitment `0` (`commitStack`, as leanVM's
  `verify_execution` does), then `openingCheck L R claims`, then accept;
* `fixedSeeds label D`: the seed `F(H(label) ‖ D ‖ 0)`, for a fixed statement (a family of one):
  any label and any public digest `D`, for instance `keccak256(claims)` computed outside the
  model.

`variant_sound`: for an adversary making at most `QA` queries to Keccak-256 and Keccak-f[1600]
(independent random oracles), the verifier accepts while **every candidate of the root's word
extracted from the oracle's answers** (the straight-line extraction of mumbai's
`Compile.Rom.extractedHistory`) has a table violating one of the claims, with probability at most
`(QA + QV) · (2^-128 + 5 (QA + QV) / 2^256)`, `QV = variantQueries = 10122`.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Sound (commitSpec commitSpec_D MovesOK movesOK_commitStack
  movesOK_verifyStackedOpening queryGrindingBits_le retSplit_eq_none_of_after after_bind_ret
  commitStack_after_ret)
open LeanVM.Semantics LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The program and its certificate -/

/-- **The opening with leanVM's transcript shape**: the stack's root read as commitment `0`, then
the opening check, then accept. -/
def variantProg (L : Layout) (R : ℕ) (claims : List Claim) : Prog Bool := do
  commitStack L.logN R
  openingCheck L R claims
  return true

theorem after_nil' {α : Type} (p : Prog α) : p.after [] = some p := by
  cases p <;> rfl

theorem commitStack_ne_ret (logN R : ℕ) (a : Unit) : commitStack logN R ≠ .ret a := by
  intro h
  unfold commitStack at h
  rcases hl : Whir.ladder logN R with _ | ⟨_ | ⟨level, rest⟩⟩ <;> rw [hl] at h <;>
    simp [Verifier.liftOption, Prog.bind, Prog.readCommitment] at h

/-! ## The seed -/

/-- The seeding of a fixed statement: the IV `H(label)`, then the permutation of the IV and the
public digest `D` (`Transcript::new(proof, iv, D, true)`). -/
def fixedSeed (label : Bytes) (D : Digest) : Seed where
  hs := [fun _ ↦ label]
  fin ds := seedInput (ds.getD 0 default) D

/-- **A fixed statement's seedings**, a family of one, rooted at the empty history. -/
def fixedSeeds (label : Bytes) (D : Digest) : Seeds Unit where
  seed _ := fixedSeed label D
  root _ := []
  offs := []
  refs x ds hds i hi := by
    have hl : (fixedSeed label D).hs.length = 1 := rfl
    rw [hl] at hds
    have hd0 : ds.getD 0 default = ds[0] := by simp [List.getD_eq_getElem?_getD, hds]
    rw [hds] at hi
    interval_cases i
    left
    show laneDigest (seedInput (ds.getD 0 default) D) = ds[0]
    rw [laneDigest_seedInput, hd0]
  cap0 x ds := capOf_seedInput _ _
  inj _ _ _ _ _ _ _ _ _ := Subsingleton.elim _ _

variable (L : Layout) (R : ℕ) (hw : Whir.Admissible L.logN R) (claims : List Claim)
  (hJ : claims.length ≤ 2 ^ 46 + 1)

/-- The specification of the variant: from no doom, the root creates `OpeningDoom`, the opening
check follows (`openingSpec`). -/
noncomputable def variantSpec :
    Spec (variantProg L R claims) (fun _ ↦ False) (fun b _ ↦ b = false) εWhir 0 0 :=
  (commitSpec (fun _ h ↦ OpeningDoom L R claims (commits h)) L.logN R
      (eBatch_le_εWhir hw hJ)).bind' fun _ ↦
    (openingSpec L R hw claims).bind' fun _ ↦
      (Spec.ret (Post := fun b _ ↦ b = false) true).mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl

/-- The variant's doom certificate. -/
noncomputable def variantCert : Cert (variantProg L R claims) :=
  (variantSpec L R hw claims hJ).toCert

/-- Doom never holds at the empty history. -/
theorem variantSpec_D_nil : ¬ (variantSpec L R hw claims hJ).D [] [] := by
  intro hD
  have hs : (commitStack L.logN R).retSplit [] = none :=
    retSplit_eq_none_of_after (after_nil' _) fun a ↦ commitStack_ne_ret _ _ a
  have h1 := (Spec.bindD_none hs).1 hD
  unfold commitSpec at h1
  rw [Spec.bind_D] at h1
  rcases hl : Whir.ladder L.logN R with _ | c
  · have hs' : (Verifier.liftOption (Whir.ladder L.logN R)).retSplit [] = none := by rw [hl]; rfl
    exact (Spec.bindD_none hs').1 h1
  · have hs' : (Verifier.liftOption (Whir.ladder L.logN R)).retSplit [] = some (c, [], []) := by
      rw [hl]; rfl
    exact ((Spec.bindD_some hs').1 h1).1 rfl

/-- The variant's proofs of work: WHIR's, of `17` bits. -/
theorem movesOK_variant :
    MovesOK (· ≤ 64) True (variantProg L R claims) := by
  refine MovesOK.seq ((movesOK_commitStack _ _).mono (fun _ h ↦ h.elim) id) fun _ ↦
    MovesOK.seq ?_ fun _ ↦ MovesOK.pure _
  rw [openingCheck_eq]
  exact MovesOK.seq (MovesOK.require _) fun _ ↦
    (movesOK_verifyStackedOpening _ _ _).mono (fun _ hb ↦ hb ▸ queryGrindingBits_le) id

/-- **The certificate's bound**: every group's escape, discounted by the proof of work before it,
is at most `2^-128`. -/
theorem variantCert_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (variantCert L R hw claims hJ).ε h ≤ εWhir := by
  by_cases hr : (variantProg L R claims).Reachable h
  · rw [min_eq_left ((movesOK_variant L R claims).grindBits_le hr)]
    exact Spec.toCert_bound _ (fun hD ↦ absurd hD (variantSpec_D_nil L R hw claims hJ)) h
  · simp only [variantCert, Spec.toCert_ε, hr, false_and, ↓reduceIte, mul_zero, zero_le]

/-! ## The cost -/

theorem rootOk_nil : RootOk (variantProg L R claims) [] :=
  ⟨Prog.Reachable.nil, trivial, rfl, rfl, by rw [after_nil']; rfl⟩

/-- The variant's cost, in quarters of a query: the root, the batching challenge and WHIR at the
largest admissible ladder (mumbai's `whirBound`). -/
theorem costLE_variant :
    (variantProg L R claims).CostLE costHeight (2 + (4 + (2 + whirBound))) := by
  have hopen : Prog.Costs costHeight (openingCheck L R claims) (4 + (2 + whirBound))
      fun _ ↦ True := by
    rw [openingCheck_eq]
    refine Prog.Costs.seq (a := 0) (Prog.Costs.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
    exact (costs_verifyStackedOpening _ _ _ whirBound fun levels h ↦
      ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2.1,
        (ladder_cost _ _ levels h).2.2.2⟩).mono (by omega) fun _ h ↦ h
  exact (Prog.Costs.bind' (costs_commitStack _ _ fun levels h ↦ (ladder_cost _ _ levels h).2.1)
    fun _ _ ↦ Prog.Costs.bind' hopen fun _ _ ↦ Prog.Costs.pure0 true).mono (by omega)
      fun _ _ ↦ trivial

/-- The variant's query bound: the IV's hash, the seed's permutation, and the program's cost. -/
def variantQueries : ℕ := 1 + 1 + (2 + (4 + (2 + whirBound))) / 4

theorem variantQueries_eq : variantQueries = 10122 := by decide

theorem isTotalQueryBound_variant (label : Bytes) (D : Digest) (z : Unit × Proof) :
    IsTotalQueryBound (verifierFam (fixedSeeds label D) (variantProg L R claims) z)
      variantQueries := by
  show IsTotalQueryBound (verifierComp (fixedSeed label D) (nodeAt (variantProg L R claims) []) z.2)
    variantQueries
  rw [nodeAt, after_nil']
  exact isTotalQueryBound_verifierComp (costLE_variant L R claims) (fixedSeed label D) z.2

/-! ## The doom after the root -/

/-- The root's events of an extracted history: its first event. -/
def rootEvents (h : List Ev) : List Ev := h.take 1

/-- **Doom right after the root** is the opening's doom of the root's word. -/
theorem variantCert_D_root {e : Ev} (hce : (commitStack L.logN R).after [e] = some (.ret ()))
    (hdoom : OpeningDoom L R claims (commits [e])) :
    (variantCert L R hw claims hJ).D [e] := by
  obtain ⟨level, rest, W, hc, he⟩ := commitStack_after_ret hce
  rw [variantCert, Spec.toCert_D]
  show Spec.bindD _ _ [] [e]
  refine (Spec.bindD_some (Prog.retSplit_of_after _ [e] [] hce)).2 ⟨fun _ ↦ ?_, ?_⟩
  · exact (commitSpec_D _ (eBatch_le_εWhir hw hJ) hc [] e).2 (by simpa using hdoom)
  · exact Spec.start_D _ _ (by simpa using hdoom)

variable {L R hw claims hJ} in
/-- An accepted run's extracted history starts with the root's commitment. -/
theorem extracted_root {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState}
    {σ : Seed} {π : Proof} (hv : LeanVM.Protocol.Compile.Rom.verify H F σ (variantProg L R claims) π = some true) :
    ∃ e rest, extractedHistory H F σ (variantProg L R claims) π = e :: rest ∧
      (commitStack L.logN R).after [e] = some (.ret ()) := by
  obtain ⟨hafter, -⟩ := Sound.after_extractedHistory H F hv
  obtain ⟨u, m, m', hm, hce, -⟩ := after_bind_ret hafter
  obtain ⟨level, rest, W, hc, rfl⟩ := commitStack_after_ret hce
  exact ⟨_, m', by rw [hm]; rfl, hce⟩

/-! ## The theorem -/

/-- The event: the verifier's run on the proof, every query answered by the cache `c`, extracts a
root word every candidate of which violates one of the claims. -/
def RootDoomed (label : Bytes) (D : Digest) (z : Unit × Proof)
    (c : KeccakCalls.QueryCache) : Prop :=
  OpeningDoom L R claims (commits (rootEvents (extractedHistory (fun x ↦ c (.inl x))
    (fun s ↦ c (.inr s)) (fixedSeed label D) (variantProg L R claims) z.2)))

include hw hJ in
/-- **Fiat-Shamir soundness of the opening with leanVM's transcript shape**, in the two-oracle
random-oracle model (mumbai's `romExperiment`): an adversary of at most `QA` queries outputs a
proof; the verifier accepts while every candidate of the extracted root word violates one of the
claims with probability at most `(QA + QV) · (2^-128 + 5 (QA + QV) / 2^256)`. -/
theorem variant_sound (label : Bytes) (D : Digest)
    (A : OracleComp KeccakCalls (Unit × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam (fixedSeeds label D) (variantProg L R claims))}[
        z.1.2 = true ∧ RootDoomed L R claims label D z.1.1 z.2] ≤
      (QA + variantQueries : ℕ) *
        (εWhir + failBound (fixedSeeds label D) (QA + variantQueries)) := by
  refine romSound_of_imp (variantProg L R claims) (variantCert L R hw claims hJ)
    (fixedSeeds label D) (fun _ ↦ rootOk_nil L R claims) εWhir (variantCert_bound L R hw claims hJ)
    A QA hA variantQueries (isTotalQueryBound_variant L R claims label D)
    (RootDoomed L R claims label D) fun z c hv hbad ↦ ?_
  have key : (fixedSeeds label D).root z.1 = [] := rfl
  have hseed : (fixedSeeds label D).seed z.1 = fixedSeed label D := rfl
  have hroot : nodeAt (variantProg L R claims) [] = variantProg L R claims := by
    rw [nodeAt, after_nil']; rfl
  rw [key, hroot, hseed] at hv
  obtain ⟨e, rest, hhist, hce⟩ := extracted_root (L := L) (R := R) (claims := claims) hv
  unfold Doomed
  rw [key, hroot, hseed]
  refine ⟨[e], ?_, Nat.zero_le _, ?_, ?_⟩
  · show [e] <+: extractedHistory _ _ (fixedSeed label D) (variantProg L R claims) z.2
    rw [hhist]
    exact ⟨rest, rfl⟩
  · obtain ⟨level, rest', W, -, he⟩ := commitStack_after_ret hce
    rw [List.singleton_inj.1 he]
    trivial
  · refine variantCert_D_root L R hw claims hJ hce ?_
    have h := hbad
    unfold RootDoomed rootEvents at h
    rw [hhist] at h
    simpa using h

/-- `2^-k` as `2^(n - k) / 2^n` (mumbai's `inv_pow_eq_div`, `EndToEnd/Sound/Statements.lean`). -/
theorem inv_pow_eq_div (k n : ℕ) (h : k ≤ n) :
    (2 : ℝ≥0∞)⁻¹ ^ k = ((2 ^ (n - k) : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ENNReal.div_eq_inv_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat, pow_add, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

/-- **The numbers** (as mumbai's `leanVm_bound_le`): against `2^64` queries, the bound of
`variant_sound` is at most `2^-63`. -/
theorem variant_bound_le (label : Bytes) (D : Digest) {QA : ℕ} (hQ : QA ≤ 2 ^ 64) :
    ((QA + variantQueries : ℕ) : ℝ≥0∞) *
        (εWhir + failBound (fixedSeeds label D) (QA + variantQueries)) ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  rw [variantQueries_eq]
  set N := QA + 10122 with hN
  have hfail : failBound (fixedSeeds label D) N =
      ((5 * N : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
    rw [failBound, Nat.cast_pow, Nat.cast_ofNat]
    rfl
  rw [hfail, εWhir, inv_pow_eq_div 128 256 (by norm_num),
    ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul,
    inv_pow_eq_div 63 256 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  have hN' : N ≤ 2 ^ 64 + 10122 := by omega
  rw [show 256 - 128 = 128 from rfl, show 256 - 63 = 193 from rfl]
  calc N * (2 ^ 128 + 5 * N) ≤ (2 ^ 64 + 10122) * (2 ^ 128 + 5 * (2 ^ 64 + 10122)) :=
        Nat.mul_le_mul hN' (Nat.add_le_add_left (Nat.mul_le_mul_left 5 hN') _)
    _ ≤ 2 ^ 193 := by norm_num

end WhirBridge
