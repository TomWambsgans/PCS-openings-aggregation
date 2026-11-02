-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM `mumbai`'s cost lemmas (https://github.com/Verified-zkEVM/leanerVM, commit
-- 6175f1a0, MIT OR Apache-2.0, `lean_vm/LeanVM/Protocol/Rpm/Cost.lean`): `Short`,
-- `hashBlocks_le_of_short`, `WidthsLE`, `widthsLE_commitStack`, `widthsLE_verifyWhir`,
-- `allQ_runProof`, `isWeightBound_of_isTotalQueryBound`, as `isWeightBound_verifier` there.
import Soundness.Defs

/-!
# The deployed verifier's calls of `π`

In the random-permutation model a Keccak-256 hash of `n` bytes costs `⌊n / 136⌋ + 1` calls of `π`
and a Keccak-f call one (`hashBlocks`). The deployed verifier (`verifyD` at `deployD c 22`) makes
at most `6 + 3 · 10122` queries (the chain's six, `ourVerifier_queryBound` for each opening), each
**short** (at most `2^39 + 9` bytes, so at most `2^32` calls of `π`): the chain's inputs are at
most `112` bytes; an opening's seed hashes its `76`-byte prefix and its claims, at most two
(`deployD`'s claim maps: `reduce`'s one or two claims, or `rejectClaims`' two) of at most
`2^39 / 48` coordinates; its program commits at most `192` words a leaf (mumbai's `WidthsLE`, as
leanVM's verifier program), so its Merkle leaves are at most `1536` bytes and its nodes `64`.

* **`cost_verifyD_deployD`**: `verifyD W (deployD c 22) po` makes at most
  `(6 + 3 · 10122) · 2^32` calls of `π`, whatever the proof: the hypothesis `hOπ` of
  `Compose/Rpm.lean`, in the form `RpmV.lean` takes it (the whole verifier, at the deployed
  claim maps; `Rpm.lean`'s `∀ L w` form, for every layout and every statement of up to `2^46`
  claims, does not hold).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge
open LeanVM.Rpm (Short hashBlocks WidthsLE maxWidth)

/-- The chain's queries are short. -/
theorem allQ_chain {P : Params E} {B : P.Bounds} (W : Wire P B) (π : RootProof E) :
    AllQueriesSatisfy (chainWith W hash256 π) Short := by
  simp only [chainWith, hash256, bind_assoc, pure_bind]
  have hq : ∀ (x : List UInt8), x.length ≤ 2 ^ 39 + 9 →
      ∀ {β : Type} (k : Digest → OracleComp KeccakCalls β), (∀ u, AllQueriesSatisfy (k u) Short) →
        AllQueriesSatisfy (callKeccak256 x >>= k) Short :=
    fun x hx _ k hk => allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryH hx) hk
  refine hq _ (by simp [length_labelOf]) _ fun _ => hq _ ?_ _ fun _ => hq _ ?_ _ fun _ =>
    hq _ ?_ _ fun _ => hq _ ?_ _ fun _ => hq _ ?_ _ fun _ => trivial
  all_goals simp [Wire.afterRoot, Wire.afterValues, Wire.valueWords]

/-- Every commitment of the opening's program has width at most `192`. -/
theorem widthsLE_variantProg (S : Stacking) (R : ℕ) (cs : List Claim) :
    WidthsLE maxWidth (variantProg S R cs) := by
  unfold variantProg
  refine LeanVM.Rpm.WidthsLE.seq (LeanVM.Rpm.widthsLE_commitStack _ _) fun _ => ?_
  refine LeanVM.Rpm.WidthsLE.seq ?_ fun _ => trivial
  rw [Stacking.check_eq_ite]
  split_ifs
  · rw [LeanVM.Protocol.Verifier.verifyStackedOpening_eq_target]
    exact LeanVM.Rpm.WidthsLE.seq
      (LeanVM.Rpm.WidthsLE.of_moves (g := fun _ ↦ True) LeanVM.Protocol.EndToEnd.Sound.MovesOK.sampleE)
      fun _ ↦ LeanVM.Rpm.widthsLE_verifyWhir _ _ _ _
  · trivial

theorem length_claimsBytes (cs : List Claim) :
    (claimsBytes cs).length = 24 * (flat cs).length := by
  simp [claimsBytes, List.length_flatMap, scalarBytes_length, Nat.mul_comm]

theorem length_flat (cs : List Claim) : (flat cs).length = (cs.map fun c => c.point.length + 1).sum := by
  simp [flat, List.length_flatMap]

/-- **An opening of at most two claims of at most `2^30` coordinates makes short queries only.** -/
theorem allQ_ourVerifier (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof)
    (h2 : w.1.2.claims.length ≤ 2) (hv : L.vars ≤ 2 ^ 30) :
    AllQueriesSatisfy (ourVerifier L R w) Short := by
  rw [ourVerifier_eq]
  by_cases hne : w.1.2.claims.isEmpty = false
  swap
  · simp only [hne, ↓reduceIte]; trivial
  simp only [hne, ↓reduceIte]
  refine allQueriesSatisfy_bind (allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryH ?_)
    fun _ => LeanVM.Rpm.allQ_queryF _) fun seed => ?_
  · rw [List.length_append, openingPrefix_length, length_claimsBytes, length_flat]
    have hpt : ∀ c ∈ w.1.2.claims, c.point.length + 1 ≤ 2 ^ 30 + 1 := fun c hc => by
      have := w.1.2.wide c hc
      simp only [Layout.stacking] at this
      omega
    have hs := List.sum_le_length_nsmul (w.1.2.claims.map fun c => c.point.length + 1)
      (2 ^ 30 + 1) (by simpa using hpt)
    simp only [List.length_map, smul_eq_mul] at hs
    have : w.1.2.claims.length * (2 ^ 30 + 1) ≤ 2 * (2 ^ 30 + 1) := Nat.mul_le_mul_right _ h2
    omega
  · by_cases hr : WhirBridge.rootOf w.2 = some w.1.1
    · simp only [hr, ↓reduceIte]
      exact LeanVM.Rpm.allQ_runProof _ seed _ (widthsLE_variantProg _ _ _)
    · simp only [hr, ↓reduceIte]; trivial

/-- `toStmt`'s claims are at most two when the claims handed are. -/
theorem length_toStmt_le (L : Layout) (cs : List Claim) (h : cs.length ≤ 2) :
    (toStmt L cs).claims.length ≤ 2 := by
  rcases toStmt_claims L cs with ⟨he, -⟩ | he
  · rw [he]; exact h
  · rw [he]; rfl

theorem length_claimsFrom_le (v : ℕ) (o : Option Reduced) (sel : Reduced → List Claim)
    (h : ∀ r, (sel r).length ≤ 2) : (claimsFrom v o sel).length ≤ 2 := by
  cases o with
  | none => rfl
  | some r => exact h r

/-- The deployed layouts have at most `30` variables. -/
theorem vars_deployD (c : Consts) :
    (deployD c 22).Lw.vars ≤ 2 ^ 30 ∧ (deployD c 22).Lσ.vars ≤ 2 ^ 30 ∧
      (deployD c 22).LQ.vars ≤ 2 ^ 30 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [deployD, witnessLayout, wiringLayout, quotientLayout, Layout.hidden, Layout.new, cellVars]

/-- **The deployed verifier's queries are short.** -/
theorem allQ_verifyD_deployD (c : Consts) {P : Params E} {B : P.Bounds} (W : Wire P B)
    (po : RootProof E × OpenProofs) :
    AllQueriesSatisfy (verifyD W (deployD c 22) po) Short := by
  obtain ⟨hw, hs, hq⟩ := vars_deployD c
  unfold verifyD
  refine allQueriesSatisfy_bind (allQ_chain W po.1) fun ch => ?_
  refine allQueriesSatisfy_bind (allQ_ourVerifier _ _ _ ?_ hw) fun _ =>
    allQueriesSatisfy_bind (allQ_ourVerifier _ _ _ ?_ hs) fun _ =>
      allQueriesSatisfy_bind (allQ_ourVerifier _ _ _ ?_ hq) fun _ => trivial
  · exact length_toStmt_le _ _ (length_claimsFrom_le _ _ _ fun _ => by simp)
  · exact length_toStmt_le _ _ (length_claimsFrom_le _ _ _ fun _ => by simp)
  · exact length_toStmt_le _ _ (length_claimsFrom_le _ _ _ fun _ => by simp)

/-- The deployed verifier makes at most `6 + 3 · 10122` queries. -/
theorem isTotalQueryBound_verifyD {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F]
    [SampleableType F] {P : Params F} {B : P.Bounds} (W : Wire P B) (D : Deploy F)
    (po : RootProof F × OpenProofs) :
    IsTotalQueryBound (verifyD W D po) (6 + (10122 + (10122 + (10122 + 0)))) := by
  unfold verifyD
  exact isTotalQueryBound_bind (chain_queryBound_kc W po.1) fun _ =>
    isTotalQueryBound_bind (ourVerifier_queryBound _ _ _) fun _ =>
      isTotalQueryBound_bind (ourVerifier_queryBound _ _ _) fun _ =>
        isTotalQueryBound_bind (ourVerifier_queryBound _ _ _) fun _ => trivial

/-- One query's worth of permutation calls, `2^32`, times the verifier's queries. -/
def verifierPermCalls : ℕ := (6 + 3 * 10122) * 2 ^ 32

/-- **The deployed verifier makes at most `(6 + 3 · 10122) · 2^32` calls of `π`**, on every proof. -/
theorem cost_verifyD_deployD (c : Consts) {P : Params E} {B : P.Bounds} (W : Wire P B)
    (po : RootProof E × OpenProofs) :
    Common.QueryCostAtMost (verifyD W (deployD c 22) po) hashBlocks verifierPermCalls := by
  have h := LeanVM.Rpm.isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32)
    (isTotalQueryBound_verifyD W (deployD c 22) po)
    ((allQ_verifyD_deployD c W po).mono fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)
  unfold verifierPermCalls
  simpa using h

/-- info: 'Soundness.cost_verifyD_deployD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.cost_verifyD_deployD

end Soundness
