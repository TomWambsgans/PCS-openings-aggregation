-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the two calls `KeccakCalls`, the block cost `hashBlocks`, the weight calculus `Common.QueryCostAtMost`, the
-- transfer's error `rpmError`, the proof-of-work miss probability `missProb`; VCVio's `support` of an `OracleComp`.
import UniComplete.FlockProver
import UniComplete.ProverSim
import UniComplete.ProverCost
import UniComplete.Prob

/-!
# Flock's honest prover: its commutation, its cost, and the prover's hypotheses of the probability layer

The probability layer takes Flock's prover as a parameter (`FlockProverH`) and names the facts it uses of it. Here
they are proved of the honest one, **`flockProveH`** (`FlockP.flockProve`, `FlockProver.lean`):

1. **`flockCommutes_flockProveH : FlockCommutes flockProveH`**: it commutes with every monad morphism, the hash
   becoming `φ ∘ H` (`FlockP.wr_flockProve`, piece by piece: `wr_zcRounds`, `wr_lcRounds` by recursion, `wr_skipW`,
   `wr_zerocheckW`, `wr_sendSlices`, `wr_frontW`, `wr_ringEndW`, `wr_endW`), with `Morph.wr`'s lemmas
   (`ProverSim.lean`).
2. **`flockCost_flockProveH : FlockCost flockProveH flockBlocks flockBytes flockCoords`** (`ProverCost.lean`'s writer
   calculus `WC`): at `log_n` and a variant of skip `k`,
   * `flockBlocks`: `log_n − k − 7` sampled coordinates, the skip's `z`, one challenge per zerocheck round
     (`7 + (log_n − k − 7)` rounds), `α`, the lincheck's `8`, the ring map's `6`;
   * `flockBytes`: the `2^k` coset values, two scalars per zerocheck round, `v_a`, `v_b`, two per lincheck round,
     the `64` slices (`24` bytes a scalar);
   * `flockCoords`: `row_low` (at most `6 − k`), `chi_in` (at most `8`), `chi_in'` (`8`).

   At the reference (`log_n = 32`, `flockMain`, skip `3`): `67` blocks, `3552` bytes, `19` coordinates
   (`flockBlocks_reference`, …), within `ProverCost.lean`'s `2^32`, `2^32`, `2^16`.
3. **The probability layer's hypotheses** (`ProbHyp.lean`), at every deployment of the reference shape with a program
   IV of at most `2^16` bytes:
   * **`proverCost_flockProveH : ProverCost flockProveH D (3 * 2 ^ 46)`** (`cost_uniProverWith`,
     `proverBlocks_reference`);
   * **`proverStreamSize_flockProveH : ProverStreamSize flockProveH D (2 ^ 40)`** (`costP_uniProverWith` read on
     the support, `CostP.mem_support`; `proverStream_reference`: at most `4480 + 3552` bytes);
   * `ProverCommutes`, `ProverDuplex`, `FlockSimCommutes` from the commutation (`ProbHyp.lean`'s `…_of_flock`).

**Decision: `3 · 2^46`, not `2^47`.** `Prob.uniCompleteness_reference` asks for `ProverCost flock D (2 ^ 47)`. That
is not provable from this repository's bounds: the prover's count `proverBlocks` is dominated by the five WHIR
openings' bound (E2ECompleteness's `cost_proveOpeningWithH`, `(4 + (2 + whirBound)) · blockFactor 26 2^25` each,
about `5 · 40481 · (14 · 2^26 + 2) ≈ 2^47.43 > 2^47`), whatever Flock's prover costs (its `67` blocks and `3552`
bytes are negligible). The closest statement proved is `ProverCost flockProveH D (3 * 2 ^ 46)`
(`proverBlocks_reference`'s bound). It still fits the run's `2^48` (`totalCost_le_three`: the setup, `3 · 2^46`, the
verifier on `2^40` bytes), so **`uniCompleteness_reference_flockProve`** restates `uniCompleteness_reference` for
`flockProveH` at `NP = 3 · 2^46`, with the same `deltaUni`, from the five hypotheses left (`CoreAccepts`,
`CoreFailsOnlyAtPow`, `BadFpCard`, `BadTCard`, `TQueryFresh`). `Prob.lean` itself is left unchanged.

**Decisions.**

* The commutation lemmas are generic in the monads (no lawfulness needed: `Morph.wr_bind`, `wr_pure`, `wr_ite`,
  `wr_sampleW`, `wr_samplesW`, `wr_sendScalar(s)` do not use it); the recursions (`zcRounds`, `lcRounds`) are
  proved by the same recursion.
* The cost lemmas carry only what the budget and the pending claim need: `samplesW`'s length (the rounds' count),
  `lcRounds`' challenges (`chi_in'`) and the slices' count (`lc.z.size = 2^14 / 2^8 = 64`); `row_low` and `chi_in`
  are `take`s, bounded by their counts whatever the point's length.
* The coset values are bounded by `24 · 2^k` bytes and one challenge (`z`) also without a skip (`k = 0` sends and
  draws nothing); the slices by `64` scalars also with `Slices.claim` (nothing sent).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile.Rom (missProb)
open UniStatement
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.FlockP

open UniStatement.Flock

/-! ## Flock's prover commutes with every monad morphism -/

section Commute

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Morph m n) (H : List UInt8 → m Digest)

/-- **The zerocheck's rounds commute.** -/
theorem wr_zcRounds : ∀ (r : List E) (claim : E) (a b c : Array E),
    φ.wr (zcRounds H r claim a b c) = zcRounds (fun x ↦ φ.app (H x)) r claim a b c
  | [], _, _, _, _ => by simp only [zcRounds, Morph.wr_pure]
  | _ :: rest, _, _, _, _ => by
    simp only [zcRounds, Morph.wr_bind, Morph.wr_sendScalar, Morph.wr_sampleW, Morph.wr_pure, wr_zcRounds rest]

/-- **The lincheck's rounds commute.** -/
theorem wr_lcRounds : ∀ (k : ℕ) (claim : E) (w z : Array E),
    φ.wr (lcRounds H k claim w z) = lcRounds (fun x ↦ φ.app (H x)) k claim w z
  | 0, _, _, _ => by simp only [lcRounds, Morph.wr_pure]
  | k + 1, _, _, _ => by
    simp only [lcRounds, Morph.wr_bind, Morph.wr_sendScalar, Morph.wr_sampleW, Morph.wr_pure, wr_lcRounds k]

theorem wr_skipW (k : ℕ) (r : List E) (wit : Wit) :
    φ.wr (skipW H k r wit) = skipW (fun x ↦ φ.app (H x)) k r wit := by
  simp only [skipW, Morph.wr_ite, Morph.wr_bind, Morph.wr_sendScalars, Morph.wr_sampleW, Morph.wr_pure]

theorem wr_zerocheckW (logN k : ℕ) (wit : Wit) :
    φ.wr (zerocheckW H logN k wit) = zerocheckW (fun x ↦ φ.app (H x)) logN k wit := by
  simp only [zerocheckW, Morph.wr_bind, Morph.wr_samplesW, wr_skipW, wr_zcRounds, Morph.wr_sendScalar,
    Morph.wr_pure]

theorem wr_sendSlices (variant : Variant) (s : List E) :
    φ.wr (sendSlices (m := m) variant s) = sendSlices variant s := by
  simp only [sendSlices, Morph.wr_ite, Morph.wr_bind, Morph.wr_sendScalars, Morph.wr_pure]

theorem wr_frontW (logN : ℕ) (variant : Variant) (q : Array K) :
    φ.wr (frontW H logN variant q) = frontW (fun x ↦ φ.app (H x)) logN variant q := by
  simp only [frontW, Morph.wr_bind, wr_zerocheckW, Morph.wr_sampleW, wr_lcRounds, wr_sendSlices, Morph.wr_pure]

theorem wr_ringEndW (variant : Variant) (s : List E) :
    φ.wr (ringEndW H variant s) = ringEndW (fun x ↦ φ.app (H x)) variant s := by
  simp only [ringEndW, Morph.wr_bind, Morph.wr_samplesW, Morph.wr_pure]

theorem wr_endW (variant : Variant) : ∀ o : Option (List E),
    φ.wr (endW H variant o) = endW (fun x ↦ φ.app (H x)) variant o
  | some s => wr_ringEndW φ H variant s
  | none => Morph.wr_pure φ _

/-- **Flock's honest prover commutes with every monad morphism**, the hash becoming `φ ∘ H`. -/
theorem wr_flockProve (logN : ℕ) (variant : Variant) (q : Array K) :
    φ.wr (flockProve H logN variant q) = flockProve (fun x ↦ φ.app (H x)) logN variant q := by
  simp only [flockProve, Morph.wr_bind, wr_frontW, wr_endW, Morph.wr_pure]

end Commute

/-! ## Flock's prover's cost -/

section Cost

open UniComplete.Cost (WC wc_seq wc_mono wc_pure wc_sampleW wc_sendScalar wc_sendScalars wc_samplesW)

/-- `count` challenges, and as many. -/
theorem wc_samplesW_len : ∀ count : ℕ,
    WC (samplesW callKeccak256 count) count 0 fun l _ ↦ l.length = count
  | 0 => wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by subst hb; rfl
  | count + 1 => by
    unfold samplesW
    refine wc_seq wc_sampleW (fun _ _ _ ↦ ?_) (by omega) (Nat.zero_le _)
    refine wc_seq (wc_samplesW_len count) (fun _ _ hl ↦ ?_) (by omega) (by omega)
    exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by rw [hb, List.length_cons, hl]

/-- **The zerocheck's rounds**: one challenge and two scalars each. -/
theorem wc_zcRounds : ∀ (r : List E) (claim : E) (a b c : Array E),
    WC (zcRounds callKeccak256 r claim a b c) r.length (48 * r.length) fun _ _ ↦ True
  | [], _, _, _, _ => wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial
  | _ :: rest, _, _, _, _ => by
    simp only [zcRounds, List.length_cons]
    refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
    refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
    refine wc_seq wc_sampleW (fun _ _ _ ↦ ?_) (by omega) (Nat.zero_le _)
    refine wc_seq (wc_zcRounds rest _ _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
    exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

theorem length_cosetValues (k : ℕ) (r : List E) (wit : Wit) : (cosetValues k r wit).length = 2 ^ k := by
  simp [cosetValues]

/-- **The skip**: the `2^k` coset values and `z` (nothing without a skip). -/
theorem wc_skipW (k : ℕ) (r : List E) (wit : Wit) :
    WC (skipW callKeccak256 k r wit) 1 (24 * 2 ^ k) fun _ _ ↦ True := by
  unfold skipW
  split
  · refine wc_seq (wc_sendScalars _) (fun _ _ _ ↦ ?_) (Nat.zero_le _)
      (le_of_eq (by rw [length_cosetValues]))
    refine wc_seq wc_sampleW (fun _ _ _ ↦ ?_) (by omega) (Nat.zero_le _)
    exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial
  · exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

theorem length_fixedChallenges : fixedChallenges.length = nFixed := rfl

/-- **The zerocheck**: the sampled coordinates, the skip, `7 + (log_n − k − 7)` rounds, `v_a`, `v_b`. -/
theorem wc_zerocheckW (logN k : ℕ) (wit : Wit) :
    WC (zerocheckW callKeccak256 logN k wit) ((logN - k - nFixed) + 1 + (nFixed + (logN - k - nFixed)))
      (24 * 2 ^ k + 48 * (nFixed + (logN - k - nFixed)) + 48) fun _ _ ↦ True := by
  unfold zerocheckW
  refine wc_seq (wc_samplesW_len _) (fun sampled _ hs ↦ ?_) (by omega) (Nat.zero_le _)
  have hr : (fixedChallenges ++ sampled).length = nFixed + (logN - k - nFixed) := by
    rw [List.length_append, hs, length_fixedChallenges]
  refine wc_seq (wc_skipW _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_zcRounds _ _ _ _ _) (fun _ _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  exact wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

theorem size_foldHigh (v : Array E) (x : E) : (foldHigh v x).size = v.size / 2 := by
  simp [foldHigh]

/-- **The lincheck's rounds**: one challenge and two scalars each; `n` challenges, the witness halved `n` times. -/
theorem wc_lcRounds : ∀ (n : ℕ) (claim : E) (w z : Array E),
    WC (lcRounds callKeccak256 n claim w z) n (48 * n)
      fun out _ ↦ out.challenges.length = n ∧ out.z.size = z.size / 2 ^ n
  | 0, _, _, _ => wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ by subst hb; simp
  | n + 1, _, _, z => by
    simp only [lcRounds]
    refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
    refine wc_seq (wc_sendScalar _) (fun _ _ _ ↦ ?_) (Nat.zero_le _) (by omega)
    refine wc_seq wc_sampleW (fun x _ _ ↦ ?_) (by omega) (Nat.zero_le _)
    refine wc_seq (wc_lcRounds n _ _ _) (fun out _ hout ↦ ?_) (by omega) (by omega)
    refine wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
    subst hb
    dsimp only
    refine ⟨by rw [List.length_cons, hout.1], ?_⟩
    rw [hout.2, size_foldHigh, Nat.div_div_eq_div_mul, ← pow_succ']

/-- The slices, `24` bytes each (none with `Slices.claim`). -/
theorem wc_sendSlices (variant : Variant) (s : List E) :
    WC (sendSlices (m := OracleComp KeccakCalls) variant s) 0 (24 * s.length) fun _ _ ↦ True := by
  unfold sendSlices
  split
  · exact wc_mono (wc_pure _) le_rfl (Nat.zero_le _) fun _ _ _ ↦ trivial
  · exact wc_seq (wc_sendScalars _) (fun _ _ _ ↦ wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _)
      fun _ _ _ ↦ trivial) le_rfl le_rfl

theorem size_lcWitnessOf (k : ℕ) (q : Array K) (zc : Option E × List E × E × E × E) :
    (lcWitnessOf k q zc).size = 2 ^ blake2sR1csLogSize := by
  simp [lcWitnessOf, lincheckWitness]

/-- `2^14 / 2^8 = 64` slices. -/
theorem slices_count : 2 ^ blake2sR1csLogSize / 2 ^ lincheckRounds = kBits := by decide

/-- **The front**: the zerocheck, `α`, the lincheck, the `64` slices; `row_low`, `chi_in`, `chi_in'` have at most
`6 − k`, `8`, `8` coordinates. -/
theorem wc_frontW (logN : ℕ) (variant : Variant) (q : Array K) :
    WC (frontW callKeccak256 logN variant q)
      ((logN - variant.skip - nFixed) + 1 + (nFixed + (logN - variant.skip - nFixed)) + 1 + lincheckRounds)
      (24 * 2 ^ variant.skip + 48 * (nFixed + (logN - variant.skip - nFixed)) + 48 + 48 * lincheckRounds +
        24 * kBits)
      fun frs _ ↦ frs.1.rowLow.length + frs.1.chiIn.length + frs.1.chiInPrime.length ≤
        packing - variant.skip + 2 * lincheckRounds := by
  unfold frontW
  refine wc_seq (wc_zerocheckW _ _ _) (fun zc _ _ ↦ ?_) (by omega) (by omega)
  refine wc_seq wc_sampleW (fun alpha _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  refine wc_seq (wc_lcRounds _ _ _ _) (fun lc _ hlc ↦ ?_) (by omega) (by omega)
  have hz : lc.z.toList.length = kBits := by
    rw [Array.length_toList, hlc.2, size_lcWitnessOf, slices_count]
  refine wc_seq (wc_sendSlices _ _) (fun slices _ _ ↦ ?_) (Nat.zero_le _) (by omega)
  refine wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
  subst hb
  simp only [frontOf, List.length_take, List.length_reverse, hlc.1]
  omega

/-- **The ring map's `6` challenges.** -/
theorem wc_ringEndW (variant : Variant) (s : List E) :
    WC (ringEndW callKeccak256 variant s) ringMapShifts.length 0 fun _ _ ↦ True := by
  unfold ringEndW
  exact wc_seq (wc_samplesW _) (fun _ _ _ ↦ wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _)
    fun _ _ _ ↦ trivial) le_rfl le_rfl

theorem wc_endW (variant : Variant) : ∀ o : Option (List E),
    WC (endW callKeccak256 variant o) ringMapShifts.length 0 fun _ _ ↦ True
  | some s => wc_ringEndW variant s
  | none => wc_mono (wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun _ _ _ ↦ trivial

/-- `assemble`'s pending claim keeps the front's coordinates. -/
theorem assemble_pending (fr : Front) (s : List E) (e : End) :
    (assemble fr s e).pending.rowLow = fr.rowLow ∧ (assemble fr s e).pending.chiIn = fr.chiIn ∧
      (assemble fr s e).pending.chiInPrime = fr.chiInPrime :=
  ⟨rfl, rfl, rfl⟩

end Cost

end UniComplete.FlockP

namespace UniComplete

open UniStatement.Flock

/-! ## The honest Flock prover, generic in the monad and the hash -/

/-- **Flock's honest prover** as the probability layer's parameter (`FlockProverH`). -/
def flockProveH : FlockProverH := fun H ↦ FlockP.flockProve H

/-- **Flock's honest prover commutes with every monad morphism** (`ProverSim.lean`'s `FlockCommutes`). -/
theorem flockCommutes_flockProveH : FlockCommutes flockProveH := by
  intro m n _ _ _ _ φ H logN variant words
  exact FlockP.wr_flockProve φ H logN variant words

/-! ## Its cost -/

/-- **Flock's blocks beyond its bytes**: the `log_n − k − 7` sampled coordinates, the skip's `z`, the zerocheck's
`7 + (log_n − k − 7)` round challenges, `α`, the lincheck's `8`, the ring map's `6`. -/
def flockBlocks (logN : ℕ) (variant : Flock.Variant) : ℕ :=
  (logN - variant.skip - nFixed) + 1 + (nFixed + (logN - variant.skip - nFixed)) + 1 + lincheckRounds +
    ringMapShifts.length

/-- **Flock's bytes**: the `2^k` coset values, the zerocheck's rounds' two scalars, `v_a`, `v_b`, the lincheck's
rounds' two, the `64` slices; `24` bytes a scalar. -/
def flockBytes (logN : ℕ) (variant : Flock.Variant) : ℕ :=
  24 * 2 ^ variant.skip + 48 * (nFixed + (logN - variant.skip - nFixed)) + 48 + 48 * lincheckRounds + 24 * kBits

/-- **Flock's pending coordinates**: `row_low` (`6 − k`), `chi_in` (`8`), `chi_in'` (`8`). -/
def flockCoords (_logN : ℕ) (variant : Flock.Variant) : ℕ := packing - variant.skip + 2 * lincheckRounds

/-- **Flock's honest prover's cost** (`ProverCost.lean`'s `FlockCost`): at most `flockBlocks` blocks beyond one per
byte it writes, at most `flockBytes` bytes, a pending claim of at most `flockCoords` coordinates of its own. -/
theorem flockCost_flockProveH : Cost.FlockCost flockProveH flockBlocks flockBytes flockCoords := by
  intro logN variant words
  show Cost.WC (FlockP.flockProve callKeccak256 logN variant words) _ _ _
  unfold FlockP.flockProve flockBlocks flockBytes flockCoords
  refine Cost.wc_seq (FlockP.wc_frontW _ _ _) (fun frs _ hfrs ↦ ?_) (by omega) (by omega)
  refine Cost.wc_seq (FlockP.wc_endW _ _) (fun e _ _ ↦ ?_) (by omega) (Nat.zero_le _)
  refine Cost.wc_mono (Cost.wc_pure _) (Nat.zero_le _) (Nat.zero_le _) fun b _ hb ↦ ?_
  subst hb
  obtain ⟨h1, h2, h3⟩ := FlockP.assemble_pending frs.1 frs.2 e
  rw [h1, h2, h3]
  exact hfrs

theorem flockBlocks_reference : flockBlocks 32 flockMain = 67 := by decide

theorem flockBytes_reference : flockBytes 32 flockMain = 3552 := by decide

theorem flockCoords_reference : flockCoords 32 flockMain = 19 := by decide

/-- **At the reference (`log_n = 32`, skip `3`)**: `67` blocks, `3552` bytes, `19` coordinates, within
`ProverCost.lean`'s `2^32`, `2^32`, `2^16`. -/
theorem flockCost_reference :
    flockBlocks 32 flockMain ≤ 2 ^ 32 ∧ flockBytes 32 flockMain ≤ 2 ^ 32 ∧ flockCoords 32 flockMain ≤ 2 ^ 16 := by
  rw [flockBlocks_reference, flockBytes_reference, flockCoords_reference]
  norm_num

/-! ## The probability layer's hypotheses on the prover -/

namespace Prob

/-- **A cost with a postcondition on the result holds on the support.** -/
theorem CostP.mem_support {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} {P : α → Prop}
    (h : Cost.CostP X n fun a _ ↦ P a) : ∀ a ∈ support X, P a := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a =>
    intro b hb
    rw [support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact h
  | query_bind t k ih =>
    intro b hb
    rw [Cost.costP_query_bind] at h
    rw [mem_support_bind_iff] at hb
    obtain ⟨u, -, hu⟩ := hb
    exact ih u (h.2 u) b hu

/-- **The honest prover with Flock's honest prover makes at most `3 · 2^46` block calls** at the reference shape
(a program IV of at most `2^16` bytes). Not `2^47`: see the module's note (the five WHIR openings' bound alone is
about `2^47.43`). -/
theorem proverCost_flockProveH (D : Deployment) (hD : D.shape = reference) (hIv : D.programIv.length ≤ 2 ^ 16) :
    ProverCost flockProveH D (3 * 2 ^ 46) := by
  intro input rows q hfit _
  have h := Cost.cost_uniProverWith flockProveH flockBlocks flockBytes flockCoords flockCost_flockProveH D input
    rows q
  rw [hfit.1] at h
  obtain ⟨hk, hw, hp⟩ := flockCost_reference
  exact h.mono (Cost.proverBlocks_reference D hD hIv flockBlocks flockBytes flockCoords hk hw hp)

/-- **Every proof the honest prover can output has a stream of at most `2^40` bytes** at the reference shape (at
most `4480 + 3552`). -/
theorem proverStreamSize_flockProveH (D : Deployment) (hD : D.shape = reference) :
    ProverStreamSize flockProveH D (2 ^ 40) := by
  intro input rows q hfit _ π hπ
  have h := CostP.mem_support (Cost.costP_uniProverWith flockProveH flockBlocks flockBytes flockCoords
    flockCost_flockProveH D input rows q) _ hπ π rfl
  rw [hfit.1] at h
  have hs := Cost.proverStream_reference D hD flockBytes
  rw [flockBytes_reference] at hs
  exact h.trans (hs.trans (by norm_num))

theorem proverCommutes_flockProveH (D : Deployment) : ProverCommutes flockProveH D :=
  proverCommutes_of_flock flockCommutes_flockProveH D

theorem proverDuplex_flockProveH (D : Deployment) : ProverDuplex flockProveH D :=
  proverDuplex_of_flock flockCommutes_flockProveH D

theorem flockSimCommutes_flockProveH : FlockSimCommutes flockProveH :=
  flockSimCommutes_of_commutes flockCommutes_flockProveH

/-! ## The end theorem for Flock's honest prover -/

/-- **The block count at the reference shape, at `NP = 3 · 2^46`**: still below `2^48` (as `totalCost_le` at
`2^47`): the setup's `5 · 2^19 + 10 · 2^23`, the prover's `3 · 2^46`, the verifier's on `2^40` bytes. -/
theorem totalCost_le_three (D : Deployment) (hD : D.shape = reference) (hiv : D.programIv.length ≤ 2 ^ 40) :
    Cost.setupCost D + (3 * 2 ^ 46 + Cost.verifierCost D (2 ^ 40)) ≤ 2 ^ 48 := by
  have h1 : Cost.setupCost D ≤ 5 * 2 ^ 19 + 2 * (5 * 2 ^ 23) := by
    have hv := setupLayout_reference_vars
    have hp : 2 ^ ((setupLayout D.shape).vars - 6 + 1) ≤ 2 ^ 19 := by
      rw [hD]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : 2 ^ (matrixVars - 6 + 1) = 2 ^ 23 := rfl
    unfold Cost.setupCost
    omega
  have h2 : Cost.verifierCost D (2 ^ 40) ≤ (280 + 2 ^ 40) + 1 + (2 * (14 + 18) + 34) + 3 * 2 ^ 40 + 5 * 121492 := by
    unfold Cost.verifierCost Cost.ivCost
    have hw : Cost.walkCost D.shape flockMain ≤ 2 * (14 + 18) + 34 := by
      have h := walkCost_le D.shape flockMain
      rw [hD] at h ⊢
      have hb := reference_blake2s_height
      have hR : blake2sR1csLogSize = 14 := rfl
      rw [hR] at h
      omega
    have hivc : (280 + D.programIv.length) / 136 ≤ 280 + 2 ^ 40 :=
      (Nat.div_le_self _ _).trans (by omega)
    have ho := openCost_le
    omega
  omega

/-- **`UniCompleteness` at the reference shape for Flock's honest prover**, `deltaUni < 2^-167` (`deltaUni_lt`):
`uniCompleteness_reference` at `NP = 3 · 2^46` prover block calls (`proverCost_flockProveH`), `S = 2^40` stream bytes
(`proverStreamSize_flockProveH`), the commutation's three (`flockCommutes_flockProveH`), for a program IV of at most
`2^16` bytes, from the five hypotheses left: `CoreAccepts`, `CoreFailsOnlyAtPow`, `BadFpCard` (`2^24 − 1`),
`BadTCard` (`3 · 2^17`), `TQueryFresh` (`2^-200`). -/
theorem uniCompleteness_reference_flockProve (D : Deployment) (hD : D.shape = reference)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hacc : CoreAccepts D flockProveH)
    (hpow : CoreFailsOnlyAtPow D flockProveH) (hbad : BadFpCard D (2 ^ 24 - 1))
    (hbadT : BadTCard reference (3 * 2 ^ 17)) (htf : TQueryFresh flockProveH D ((2 : ℝ≥0∞)⁻¹ ^ 200)) :
    UniCompleteness D (uniProverRP flockProveH D) deltaUni := by
  rw [← hD] at hbadT
  refine UniCompletenessWith.mono D
    (uniCompleteness_of_core flockProveH D (proverCommutes_flockProveH D) flockSimCommutes_flockProveH
      (proverDuplex_flockProveH D) (proverCost_flockProveH D hD hiv) (proverStreamSize_flockProveH D hD) hacc hpow
      hbad hbadT htf) ?_
  have hN := totalCost_le_three D hD (hiv.trans (by norm_num))
  set N := Cost.setupCost D + (3 * 2 ^ 46 + Cost.verifierCost D (2 ^ 40))
  unfold deltaUni
  gcongr
  · calc (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel
        ≤ ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
          gcongr
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 304 := E2ECompleteness.grinding_le
  · exact rpmError_mono hN

end Prob

end UniComplete

/-! ## Axioms -/

/-- info: 'UniComplete.flockCommutes_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.flockCommutes_flockProveH

/-- info: 'UniComplete.flockCost_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.flockCost_flockProveH

/-- info: 'UniComplete.flockCost_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.flockCost_reference

/-- info: 'UniComplete.Prob.proverCost_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.proverCost_flockProveH

/-- info: 'UniComplete.Prob.proverStreamSize_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.proverStreamSize_flockProveH

/-- info: 'UniComplete.Prob.uniCompleteness_reference_flockProve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.uniCompleteness_reference_flockProve
