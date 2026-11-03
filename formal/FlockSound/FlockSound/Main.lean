-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Leanvm

/-!
# Flock's soundness at leanVM's constants: `FlockRegion.Holds` but for bad challenges

The generic theorems of `Flock.lean` at leanVM 42422001's constants (`Leanvm.lean`), for a column
`c` of `2^(8 + κ)` cells of `K` (`q_flock`) and the block R1CS `r1cs` (`blake2sFlockSpec.r1cs`):
the conclusion is Lv42's relation, `BlockR1CS.BatchHolds r1cs constPos (bitTable c)`, which is
`FlockRegion.Holds` (`Lv42.Protocol.FlockRegion.Holds`) of the BLAKE2s region.

* **`flockHolds_v1`** (milestone 1; iteration 2's extension W, `Flock.verify`): the matrices'
  reduction in its own rounds;
* **`flockHolds_merged`** (iteration 2's main line, `Flock.verifyDeferred` and the batching
  sumcheck's `λ³` component);
* **`card_bad`**: every bad set's size: `1` a sampled coordinate, `2^(k+1) - 1` the skip, `2` a
  zerocheck round, `3` `α`, `2` a lincheck round, `1` a ring stage (either order), `2` a matrices'
  round, `K - 1` the batch's `λ`.

The claim on `q_flock` is stated as its value, `Σ_u Φ(eq(p, u)) q(u) = target` (`colWord c`), the
semantics of both of the verifier's encodings: milestone 1's 64 Frobenius-twisted terms and
iteration 2's one ring-twist term.
-/

namespace FlockSound

open Finset Polynomial LeanVM.Parameters LeanVM.Protocol Lv42.Parameters Lv42.Protocol

/-- leanVM's Flock at a skip of `k` bits, its R1CS the block's. -/
abbrev setupOf (k l κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6) (hsize : l + 8 + κ = 7 + ns)
    (sh : List ℕ) (C : BlockR1CS E (Flock.kSkip + Flock.kIn)) : Setup E k l 8 κ 7 ns :=
  leanvmSetup k l κ ns hkl hk hsize sh (cubeMat hkl C.A) (cubeMat hkl C.B)
    ((posFin hkl).symm Flock.constPos)

/-- **Flock at leanVM's constants, the matrices' own rounds** (milestone 1; extension W): if
its rounds are consistent, its terminal check holds and its claims on `q_flock`, `A0`, `B0` are
true, the column satisfies Lv42's Flock relation or a challenge is bad. -/
theorem flockHolds_v1 (k l κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6) (hsize : l + 8 + κ = 7 + ns)
    (sh : List ℕ) (hsh : sh = [32, 16, 8, 4, 2, 1] ∨ sh = [1, 2, 4, 8, 16, 32])
    (C : BlockR1CS E (Flock.kSkip + Flock.kIn)) (c : Column (8 + κ))
    (R : Front E k l 8 κ ns sh.length) (mq : Fin (k + (k + l)) → E[X])
    (mχ : Fin (k + (k + l)) → E) (a b : E)
    (hzc : Consistent 2 (fun i ↦ some (Front.τ (setupOf k l κ ns hkl hk hsize sh C) R i))
      (Front.c₀ (setupOf k l κ ns hkl hk hsize sh C) R) R.zq R.zχ)
    (hlin : Consistent 2 (fun _ ↦ none) (Front.linC₀ (setupOf k l κ ns hkl hk hsize sh C) R) R.lq R.lχ)
    (hmat : Consistent 2 (fun _ ↦ none) (Front.matClaim (setupOf k l κ ns hkl hk hsize sh C) R) mq mχ)
    (hcheck : claimAt (Front.matClaim (setupOf k l κ ns hkl hk hsize sh C) R) mq mχ (Fin.last _) =
      (a + R.α * b) * mle (fun bx ↦ (lag (skipNodes k hk) bx).eval R.z) (lowPart mχ) *
        mle R.s (highPart mχ))
    (ha : a = matMle (Front.rl (setupOf k l κ ns hkl hk hsize sh C) R)
      (Front.rh (setupOf k l κ ns hkl hk hsize sh C) R) (Front.χ' (setupOf k l κ ns hkl hk hsize sh C) R)
      (cubeMat hkl C.A) (lowPart mχ) (highPart mχ))
    (hb : b = matMle (Front.rl (setupOf k l κ ns hkl hk hsize sh C) R)
      (Front.rh (setupOf k l κ ns hkl hk hsize sh C) R) (Front.χ' (setupOf k l κ ns hkl hk hsize sh C) R)
      (cubeMat hkl C.B) (lowPart mχ) (highPart mχ))
    (hring : ∑ u, stagedMap sh R.f (eqP (Front.p (setupOf k l κ ns hkl hk hsize sh C) R) u) *
      colWord c u = Front.target (setupOf k l κ ns hkl hk hsize sh C) R) :
    BlockR1CS.BatchHolds C Flock.constPos (bitTable c) ∨
      Front.Bad (setupOf k l κ ns hkl hk hsize sh C) R (colBits hkl c) ∨
      ∃ j, mχ j ∈ sumBad 2 _ (fun _ ↦ none)
        (matFun (cubeMat hkl C.A) (cubeMat hkl C.B) (skipNodes k hk) R.z
          (Front.rl (setupOf k l κ ns hkl hk hsize sh C) R) (Front.rh (setupOf k l κ ns hkl hk hsize sh C) R)
          (Front.χ' (setupOf k l κ ns hkl hk hsize sh C) R) R.s R.α) mq mχ j := by
  rcases flock_sound_v1 (setupOf k l κ ns hkl hk hsize sh C)
      (leanvmSetup_valid k l κ ns hkl hk hsize sh hsh _ _ _) (colBits hkl c) (colBits_bool hkl c)
      (colWord c) (colPack hkl c) R mq mχ a b hzc hlin hmat hcheck ha hb hring with h | h
  · exact Or.inl ((r1csHolds_iff hkl C c).mp h)
  · exact Or.inr h

/-- **Flock at leanVM's constants, iteration 2's main line** (lever 4a): the product sum is
component `iM` of the batching sumcheck. If every component's terminal claim is true (`a`, `b`
on `A0`, `B0`, the stacks' values for the others) and the claim on `q_flock` holds, the column
satisfies Lv42's Flock relation or a challenge is bad (Flock's, `λ`, or a batch round's). -/
theorem flockHolds_merged (k l κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6) (hsize : l + 8 + κ = 7 + ns)
    (sh : List ℕ) (hsh : sh = [32, 16, 8, 4, 2, 1] ∨ sh = [1, 2, 4, 8, 16, 32])
    (C : BlockR1CS E (Flock.kSkip + Flock.kIn)) (c : Column (8 + κ))
    (R : Front E k l 8 κ ns sh.length) {K e d : ℕ} (iM : Fin K)
    (Φ : Fin K → (Fin (k + (k + l) + e) → E) → E) (hΦ : ∀ i, IndDeg (Φ i) d)
    (hΦM : Φ iM = extFun (lsTab (skipNodes k hk) R.z R.s)
      (gTab (cubeMat hkl C.A) (cubeMat hkl C.B) (Front.rl (setupOf k l κ ns hkl hk hsize sh C) R)
        (Front.rh (setupOf k l κ ns hkl hk hsize sh C) R) (Front.χ' (setupOf k l κ ns hkl hk hsize sh C) R)
        R.α))
    (cl v : Fin K → E) (hcM : cl iM = Front.matClaim (setupOf k l κ ns hkl hk hsize sh C) R) (lam : E)
    (bq : Fin (k + (k + l) + e) → E[X]) (bχ : Fin (k + (k + l) + e) → E) (a b : E)
    (hzc : Consistent 2 (fun i ↦ some (Front.τ (setupOf k l κ ns hkl hk hsize sh C) R i))
      (Front.c₀ (setupOf k l κ ns hkl hk hsize sh C) R) R.zq R.zχ)
    (hlin : Consistent 2 (fun _ ↦ none) (Front.linC₀ (setupOf k l κ ns hkl hk hsize sh C) R) R.lq R.lχ)
    (hbatch : Consistent d (fun _ ↦ none) (∑ i : Fin K, lam ^ (i : ℕ) * cl i) bq bχ)
    (hend : claimAt (∑ i : Fin K, lam ^ (i : ℕ) * cl i) bq bχ (Fin.last _) =
      ∑ i : Fin K, lam ^ (i : ℕ) * v i)
    (hvM : v iM = (a + R.α * b) * mle (fun bx ↦ (lag (skipNodes k hk) bx).eval R.z) (lowPart (lowPart bχ)) *
      mle R.s (highPart (lowPart bχ)) * eqP (highPart bχ) (fun _ ↦ false))
    (hv : ∀ i, i ≠ iM → v i = Φ i bχ)
    (ha : a = matMle (Front.rl (setupOf k l κ ns hkl hk hsize sh C) R)
      (Front.rh (setupOf k l κ ns hkl hk hsize sh C) R) (Front.χ' (setupOf k l κ ns hkl hk hsize sh C) R)
      (cubeMat hkl C.A) (lowPart (lowPart bχ)) (highPart (lowPart bχ)))
    (hb : b = matMle (Front.rl (setupOf k l κ ns hkl hk hsize sh C) R)
      (Front.rh (setupOf k l κ ns hkl hk hsize sh C) R) (Front.χ' (setupOf k l κ ns hkl hk hsize sh C) R)
      (cubeMat hkl C.B) (lowPart (lowPart bχ)) (highPart (lowPart bχ)))
    (hring : ∑ u, stagedMap sh R.f (eqP (Front.p (setupOf k l κ ns hkl hk hsize sh C) R) u) *
      colWord c u = Front.target (setupOf k l κ ns hkl hk hsize sh C) R) :
    BlockR1CS.BatchHolds C Flock.constPos (bitTable c) ∨
      Front.Bad (setupOf k l κ ns hkl hk hsize sh C) R (colBits hkl c) ∨
      lam ∈ lambdaBad cl (fun i ↦ cubeSum (fun _ ↦ none) (Φ i)) ∨
      ∃ j, bχ j ∈ sumBad d _ (fun _ ↦ none) (fun r ↦ ∑ i : Fin K, lam ^ (i : ℕ) * Φ i r) bq bχ j := by
  rcases flock_sound_merged (setupOf k l κ ns hkl hk hsize sh C)
      (leanvmSetup_valid k l κ ns hkl hk hsize sh hsh _ _ _) (colBits hkl c) (colBits_bool hkl c)
      (colWord c) (colPack hkl c) R iM Φ hΦ hΦM cl v hcM lam bq bχ a b hzc hlin hbatch hend hvM hv
      ha hb hring with h | h
  · exact Or.inl ((r1csHolds_iff hkl C c).mp h)
  · exact Or.inr h

/-! ## The bad sets' sizes -/

/-- **Every bad set's size**, at leanVM's constants (`E = GF(2^192)`): `1` for a sampled
coordinate, `2^(k+1) - 1` for the skip challenge, `2` for a zerocheck round, `3` for `α`, `2` for
a lincheck round, `1` for a ring stage; each a function of the run before its challenge. -/
theorem card_bad (k l κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6) (hsize : l + 8 + κ = 7 + ns)
    (sh : List ℕ) (C : BlockR1CS E (Flock.kSkip + Flock.kIn)) (c : Column (8 + κ))
    (R : Front E k l 8 κ ns sh.length) :
    let S := setupOf k l κ ns hkl hk hsize sh C
    let Z := colBits hkl c
    (∀ j, (pointBad ns (sampledTables S.hsize S.fixed (Front.zRes S Z)) R.τs j).card ≤ 1) ∧
    (skipBad S.node (Front.zA S Z) (Front.zB S Z) (Front.zZ Z) (Front.τ S R) R.cv).card ≤
      2 ^ (k + 1) - 1 ∧
    (∀ j, (zcBad S.node (Front.zA S Z) (Front.zB S Z) (Front.zZ Z) (pinTab Z S.cpos) (Front.τ S R) R.z
      (Front.c₀ S R) R.zq R.zχ j).card ≤ 2) ∧
    (alphaBad R.va R.vb (Front.vc S R) (skipVal S.node (Front.zA S Z) R.z R.zχ)
      (skipVal S.node (Front.zB S Z) R.z R.zχ) (skipVal S.node (Front.zZ Z) R.z R.zχ)
      (zhat Z (Front.rt S R) S.cpos)).card ≤ 3 ∧
    (∀ j, (sumBad 2 8 (fun _ ↦ none)
      (linRev (linFun S.A S.B Z S.cpos S.node R.z (Front.rl S R) (Front.rh S R) (Front.rt S R) R.α))
        R.lq R.lχ j).card ≤ 2) ∧
    (∀ j, (ringBad univ S.w S.sh (fun cy ↦ R.s cy - strue Z (Front.rt S R) (Front.χ' S R) cy) R.f j).card
      ≤ 1) := by
  intro S Z
  refine ⟨fun j ↦ card_pointBad_le _ _ _ j, ?_, fun j ↦ card_zcBad_le _ _ _ _ _ _ _ _ _ _ j,
    card_alphaBad_le _ _ _ _ _ _ _, fun j ↦ card_sumBad_le 2 8 _ _ _ _
      ((indDeg_linFun _ _ _ _ _ _ _ _ _ _).linRev) j, fun j ↦ card_ringBad_le _ _ _ _ _ j⟩
  have h := card_skipBad_le (node := S.node) (skipNodes_injective k hk : Function.Injective S.node)
    (Front.zA S Z) (Front.zB S Z) (Front.zZ Z) (Front.τ S R) R.cv
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at h
  rw [pow_succ]
  omega

/-- The matrices' rounds' bad sets (milestone 1): `2` each. -/
theorem card_matBad (k l : ℕ) (A B : Pos k l 8 → Pos k l 8 → Bool) (node : Bool × Cube k → E)
    (z : E) (rl : Fin l → E) (rh χ' : Fin 8 → E) (s : Cube (k + l) → E) (α : E)
    (q : Fin (k + (k + l)) → E[X]) (χ : Fin (k + (k + l)) → E) (j : Fin (k + (k + l))) :
    (sumBad 2 _ (fun _ ↦ none) (matFun A B node z rl rh χ' s α) q χ j).card ≤ 2 :=
  card_sumBad_le 2 _ _ _ q χ ((indDeg_mle _).mul (indDeg_mle _)) j

end FlockSound
