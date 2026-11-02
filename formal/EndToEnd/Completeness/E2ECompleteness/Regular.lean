-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): a lane's bytes read back (`common/Common/Lanes.lean`), `|UInt64| = 2^64`.
import E2ECompleteness.Chain

/-!
# The transcript's challenge is regular

`PcsQuotient.Transcript.challengeOf` reads a digest's bytes `8 … 31` as three big-endian words
(`beWord`), the limbs of the challenge; byte `0 … 7`, the digest's lane `0`, is dropped. So the
challenge and lane `0` determine the digest (`challengeOf_lane0_injective`), and each challenge has
at most `2^64` digests (**`challengeOf_regular`**). A big-endian word's little-endian bytes are its
bytes reversed (`wordBytes_beWord`).
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

theorem shl_or (x : ℕ) (b : UInt8) :
    x <<< (UInt64.toNat 8 % 64) % 2 ^ 64 ||| b.toNat = (x * 256 + b.toNat) % 2 ^ 64 := by
  have h8 : UInt64.toNat 8 % 64 = 8 := rfl
  have hb := UInt8.toNat_lt b
  rw [h8, Nat.shiftLeft_eq, show (2 : ℕ) ^ 64 = 2 ^ 56 * 2 ^ 8 by norm_num,
    Nat.mul_mod_mul_right, Nat.lor_comm,
    LeanVM.Rpm.or_mul_two_pow _ (show b.toNat < 2 ^ 8 by simpa using hb)]
  omega

/-- **A big-endian word's bytes, little-endian, are its bytes reversed.** -/
theorem wordBytes_beWord (bs : List UInt8) :
    wordBytes (beWord bs 0) = [bs.getD 7 0, bs.getD 6 0, bs.getD 5 0, bs.getD 4 0,
      bs.getD 3 0, bs.getD 2 0, bs.getD 1 0, bs.getD 0 0] := by
  have hb : ∀ k, (bs.getD k 0).toNat < 256 := fun k ↦ UInt8.toNat_lt _
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4
  have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  simp only [wordBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [beWord, List.range_succ, List.range_zero, List.nil_append, List.foldl_cons,
      List.foldl_nil, List.foldl_append, UInt64.toNat_or, UInt64.toNat_shiftLeft,
      UInt8.toNat_toUInt64, shl_or, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow, zero_add] <;>
    generalize (bs.getD 0 0).toNat = x0 at * <;>
    generalize (bs.getD 1 0).toNat = x1 at * <;>
    generalize (bs.getD 2 0).toNat = x2 at * <;>
    generalize (bs.getD 3 0).toNat = x3 at * <;>
    generalize (bs.getD 4 0).toNat = x4 at * <;>
    generalize (bs.getD 5 0).toNat = x5 at * <;>
    generalize (bs.getD 6 0).toNat = x6 at * <;>
    generalize (bs.getD 7 0).toNat = x7 at * <;>
    norm_num <;> omega

/-- A big-endian word read from `start` is the one read from the bytes from `start`. -/
theorem beWord_drop (bs : List UInt8) (start : ℕ) : beWord bs start = beWord (bs.drop start) 0 := by
  simp only [beWord, List.getD_eq_getElem?_getD, List.getElem?_drop, zero_add]

/-- **Equal big-endian words have equal bytes.** -/
theorem getD_of_beWord_eq {bs bs' : List UInt8} {s s' : ℕ} (h : beWord bs s = beWord bs' s')
    {k : ℕ} (hk : k < 8) : bs.getD (s + k) 0 = bs'.getD (s' + k) 0 := by
  rw [beWord_drop bs, beWord_drop bs'] at h
  have e := congrArg wordBytes h
  rw [wordBytes_beWord, wordBytes_beWord] at e
  simp only [List.cons.injEq, and_true] at e
  have g : ∀ (l : List UInt8) (t j : ℕ), (l.drop t).getD j 0 = l.getD (t + j) 0 := by
    intro l t j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [← g bs s k, ← g bs' s' k]
  interval_cases k <;> simp only [e]

/-- Byte `8i + k` of a digest is byte `k` of its lane `i`. -/
theorem getD_digestBytes (d : Digest) (i : Fin 4) {k : ℕ} (hk : k < 8) :
    (digestBytes d).getD (8 * i + k) 0 = (wordBytes d[i]).getD k 0 := by
  have e : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [e, LeanVM.Rpm.getD_lanesBytes _ _ (by simp; omega)]
  have h1 : (8 * (i : ℕ) + k) / 8 = i := by omega
  have h2 : (8 * (i : ℕ) + k) % 8 = k := by omega
  simp only [h1, h2, Vector.getElem_toList]
  rfl

/-- Lanes with the same eight bytes are equal. -/
theorem lane_eq_of_bytes {w w' : UInt64} (h : ∀ k < 8, (wordBytes w).getD k 0 = (wordBytes w').getD k 0) :
    w = w' := by
  have hl : wordBytes w = wordBytes w' := by
    refine List.ext_getElem (by simp [LeanVM.Rpm.wordBytes_len]) fun k h1 h2 ↦ ?_
    have hk : k < 8 := by simpa [LeanVM.Rpm.wordBytes_len] using h1
    have := h k hk
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  have e1 := LeanVM.Rpm.bytesLane_wordBytes_append w []
  have e2 := LeanVM.Rpm.bytesLane_wordBytes_append w' []
  rw [hl] at e1
  exact e1.symm.trans e2

/-- Lane `i ∈ {1, 2, 3}` of a digest is read back from its challenge's limb `3 − i`. -/
theorem lane_eq_of_challengeOf {d d' : Digest} (h : challengeOf d = challengeOf d') (i : Fin 4)
    (hi : i ≠ 0) : d[i] = d'[i] := by
  have hlimb : ∀ j : Fin 3, (challengeOf d).limb j = (challengeOf d').limb j := fun j ↦ by rw [h]
  have hw : beWord (digestBytes d) (8 * i) = beWord (digestBytes d') (8 * i) := by
    have hK : ∀ a b : UInt64, K.ofLane a = K.ofLane b → a = b := fun a b hab ↦ by
      have := congrArg K.lane hab
      exact this
    fin_cases i
    · exact absurd rfl hi
    · exact hK _ _ (hlimb 2)
    · exact hK _ _ (hlimb 1)
    · exact hK _ _ (hlimb 0)
  refine lane_eq_of_bytes fun k hk ↦ ?_
  rw [← getD_digestBytes d i hk, ← getD_digestBytes d' i hk]
  exact getD_of_beWord_eq hw hk

/-- **The challenge and lane `0` determine the digest.** -/
theorem challengeOf_lane0_injective {d d' : Digest} (h : challengeOf d = challengeOf d')
    (h0 : d[0] = d'[0]) : d = d' := by
  refine Vector.ext fun i hi ↦ ?_
  have hi' : i < 4 := hi
  interval_cases i
  · exact h0
  · exact lane_eq_of_challengeOf h 1 (by decide)
  · exact lane_eq_of_challengeOf h 2 (by decide)
  · exact lane_eq_of_challengeOf h 3 (by decide)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest

/-- **The transcript's challenge is regular**: at most `2^64` digests per challenge. -/
theorem challengeOf_regular : Regular challengeOf := by
  intro e
  classical
  calc (Finset.univ.filter fun d : Digest ↦ challengeOf d = e).card
      ≤ (Finset.univ : Finset UInt64).card :=
        Finset.card_le_card_of_injOn (fun d : Digest ↦ d[0]) (fun _ _ ↦ Finset.mem_univ _)
          fun d hd d' hd' h0 ↦ challengeOf_lane0_injective
            (((Finset.mem_filter.mp hd).2).trans ((Finset.mem_filter.mp hd').2).symm) h0
    _ = 2 ^ 64 := by
        rw [Finset.card_univ, LeanVM.Protocol.Compile.Rom.card_uint64]

end E2ECompleteness
