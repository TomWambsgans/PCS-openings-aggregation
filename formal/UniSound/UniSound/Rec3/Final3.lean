-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proof follows `Final.lean` (the main line's).
import UniSound.Final
import UniSound.Rec3.Fs3

/-!
# Knowledge soundness of π1-rec3, end to end, from its named links

**`uniKnowledgeSoundness3`**: `UniKnowledgeSoundnessRec3 D (uniBound3 e₃₅)` for every deployment `D`, the rounds'
errors at most `e₃₅ = 2^35 / |E|`, from

* `F3 : FlockSound3 κ` — π1-rec3's Flock phase (its zerocheck's squares, its walk);
* `I : UniIds3 D F3 np` — the identity model at π1-rec3's transcripts;
* `BR : PairBatch np` — the paired, narrow batch's rounds;
* `C : UniCode3 …`, `hFin : UniFinal3 …` — the code-level links; `hFs : FsLayer3 …` — the Fiat–Shamir layer;
* the numbers: round `0`'s error, Flock's rounds', the identities' degrees and the merge polynomial's (at most
  `2^35` in all), at most `2^35 − 2` relations on a commitment, the batch's rounds' (`errPair`, `errLast`).

The protocol is `uniPiop3 F3 I BR` (`PiopSound3.lean`, proved). **The weakest rounds are the batch's narrow
pairs**: `8 · 2^32 / |E| = 2^35 / |E|` (`2^-157`) each, the bound `e₃₅` of every round.

**`uniBound3_le_bits`**: `uniBound3 (2^35 / |E|) Q ≤ 2^-61` for `Q ≤ 2^64` (exactly `2^-61.93` at `Q = 2^64`:
`formal/EndToEnd/Review/UniRec3Numbers.py`; the three openings' doom terms, `≈ 3 · 2^-64`, and the tag's `2^-64`
dominate; the list term is `≈ 2^-66.4`).
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset WhirBridge
open scoped ENNReal

variable {D : Deployment} {κ : ℕ} (F3 : FlockSound3 κ) {np : ℕ} (I : UniIds3 D F3 np) (BR : PairBatch np)

theorem hlink_uniPiop3 (C : UniCode3 D F3 I.nV np) (hFin : UniFinal3 D F3 I BR C) (s : USt)
    (done : Done) (tl : List E) (c1 c2 : Stk)
    (hd : DoneFits (rec3Rounds F3.prog.rounds I.nV np) done) (htl : tl.length = 3)
    (hz : (C.prog s.1 s.2).ZerosVanish done tl)
    (hc : ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2) :
    ∃ p m ch, openedOf F3.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧
      (uniPiop3 F3 I BR).post s p m ch := by
  set nF := F3.prog.rounds.length
  set q := openedOf nF c1 c2 done with hq
  have hlen : done.length = nF + 4 + np := by
    rw [hd.length_eq, length_rec3Rounds]
  have hql : q.length = nF + 4 + np := by rw [hq, length_openedOf, hlen]
  have hne : q ≠ [] := by
    intro h
    rw [h] at hql
    simp only [List.length_nil] at hql
    omega
  refine ⟨q.dropLast, (q.getLast hne).1, (q.getLast hne).2, ?_, ?_⟩
  · exact (List.dropLast_append_getLast hne).symm
  change uniS3 F3 I BR s (q.dropLast ++ [((q.getLast hne).1, (q.getLast hne).2)])
  rw [show q.dropLast ++ [((q.getLast hne).1, (q.getLast hne).2)] = q from
    List.dropLast_append_getLast hne]
  obtain ⟨hPend, hFin'⟩ := hFin s done tl c1 c2 hd htl hz hc
  unfold uniS3
  refine ⟨c1, ?_, ?_⟩
  · rw [hq, rd_openedOf _ _ _ _ 0 (by omega)]
    simp
  rw [ite_eq_right (by omega)]
  refine ⟨c2, ?_, ?_, hPend, ?_⟩
  · rw [hq, rd_openedOf _ _ _ _ (nF + 1) (by omega)]
    simp
  · -- Flock's rounds completed.
    show DoneFits F3.prog.rounds (fdOf nF q)
    rw [hq, fdOf_openedOf]
    refine doneFits_map_noRoot _ _ F3.rounds_root ?_
    rcases done with _ | ⟨x, d⟩
    · simp only [List.length_nil] at hlen
      omega
    · have h1 : DoneFits (F3.prog.rounds ++ ([⟨true, 0, 0⟩, ⟨false, I.nV, 1⟩] ++
          (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]))) d := by
        have := hd
        rw [rec3Rounds_eq] at this
        simp only [List.singleton_append] at this
        exact this.2.2
      simpa using doneFits_append_take _ _ d h1
  · rw [ite_eq_right (by omega)]
    exact hFin'

/-- **Every round's error is at most `e`**, given the identity model's, Flock's and the batch's numbers. -/
theorem uniErr3_le (e : ℝ≥0∞)
    (hMain : I.errMain ≤ e) (hFl : ∀ j, F3.err j ≤ e)
    (hdeg : ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hrel : ((I.nRel - 1 + (4 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hP : BR.errPair ≤ e) (hL : BR.errLast ≤ e) (j : ℕ) : uniErr3 F3 I BR j ≤ e := by
  unfold uniErr3
  split_ifs
  · exact hMain
  · exact hFl _
  · exact hdeg
  · exact hrel
  · exact hP
  · exact hL

/-! ## The end theorem, from the named links -/

/-- **Knowledge soundness of π1-rec3** for the explicit extractor `uniExtractor`, with error `uniBound3 e Q` at `Q`
calls of `π` and `π⁻¹`, every round's error at most `e`; under π1-rec3's Flock phase `F3`, the identity model `I`,
the batch `BR`, the code-level links `C`, `hFin` and the Fiat–Shamir layer `hFs`. -/
theorem uniKnowledgeSoundness3 (C : UniCode3 D F3 I.nV np) (hFin : UniFinal3 D F3 I BR C)
    (hFs : FsLayer3 D F3 I.nV np C) (e : ℝ≥0∞)
    (hMain : I.errMain ≤ e) (hFl : ∀ j, F3.err j ≤ e)
    (hdeg : ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hrel : ((I.nRel - 1 + (4 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hP : BR.errPair ≤ e) (hL : BR.errLast ≤ e) :
    UniKnowledgeSoundnessRec3 D (uniBound3 e) :=
  hFs (uniPiop3 F3 I BR) e (uniErr3_le F3 I BR e hMain hFl hdeg hrel hP hL) (hpre_uniPiop3 F3 I BR)
    (hlink_uniPiop3 F3 I BR C hFin)

/-! ## The bits -/

/-- **The bound in bits**: at most `2^-61` for an adversary of at most `2^64` calls of `π` and `π⁻¹`, every round's
error at most `2^35 / |E|`. -/
theorem uniBound3_le_bits (Q : ℕ) (hQ : Q ≤ 2 ^ 64) :
    uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 := by
  unfold uniBound3 uniN
  rw [cardE_cast, div_192_eq']
  have hX : 2 ^ 33 + Q + 10122 ≤ 18446744082299496586 := by
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    have h33 : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
    omega
  have b1 := openingBoundAt_le' (QV := 10122) (QA := 2 ^ 33 + Q) (X := 18446744082299496586) hX
  have hN : 2 ^ 33 + Q ≤ 18446744082299496586 := by omega
  have b2 : ((2 ^ 33 + Q : ℕ) : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) *
      (((2 ^ 35 * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256) + ((2 ^ 128 + 8 * (2 ^ 33 + Q) : ℕ) : ℝ≥0∞) /
        2 ^ 256) ≤
      ((18446744082299496586 * (9952 ^ 2 * (2 ^ 35 * 2 ^ 64)) +
        18446744082299496586 * (2 ^ 128 + 8 * 18446744082299496586) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, ENNReal.div_add_div_same, ← Nat.cast_add,
      ← mul_div_assoc, ← Nat.cast_mul]
    refine cast_div_le_256 ?_
    calc (2 ^ 33 + Q) * (9952 ^ 2 * (2 ^ 35 * 2 ^ 64) + (2 ^ 128 + 8 * (2 ^ 33 + Q)))
        ≤ 18446744082299496586 * (9952 ^ 2 * (2 ^ 35 * 2 ^ 64) +
            (2 ^ 128 + 8 * 18446744082299496586)) :=
          Nat.mul_le_mul hN (by omega)
      _ = _ := by ring
  have b3 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have hq : (2 ^ 81 + Q) ^ 2 ≤ 2 ^ 164 := by
      have h82 : 2 ^ 81 + Q ≤ 2 ^ 82 := by
        have : (2 : ℕ) ^ 82 = 2 ^ 81 + 2 ^ 81 := by norm_num
        have h64 : (2 : ℕ) ^ 64 ≤ 2 ^ 81 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      calc (2 ^ 81 + Q) ^ 2 ≤ (2 ^ 82) ^ 2 := Nat.pow_le_pow_left h82 2
        _ = 2 ^ 164 := by norm_num
    have e1 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 = (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_pow]
    rw [e1]
    calc (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 508 ≤ ((2 ^ 164 : ℕ) : ℝ≥0∞) / 2 ^ 508 :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr hq) _
      _ = (2 : ℝ≥0∞)⁻¹ ^ 344 := by
          rw [Nat.cast_pow, Nat.cast_ofNat, show (508 : ℕ) = 164 + 344 from rfl,
            two_pow_div_two_pow]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 :=
          pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) (by norm_num)
      _ = ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [Nat.cast_one, one_div, ENNReal.inv_pow]
  refine (add_le_add (add_le_add (mul_le_mul' le_rfl b1) b2) b3).trans ?_
  rw [show (3 : ℝ≥0∞) = ((3 : ℕ) : ℝ≥0∞) from rfl, ← mul_div_assoc, ← Nat.cast_mul,
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
  calc _ ≤ ((2 ^ 195 : ℕ) : ℝ≥0∞) / 2 ^ 256 := cast_div_le_256 (by norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 61 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 195 + 61 from rfl, two_pow_div_two_pow]

/-- **π1-rec3, with the bound in bits**: under the same hypotheses at `e = 2^35 / |E|`, at most `2^-61` for every
adversary of at most `2^64` calls of `π` and `π⁻¹`. -/
theorem uniKnowledgeSoundness3_bits (C : UniCode3 D F3 I.nV np) (hFin : UniFinal3 D F3 I BR C)
    (hFs : FsLayer3 D F3 I.nV np C)
    (hMain : I.errMain ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hFl : ∀ j, F3.err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : I.degSum + I.degBad ≤ 2 ^ 35) (hrel : I.nRel + 2 ≤ 2 ^ 35)
    (hP : BR.errPair ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hL : BR.errLast ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) :
    UniKnowledgeSoundnessRec3 D (uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64, uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  ⟨uniKnowledgeSoundness3 F3 I BR C hFin hFs _ hMain hFl
    (ENNReal.div_le_div_right (Nat.cast_le.mpr hdeg) _) (ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _)
    hP hL, uniBound3_le_bits⟩

end UniSound

/-- info: 'UniSound.uniKnowledgeSoundness3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness3

/-- info: 'UniSound.uniKnowledgeSoundness3_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniKnowledgeSoundness3_bits

/-- info: 'UniSound.uniBound3_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniBound3_le_bits
