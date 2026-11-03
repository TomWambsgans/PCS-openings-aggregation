-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `Fs128.lean` (`FsLayer128`,
-- `uniBound128_le_bits`, `hlab_uni`) for π1-rec3: its layer `FsLayer3`, its IV (`ivInput3`, `ivAdv3`).
import UniSound.Rec3.FsGame3
import UniSound.Fs128

/-!
# π1-rec3's Fiat–Shamir layer at `≥ 128` bits: the bound and the seed

**`FsLayer128_3`**: `FsLayer3` (`Fs3.lean`) with the bound **`uniBound128 e`** (`Fs128.lean`), unchanged: its
openings' term charges the openings once, as one union family (`Compose.prEvent_doomF_le`: a fresh query extends
at most one opening's transcript), so it does not count them, and π1-rec3's three openings are plain layouts of
`2^24 ..= 2^28` words, among `WhirBridge.largeShapes` (`FsGame128_3.lean`'s `hops_uni3`), as the main line's five.

**`uniBound128_le_bits35`**: `uniBound128 (2^35 / |E|) Q ≤ 2^-64` for `Q ≤ 2^64` (`2^-64.494` at `Q = 2^64`:
`EndToEnd/Review/UniRec3Numbers.py`, exact rationals), at π1-rec3's rounds' error `2^35 / |E|` (the batch's narrow
pairs), proved as `uniBound128_le_bits` (all terms over `2^256`, numerator at most `2^192`).

**`hlab_uni3`**: the seed's first 32 bytes are `name ‖ iv[0:16]` with `iv` the answer to the two-oracle adversary's
last query (`ivAdv3`: π1-rec3's contract IV, of the `programIv.length + 289` bytes of `ivInput3`), as `hlab_uni`.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-- **π1-rec3's Fiat–Shamir layer at `≥ 128` bits**: `FsLayer3` with the bound `uniBound128`. -/
def FsLayer128_3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np) : Prop :=
  ∀ (R : RbrPiop (rec3Rounds F3.prog.rounds nV np) USt Stk) (e : ℝ≥0∞), (∀ j, R.err j ≤ e) →
    (∀ s c m, R.pre s [] (some c, m) → Rel D s c) →
    (∀ (s : USt) done tl c1 c2, DoneFits (rec3Rounds F3.prog.rounds nV np) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf F3.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch) →
    UniKnowledgeSoundnessRec3 D (uniBound128 e)

/-! ## The bound in bits, at `2^35 / |E|` -/

section Bits

/-- `2^35 / |E|` over `2^256`. -/
theorem e35_eq : ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) =
    ((2 ^ 35 * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [LeanVM.Protocol.card_E]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (256 : ℕ) = 192 + 64 from rfl, pow_add,
    ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]

/-- **The bound in bits at π1-rec3's rounds' error**: at most `2^-64` for an adversary of at most `2^64` calls of
`π` and `π⁻¹`, every round's error at most `2^35 / |E|` (`2^-64.494` at `2^64`), i.e. at least `128` bits as
`Q / ε`. -/
theorem uniBound128_le_bits35 (Q : ℕ) (hQ : Q ≤ 2 ^ 64) :
    uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  unfold uniBound128
  rw [e35_eq, eps128_eq]
  have hN : uniN Q ≤ 18446744082299486208 := by
    unfold uniN
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    have : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
    omega
  set X : ℕ := 18446744082299486208 with hX
  have b1 : (uniN Q : ℝ≥0∞) * (((269 * 2 ^ 119 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
      ((5 * uniN Q : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤ ((X * (269 * 2 ^ 119 + 5 * X) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [a256, d256]
    exact le256 (Nat.mul_le_mul hN (by omega))
  have b2 : (uniN Q : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) * (((2 ^ 35 * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((8 * uniN Q : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤
      ((X * (9952 ^ 2 * (2 ^ 35 * 2 ^ 64) + 8 * X) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [d256, a256, d256]
    exact le256 (Nat.mul_le_mul hN (by omega))
  have b3 : ((2 * uniN Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 * X ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
    le256 (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hN 2))
  have b4 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have hq : (2 ^ 81 + Q) ^ 2 ≤ 2 ^ 164 := by
      have h82 : 2 ^ 81 + Q ≤ 2 ^ 82 := by
        have : (2 : ℕ) ^ 82 = 2 ^ 81 + 2 ^ 81 := by norm_num
        have h64 : (2 : ℕ) ^ 64 ≤ 2 ^ 81 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      calc (2 ^ 81 + Q) ^ 2 ≤ (2 ^ 82) ^ 2 := Nat.pow_le_pow_left h82 2
        _ = 2 ^ 164 := by norm_num
    rw [← Nat.cast_pow]
    calc (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 508 ≤ ((2 ^ 164 : ℕ) : ℝ≥0∞) / 2 ^ 508 :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr hq) _
      _ = (2 : ℝ≥0∞)⁻¹ ^ 344 := by
          rw [Nat.cast_pow, Nat.cast_ofNat, show (508 : ℕ) = 164 + 344 from rfl,
            two_pow_div_two_pow]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 :=
          pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) (by norm_num)
      _ = ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [Nat.cast_one, one_div, ENNReal.inv_pow]
  refine (add_le_add (add_le_add (add_le_add b1 b2) b3) b4).trans ?_
  rw [a256, a256, a256]
  calc _ ≤ ((2 ^ 192 : ℕ) : ℝ≥0∞) / 2 ^ 256 := le256 (by rw [hX]; norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 64 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 192 + 64 from rfl, two_pow_div_two_pow]

end Bits

/-! ## The seed is `name ‖ iv ‖ input`, the IV an answer the adversary asked -/

theorem eval_ivKC3 (D : Deployment) (π : UPf) (T : KTable) :
    evalWithAnswerFn (QueryImpl.ofFn T) (ivKC3 D π) = viewT T (ivInput3 D π.roots) := by
  simp only [ivKC3, hash256, callKeccak256, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

theorem log_ivKC3 (D : Deployment) (π : UPf) (T : KTable) :
    (tableQueryLog (ivKC3 D π) T).map Sigma.fst = [Sum.inl (ivInput3 D π.roots)] := by
  simp only [ivKC3, hash256, callKeccak256, tableQueryLog_bind, tableQueryLog_pure]
  rfl

/-- **The seed's first 32 bytes are `name ‖ iv[0:16]`, `iv` the answer to the adversary's last query**
(`ivAdv3`: π1-rec3's contract IV of the proof the setup fixes): π1-rec3's game's `hlab`. -/
theorem hlab_uni3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (hs : UniShapes D)
    (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf) (T : KTable) :
    ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG (uSetup D hs) uFix (ivAdv3 D A₀)) T).map
        Sigma.fst ∧
      ((uSpec3 F3 nV np).label (uView (uRounds3 F3 nV np) (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (uSetup D hs) uFix (ivAdv3 D A₀)))).1).take 32 =
        name ++ (viewT T w).toList.take (32 - name.length) := by
  obtain ⟨hl, he⟩ := withSetupG_run (uSetup D hs) uFix (ivAdv3 D A₀) T
  set s := evalWithAnswerFn (QueryImpl.ofFn T) (uSetup D hs)
  set π := evalWithAnswerFn (QueryImpl.ofFn T) (A₀ s)
  refine ⟨ivInput3 D (uFix s π).roots, ?_, ?_⟩
  · rw [hl, List.map_append]
    refine List.mem_append_right _ ?_
    simp only [ivAdv3, tableQueryLog_bind, tableQueryLog_map, List.map_append, List.mem_append]
    refine Or.inr ?_
    rw [log_ivKC3]
    exact List.mem_singleton_self _
  · rw [he]
    have hev : evalWithAnswerFn (QueryImpl.ofFn T) (ivAdv3 D A₀ s) =
        setIv (viewT T (ivInput3 D (uFix s π).roots)) π := by
      simp only [ivAdv3, evalWithAnswerFn_bind, evalWithAnswerFn_map, eval_ivKC3]
      rfl
    rw [hev, name_length]
    show (uniLabel (uView (uRounds3 F3 nV np) (uFix s (setIv _ π))).1).take 32 = _
    rw [uniLabel_take32]
    rfl

end UniSound

/-- info: 'UniSound.hlab_uni3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.hlab_uni3

/-- info: 'UniSound.uniBound128_le_bits35' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniBound128_le_bits35
