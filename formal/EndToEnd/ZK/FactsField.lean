-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoinsMatch
import QuotientZk.Instance.Prover
import Completeness.Tables
import Field.Sampleable

/-!
# The deployed fields, and the statement's coins as the skeleton model's randomness

The facts about `K = GF(2^64)` and `E = GF(2^192)` (mumbai's `LeanVM.Parameters.K`, `E`, by `rfl`
`Primitives.F64`, `Primitives.F192` of `formal/Field`) the zero-knowledge instance takes as
hypotheses, and the bijection `CoinsMatch` needs (`ZK/CoinsMatch.lean`).

* **The fields**: `card_K`, `card_E` (`2^64`, `2^192` elements); `linIndep_Y`, `finrank_KE`: `1, Y, Y²`
  is a basis of `E` over `K` (`F192.ofLimbs_eq`, `F192.eq_sum_limbs`), so `E` has dimension `3`.
* **The representations** (`deployedRep`, a `QuotientZk.Instance.Rep`): `wordsK`, the element of `K`
  whose 64 bits are those of `n` (`F64.ofNat`; `+` is the `xor` of the words); `F64.toU64`, the word of
  an element; `limbsE`, an element of `E` as its three limbs `c0, c1, c2` (`F192.new` back).
* **The base field in `E`**: `inKD`, a computable test (limbs `1` and `2` zero), and `inKD_iff`: it
  holds exactly on the image of `algebraMap K E`; `limbSysE`, `E = K + K Y + K Y²` as the
  `Completeness.LimbSystem` of the quotient table.
* **The coins** (`eD`, `eD_bijective`): the skeleton model's randomness `RandD K` (the twelve masks and
  both tables' padding, lane by entry) as the statement prover's coin words `CoinWords`, a bijection
  built as an `Equiv` (`eDEquiv`). An element is the word of its 64 bits (`wK`; `ofLane_wordOf_w64`:
  decoding gives it back); mask word `k` is mask `(k / 3, k % 3)` (`decodeMasks` reads word
  `3 j + i`); padding word `l · 2^ℓ + j` of a table is the model's entry `(l, padSrc ℓ held l j)`,
  where `padSrc` is the identity except on the overflow lane `32`, where past its first piece it
  skips the `held` pieces the lane holds (`Layout.stackOf`: there the stack reads `pad 32 (i − held·2^8)`,
  the lane's stream continuing) and sends the stream's unread tail to the skipped entries, a
  permutation of the lane (`padDst` its inverse). The decoding lemmas: `decodeCoins_eD_masks`
  (the masks are the model's), `decodeCoins_eD_pad₁`, `decodeCoins_eD_pad₂` (the statement's
  `pad l j` is the model's entry `(l, padSrc ℓ held l j)`, `ℓ, held = 19, 33` for the witness table,
  `22, 167` for the quotient table). The statement layouts' sizes (`lanes_SW`, `logLane_SW`,
  `pieces_SW`, `padWords_W` and the quotient's) are checked by the kernel on the short lists.
-/

open LeanVM.Parameters
open Primitives

namespace PcsQuotient.EndToEnd

/-! ## The fields -/

/-- **`K` has `2^64` elements.** -/
theorem card_K : Fintype.card K = 2 ^ 64 :=
  (Fintype.card_congr finEquivF64.symm).trans (Fintype.card_fin _)

/-- **`E` has `2^192` elements.** -/
theorem card_E : Fintype.card E = 2 ^ 192 :=
  (Fintype.card_congr (Equiv.refl E)).trans F192.card

/-- **`1, Y, Y²` are independent over `K`.** -/
theorem linIndep_Y : LinearIndependent K ![(1 : E), F192.Y, F192.Y ^ 2] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  change g 0 • (1 : E) + g 1 • F192.Y + g 2 • F192.Y ^ 2 = 0 at hg
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one] at hg
  have h : F192.ofLimbs (g 0) (g 1) (g 2) = F192.ofLimbs 0 0 0 := by
    rw [F192.ofLimbs_eq, ← F192.zero_eq]
    exact hg
  obtain ⟨h0, h1, h2⟩ := F192.ofLimbs_injective h
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- `1, Y, Y²` span `E` over `K`. -/
theorem span_Y : ⊤ ≤ Submodule.span K (Set.range ![(1 : E), F192.Y, F192.Y ^ 2]) := by
  intro x _
  rw [F192.eq_sum_limbs x]
  have h0 : (1 : E) ∈ Set.range ![(1 : E), F192.Y, F192.Y ^ 2] := ⟨0, rfl⟩
  have h1 : F192.Y ∈ Set.range ![(1 : E), F192.Y, F192.Y ^ 2] := ⟨1, rfl⟩
  have h2 : F192.Y ^ 2 ∈ Set.range ![(1 : E), F192.Y, F192.Y ^ 2] := ⟨2, rfl⟩
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · have h := Submodule.smul_mem _ (F192.limb x 0) (Submodule.subset_span (R := K) h0)
    rw [Algebra.smul_def, mul_one] at h
    exact h
  · have h := Submodule.smul_mem _ (F192.limb x 1) (Submodule.subset_span (R := K) h1)
    rw [Algebra.smul_def] at h
    exact h
  · have h := Submodule.smul_mem _ (F192.limb x 2) (Submodule.subset_span (R := K) h2)
    rw [Algebra.smul_def] at h
    exact h

/-- The basis `1, Y, Y²` of `E` over `K`. -/
noncomputable def basisY : Module.Basis (Fin 3) K E := Module.Basis.mk linIndep_Y span_Y

/-- **`E` has dimension `3` over `K`.** -/
theorem finrank_KE : Module.finrank K E = 3 := by
  rw [Module.finrank_eq_card_basis basisY, Fintype.card_fin]

/-! ## The representations -/

/-- **`K`'s words**: `word n` is the element whose 64 bits are those of `n` (`F64(n as u64)`). -/
def wordsK : QuotientSecurity.Hiding.Words K where
  word n := F64.ofNat n
  word_xor a b := by
    unfold F64.ofNat
    rw [BitVec.ofNat_xor]
    rfl
  word_inj a b ha hb h := by
    have h' := congrArg (fun x : K => (BF64.toBitVec x).toNat) h
    simp only [F64.ofNat, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat] at h'
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- **`E` as its limbs** `(c0, c1, c2)`, `F192::new` back. -/
def limbsE : E ≃ QuotientRpm.Limbs where
  toFun x := (F192.c0 x, F192.c1 x, F192.c2 x)
  invFun c := F192.new c.1 c.2.1 c.2.2
  left_inv x := F192.new_c0_c1_c2 x
  right_inv _ := rfl

/-- **The deployed representations**: `K`'s words, the word of an element, `E`'s limbs. -/
def deployedRep : QuotientZk.Instance.Rep K E :=
  ⟨wordsK, F64.toU64, F64.toU64_injective, limbsE⟩

/-! ## The base field in `E` -/

/-- **An element of `E` lies in `K`**: its limbs `1` and `2` are zero. -/
def inKD (x : E) : Bool := decide (F192.limb x 1 = 0 ∧ F192.limb x 2 = 0)

/-- **`inKD` tests the image of `K`.** -/
theorem inKD_iff : ∀ x : E, inKD x = true ↔ x ∈ Set.range (algebraMap K E) := by
  intro x
  unfold inKD
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨F192.limb x 0, ?_⟩
    have h := F192.eq_sum_limbs x
    rw [h1, h2, F192.ofF64_zero, zero_mul, zero_mul, add_zero, add_zero] at h
    exact h.symm
  · rintro ⟨a, rfl⟩
    show F192.limb (F192.ofF64 a) 1 = 0 ∧ F192.limb (F192.ofF64 a) 2 = 0
    rw [F192.ofF64_eq]
    exact ⟨rfl, rfl⟩

/-- **`E = K + K Y + K Y²`**, the quotient table's limbs (`F192`'s `c0, c1, c2`). -/
noncomputable def limbSysE : _root_.Completeness.LimbSystem K E where
  ι := algebraMap K E
  Y := F192.Y
  limb x e := F192.limb x e
  decomp x := by
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
    exact F192.eq_sum_limbs x

/-! ## The coins

### An element as a word -/

/-- An element's coin: the `W64` of its 64 bits. -/
def wK : K ≃ W64 := finEquivF64.symm.trans (finCongr (by norm_num))

theorem wK_val (a : K) : ((wK a : W64) : ℕ) = (BF64.toBitVec a).toNat := rfl

/-- **Decoding an element's word gives it back.** -/
theorem ofLane_wordOf_w64 (a : K) : K.ofLane (wordOf (wK a)) = a := by
  apply BF64.toBitVec_injective
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 (BF64.toBitVec a).toNat).toNat = (BF64.toBitVec a).toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (BF64.toBitVec a).isLt

/-! ### Words of a list -/

theorem getD_map_ofFn {N : ℕ} (c : Fin N → W64) (k : ℕ) (hk : k < N) :
    ((List.ofFn c).map wordOf).getD k 0 = wordOf (c ⟨k, hk⟩) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem toArray_getD_map_ofFn {N : ℕ} (c : Fin N → W64) (k : ℕ) (hk : k < N) :
    ((List.ofFn c).map wordOf).toArray.getD k 0 = wordOf (c ⟨k, hk⟩) := by
  simp [Array.getD_eq_getD_getElem?, hk]

/-! ### The masks -/

/-- **The masks as words**: word `k` is mask `(k / 3, k % 3)`. -/
def masksEquiv : (Fin 4 → Fin 3 → K) ≃ (Fin 12 → W64) where
  toFun m k := wK (m ⟨k / 3, by have := k.isLt; omega⟩ ⟨k % 3, by omega⟩)
  invFun w j i := wK.symm (w ⟨3 * j + i, by have := j.isLt; have := i.isLt; omega⟩)
  left_inv m := by
    funext j i
    show wK.symm (wK (m _ _)) = m j i
    rw [Equiv.symm_apply_apply]
    have := j.isLt
    have := i.isLt
    refine congrArg₂ m (Fin.ext ?_) (Fin.ext ?_)
    · show (3 * (j : ℕ) + i) / 3 = j
      omega
    · show (3 * (j : ℕ) + i) % 3 = i
      omega
  right_inv w := by
    funext k
    show wK (wK.symm (w _)) = w k
    rw [Equiv.apply_symm_apply]
    congr 1
    apply Fin.ext
    show 3 * ((k : ℕ) / 3) + (k : ℕ) % 3 = k
    omega

theorem masksEquiv_apply (m : Fin 4 → Fin 3 → K) (j : Fin 4) (i : Fin 3) (hk : 3 * (j : ℕ) + i < 12) :
    masksEquiv m ⟨3 * (j : ℕ) + i, hk⟩ = wK (m j i) := by
  show wK (m _ _) = _
  have := j.isLt
  have := i.isLt
  refine congrArg wK (congrArg₂ m (Fin.ext ?_) (Fin.ext ?_))
  · show (3 * (j : ℕ) + i) / 3 = j
    omega
  · show (3 * (j : ℕ) + i) % 3 = i
    omega

/-! ### The padding -/

/-- **The model's entry behind the statement's padding word `j` of lane `l`**: `j` itself, except on
the overflow lane `32` past its first piece, where the statement's stream skips the `held` pieces
the lane holds (`j ↦ j + held·2^8`) and its unread tail fills them
(`j ↦ j − (2^ℓ − held·2^8) + 2^8`). -/
def padSrc (ℓ held l j : ℕ) : ℕ :=
  if l = 32 ∧ 256 ≤ j then
    if j < 2 ^ ℓ - held * 256 then j + held * 256 else j - (2 ^ ℓ - held * 256) + 256
  else j

/-- The inverse of `padSrc`: the statement's padding word read at the model's entry `y` of lane `l`. -/
def padDst (ℓ held l y : ℕ) : ℕ :=
  if l = 32 ∧ 256 ≤ y then
    if y < 256 + held * 256 then y - 256 + (2 ^ ℓ - held * 256) else y - held * 256
  else y

theorem padSrc_lt {ℓ held : ℕ} (hH : 256 + held * 256 ≤ 2 ^ ℓ) (l : ℕ) {j : ℕ} (hj : j < 2 ^ ℓ) :
    padSrc ℓ held l j < 2 ^ ℓ := by
  unfold padSrc
  generalize 2 ^ ℓ = P at *
  split_ifs <;> omega

theorem padDst_lt {ℓ held : ℕ} (hH : 256 + held * 256 ≤ 2 ^ ℓ) (l : ℕ) {y : ℕ} (hy : y < 2 ^ ℓ) :
    padDst ℓ held l y < 2 ^ ℓ := by
  unfold padDst
  generalize 2 ^ ℓ = P at *
  split_ifs <;> omega

theorem padSrc_padDst {ℓ held : ℕ} (hH : 256 + held * 256 ≤ 2 ^ ℓ) (l : ℕ) {y : ℕ}
    (hy : y < 2 ^ ℓ) : padSrc ℓ held l (padDst ℓ held l y) = y := by
  unfold padSrc padDst
  generalize 2 ^ ℓ = P at *
  split_ifs <;> omega

theorem padDst_padSrc {ℓ held : ℕ} (hH : 256 + held * 256 ≤ 2 ^ ℓ) (l : ℕ) {j : ℕ}
    (hj : j < 2 ^ ℓ) : padDst ℓ held l (padSrc ℓ held l j) = j := by
  unfold padSrc padDst
  generalize 2 ^ ℓ = P at *
  split_ifs <;> omega

theorem idx_lt' {n P l j : ℕ} (hl : l < n) (hj : j < P) : l * P + j < n * P :=
  calc l * P + j < l * P + P := by omega
    _ = (l + 1) * P := by ring
    _ ≤ n * P := Nat.mul_le_mul_right _ hl

theorem div_idx {P l j : ℕ} (hj : j < P) : (l * P + j) / P = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

theorem mod_idx {P l j : ℕ} (hj : j < P) : (l * P + j) % P = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **A table's padding as words**, `n` lanes of `2^ℓ` entries: word `l · 2^ℓ + j` is the model's entry
`(l, padSrc ℓ held l j)`. -/
def padEquiv (n ℓ held : ℕ) {nι nY N : ℕ} (hι : nι = n) (hY : nY = 2 ^ ℓ) (hN : N = n * 2 ^ ℓ)
    (hH : 256 + held * 256 ≤ 2 ^ ℓ) : (Fin nι → Fin nY → K) ≃ (Fin N → W64) where
  toFun r k := wK (r ⟨k / 2 ^ ℓ, by
      rw [hι]; exact (Nat.div_lt_iff_lt_mul (by positivity)).2 (by rw [← hN]; exact k.isLt)⟩
    ⟨padSrc ℓ held (k / 2 ^ ℓ) (k % 2 ^ ℓ), by
      rw [hY]; exact padSrc_lt hH _ (Nat.mod_lt _ (by positivity))⟩)
  invFun w l y := wK.symm (w ⟨l * 2 ^ ℓ + padDst ℓ held l y, by
    rw [hN]
    exact idx_lt' (by rw [← hι]; exact l.isLt) (padDst_lt hH _ (by rw [← hY]; exact y.isLt))⟩)
  left_inv r := by
    funext l y
    have hy : (y : ℕ) < 2 ^ ℓ := by rw [← hY]; exact y.isLt
    have hd := padDst_lt hH l hy
    show wK.symm (wK (r _ _)) = r l y
    rw [Equiv.symm_apply_apply]
    refine congrArg₂ r (Fin.ext ?_) (Fin.ext ?_)
    · exact div_idx hd
    · show padSrc ℓ held ((l * 2 ^ ℓ + padDst ℓ held l y) / 2 ^ ℓ)
          ((l * 2 ^ ℓ + padDst ℓ held l y) % 2 ^ ℓ) = y
      rw [div_idx hd, mod_idx hd, padSrc_padDst hH l hy]
  right_inv w := by
    funext k
    have hk : (k : ℕ) % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ (by positivity)
    show wK (wK.symm (w _)) = w k
    rw [Equiv.apply_symm_apply]
    congr 1
    apply Fin.ext
    show (k : ℕ) / 2 ^ ℓ * 2 ^ ℓ +
        padDst ℓ held ((k : ℕ) / 2 ^ ℓ) (padSrc ℓ held ((k : ℕ) / 2 ^ ℓ) ((k : ℕ) % 2 ^ ℓ)) = k
    rw [padDst_padSrc hH _ hk]
    exact Nat.div_add_mod' k (2 ^ ℓ)

theorem padEquiv_apply (n ℓ held : ℕ) {nι nY N : ℕ} (hι : nι = n) (hY : nY = 2 ^ ℓ)
    (hN : N = n * 2 ^ ℓ) (hH : 256 + held * 256 ≤ 2 ^ ℓ) (r : Fin nι → Fin nY → K) (l j : ℕ)
    (hl : l < n) (hj : j < 2 ^ ℓ) (hk : l * 2 ^ ℓ + j < N) :
    padEquiv n ℓ held hι hY hN hH r ⟨l * 2 ^ ℓ + j, hk⟩ =
      wK (r ⟨l, by rw [hι]; exact hl⟩ ⟨padSrc ℓ held l j, by rw [hY]; exact padSrc_lt hH l hj⟩) := by
  show wK (r _ _) = _
  refine congrArg wK (congrArg₂ r (Fin.ext ?_) (Fin.ext ?_))
  · exact div_idx hj
  · show padSrc ℓ held ((l * 2 ^ ℓ + j) / 2 ^ ℓ) ((l * 2 ^ ℓ + j) % 2 ^ ℓ) = padSrc ℓ held l j
    rw [div_idx hj, mod_idx hj]

/-- `decodePadding` of the words of `c`, at a word of the table. -/
theorem decodePadding_ofFn (L : Layout) {N ℓ : ℕ} (hℓ : L.logLane = ℓ) (c : Fin N → W64)
    (l j : ℕ) (hk : l * 2 ^ ℓ + j < N) :
    decodePadding L ((List.ofFn c).map wordOf) l j = K.ofLane (wordOf (c ⟨l * 2 ^ ℓ + j, hk⟩)) := by
  subst hℓ
  exact congrArg K.ofLane (toArray_getD_map_ofFn c _ hk)

/-! ### The statement's layouts -/

theorem lanes_SW : (PcsQuotient.witnessLayout logRows).lanes.length = 40 := by decide +kernel
theorem lanes_SQ : (PcsQuotient.quotientLayout logRows).lanes.length = 63 := by decide +kernel
theorem logLane_SW : (PcsQuotient.witnessLayout logRows).logLane = 19 := by decide +kernel
theorem logLane_SQ : (PcsQuotient.quotientLayout logRows).logLane = 22 := by decide +kernel
theorem pieces_SW : (PcsQuotient.witnessLayout logRows).pieces.length = 33 := by decide +kernel
theorem pieces_SQ : (PcsQuotient.quotientLayout logRows).pieces.length = 167 := by decide +kernel
theorem logPiece_SW : (PcsQuotient.witnessLayout logRows).logPiece = some 8 := rfl
theorem logPiece_SQ : (PcsQuotient.quotientLayout logRows).logPiece = some 8 := rfl

/-- **The witness table's padding words**: `40` lanes of `2^19`. -/
theorem padWords_W : padWords (PcsQuotient.witnessLayout logRows) = 40 * 2 ^ 19 := by
  unfold padWords
  rw [lanes_SW, logLane_SW]

/-- **The quotient table's padding words**: `63` lanes of `2^22`. -/
theorem padWords_Q : padWords (PcsQuotient.quotientLayout logRows) = 63 * 2 ^ 22 := by
  unfold padWords
  rw [lanes_SQ, logLane_SQ]

/-! ### The bijection -/

/-- The witness table's padding (`40` lanes of `2^19`, `33` held pieces). -/
def padW : (QuotientZk.Instance.ιW → QuotientZk.Instance.YW → K) ≃
    (Fin (padWords (PcsQuotient.witnessLayout logRows)) → W64) :=
  padEquiv 40 19 33 QuotientZk.Instance.lanes_W (by rw [QuotientZk.Instance.logLane_W]) padWords_W
    (by norm_num)

/-- The quotient table's padding (`63` lanes of `2^22`, `167` held pieces). -/
def padQ : (QuotientZk.Instance.ιQ → QuotientZk.Instance.YQ → K) ≃
    (Fin (padWords (PcsQuotient.quotientLayout logRows)) → W64) :=
  padEquiv 63 22 167 QuotientZk.Instance.lanes_Q (by rw [QuotientZk.Instance.logLane_Q]) padWords_Q
    (by norm_num)

/-- **The skeleton model's randomness as the statement's coin words.** -/
def eDEquiv : QuotientZk.Instance.RandD K ≃ CoinWords :=
  Equiv.prodCongr masksEquiv (Equiv.prodCongr padW padQ)

/-- **The coins of the model's randomness** (`CoinsMatch (decodeCoins ∘ eD)`). -/
def eD : QuotientZk.Instance.RandD K → CoinWords := eDEquiv

/-- **`eD` is a bijection.** -/
theorem eD_bijective : Function.Bijective eD := eDEquiv.bijective

/-- **The decoded masks are the model's.** -/
theorem decodeCoins_eD_masks (s : QuotientZk.Instance.RandD K) : (decodeCoins (eD s)).1 = s.1 := by
  funext j i
  have hk : 3 * (j : ℕ) + i < 12 := by have := j.isLt; have := i.isLt; omega
  show K.ofLane (((List.ofFn (masksEquiv s.1)).map wordOf).getD (3 * (j : ℕ) + i) 0) = s.1 j i
  rw [getD_map_ofFn _ _ hk, masksEquiv_apply _ _ _ hk, ofLane_wordOf_w64]

/-- **The decoded witness padding**: the statement's `pad l j` is the model's entry
`(l, padSrc 19 33 l j)`. -/
theorem decodeCoins_eD_pad₁ (s : QuotientZk.Instance.RandD K) (l j : ℕ) (hl : l < 40)
    (hj : j < 2 ^ 19) :
    (decodeCoins (eD s)).2.1 l j =
      s.2.1 ⟨l, by rw [QuotientZk.Instance.lanes_W]; exact hl⟩
        ⟨padSrc 19 33 l j, by
          rw [QuotientZk.Instance.logLane_W]; exact padSrc_lt (by norm_num) l hj⟩ := by
  have hk : l * 2 ^ 19 + j < padWords (PcsQuotient.witnessLayout logRows) := by
    rw [padWords_W]; exact idx_lt' hl hj
  show decodePadding (PcsQuotient.witnessLayout logRows)
    ((List.ofFn (padW s.2.1)).map wordOf) l j = _
  rw [decodePadding_ofFn _ logLane_SW _ l j hk]
  exact (congrArg (fun w => K.ofLane (wordOf w))
    (padEquiv_apply 40 19 33 QuotientZk.Instance.lanes_W (by rw [QuotientZk.Instance.logLane_W])
      padWords_W (by norm_num) s.2.1 l j hl hj hk)).trans
      (ofLane_wordOf_w64 _)

/-- **The decoded quotient padding**: the statement's `pad l j` is the model's entry
`(l, padSrc 22 167 l j)`. -/
theorem decodeCoins_eD_pad₂ (s : QuotientZk.Instance.RandD K) (l j : ℕ) (hl : l < 63)
    (hj : j < 2 ^ 22) :
    (decodeCoins (eD s)).2.2 l j =
      s.2.2 ⟨l, by rw [QuotientZk.Instance.lanes_Q]; exact hl⟩
        ⟨padSrc 22 167 l j, by
          rw [QuotientZk.Instance.logLane_Q]; exact padSrc_lt (by norm_num) l hj⟩ := by
  have hk : l * 2 ^ 22 + j < padWords (PcsQuotient.quotientLayout logRows) := by
    rw [padWords_Q]; exact idx_lt' hl hj
  show decodePadding (PcsQuotient.quotientLayout logRows)
    ((List.ofFn (padQ s.2.2)).map wordOf) l j = _
  rw [decodePadding_ofFn _ logLane_SQ _ l j hk]
  exact (congrArg (fun w => K.ofLane (wordOf w))
    (padEquiv_apply 63 22 167 QuotientZk.Instance.lanes_Q (by rw [QuotientZk.Instance.logLane_Q])
      padWords_Q (by norm_num) s.2.2 l j hl hj hk)).trans
      (ofLane_wordOf_w64 _)

/-! ## Axioms -/

/-- info: 'PcsQuotient.EndToEnd.card_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_K

/-- info: 'PcsQuotient.EndToEnd.card_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_E

/--
info: 'PcsQuotient.EndToEnd.linIndep_Y' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms linIndep_Y

/--
info: 'PcsQuotient.EndToEnd.finrank_KE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms finrank_KE

/-- info: 'PcsQuotient.EndToEnd.wordsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wordsK

/--
info: 'PcsQuotient.EndToEnd.deployedRep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms deployedRep

/--
info: 'PcsQuotient.EndToEnd.inKD_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms inKD_iff

/--
info: 'PcsQuotient.EndToEnd.limbSysE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms limbSysE

/-- info: 'PcsQuotient.EndToEnd.ofLane_wordOf_w64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofLane_wordOf_w64

/--
info: 'PcsQuotient.EndToEnd.eD_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms eD_bijective

/-- info: 'PcsQuotient.EndToEnd.padWords_W' depends on axioms: [propext] -/
#guard_msgs in #print axioms padWords_W

/-- info: 'PcsQuotient.EndToEnd.padWords_Q' depends on axioms: [propext] -/
#guard_msgs in #print axioms padWords_Q

/--
info: 'PcsQuotient.EndToEnd.decodeCoins_eD_masks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms decodeCoins_eD_masks

/--
info: 'PcsQuotient.EndToEnd.decodeCoins_eD_pad₁' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms decodeCoins_eD_pad₁

/--
info: 'PcsQuotient.EndToEnd.decodeCoins_eD_pad₂' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms decodeCoins_eD_pad₂

end PcsQuotient.EndToEnd
