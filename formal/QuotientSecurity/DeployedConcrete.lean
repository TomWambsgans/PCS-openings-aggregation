-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Deployed
import QuotientSecurity.CantorExists
import Field.F192

/-!
# The deployed end theorem over `F192`

`Instance.soundness_membership_deployed` holds over any field of `2^192` elements with bit weights
`bitWeight x Y` independent over `GF(2)`. This file discharges those hypotheses with the field of
`crates/primitives`, `F192` (`Field/F192.lean`: CompPoly's `BF64.Ext3`, `F64[y]/(y^3 + y + 1)` over
`F64 = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`), `x = F192.G = F192::new(2, 0, 0)` and
`Y = F192.Y = F192::new(0, 1, 0)`:

* `rustBitWeight_eq`: `quotient::protocol::bit_weight(j)` (`F192::new(1 << j, 0, 0)` for `j < 64`,
  `F192::new(0, 1 << (j - 64), 0)` above, transcribed as `rustBitWeight`) is `bitWeight G Y j`;
  `rustCoordinateWeight_eq`: `coordinate_weight(k)` (`rustCoordinateWeight`) is
  `some (coordWeight G Y k)` for `k < 8`, and `None` from 8 on (`rustCoordinateWeight_none`);
* `bitWeightsIndependent_G_Y`: the 128 weights are 128 distinct unit vectors of the limbs
  (`sum_bitWeight_G_Y`), so independent;
* `statementWords_G_Y`: `statementWords G Y` is `rustStatementWords`, `statement::halves`
  (`F192::new(v as u64, (v >> 64) as u64, 0)`, `v` a half read big-endian) and then `1, 0, 0, 0`;
* `Instance.soundness_membership_deployed_concrete`: the end theorem over `F192`, whose only
  hypotheses are on the instance (its weights `coordWeight G Y`, its wiring the deployed σ), the
  adversary and its query bound; `Instance.soundness_deployedInstance`: the same for
  `deployedInstance B`, any Cantor basis `B` (one exists, `nonempty_cantorBasis`).
-/

namespace QuotientSecurity

open Primitives Finset

/-- Uniform sampling of `F192`, by its enumeration. -/
noncomputable instance instSampleableTypeF192 : SampleableType F192 := SampleableType.ofFintype F192

/-- A Cantor basis of 24 vectors of `F192` exists (through `F64`, `exists_cantorBasis_big`). -/
theorem nonempty_cantorBasis : Nonempty (CantorBasis F192 (22 + 2)) :=
  exists_cantorBasis_big F192.card _ (by norm_num) (by norm_num)

/-! ## The bit weights -/

theorem bitWeight_G_Y_lo (j : ℕ) (hj : j < 64) : bitWeight F192.G F192.Y j = F192.ofF64 (F64.G ^ j) := by
  rw [bitWeight, ite_eq_left hj, F192.G_eq, F192.ofF64_pow]

theorem bitWeight_G_Y_hi (j : ℕ) (hj : 64 ≤ j) :
    bitWeight F192.G F192.Y j = F192.Y * F192.ofF64 (F64.G ^ (j - 64)) := by
  rw [bitWeight, ite_eq_right (by omega), F192.G_eq, F192.ofF64_pow]

/-- **A word's bits with their weights are the limbs**: bit `j < 64` is bit `j` of limb `c0`, bit
`64 + j` bit `j` of limb `c1`. -/
theorem sum_bitWeight_G_Y (a : Fin 128 → Bool) :
    ∑ j : Fin 128, bitWeight F192.G F192.Y j * bitF (a j) =
      F192.ofLimbs (∑ i : Fin 64, if a (Fin.castAdd 64 i) then F64.G ^ (i : ℕ) else 0)
        (∑ i : Fin 64, if a (Fin.natAdd 64 i) then F64.G ^ (i : ℕ) else 0) 0 := by
  have hsplit : ∑ j : Fin 128, bitWeight F192.G F192.Y j * bitF (a j)
      = ∑ i : Fin 64, bitWeight F192.G F192.Y (Fin.castAdd 64 i : ℕ) * bitF (a (Fin.castAdd 64 i))
        + ∑ i : Fin 64, bitWeight F192.G F192.Y (Fin.natAdd 64 i : ℕ) *
            bitF (a (Fin.natAdd 64 i)) :=
    Fin.sum_univ_add (a := 64) (b := 64) fun j => bitWeight F192.G F192.Y j * bitF (a j)
  rw [hsplit, F192.ofLimbs_eq, F192.ofF64_zero, zero_mul, add_zero, F192.ofF64_sum,
    F192.ofF64_sum, Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_castAdd, bitWeight_G_Y_lo i i.isLt]
    cases a (Fin.castAdd 64 i) <;> simp [bitF]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_natAdd, bitWeight_G_Y_hi (64 + i) (by omega), show 64 + (i : ℕ) - 64 = i by omega]
    cases a (Fin.natAdd 64 i) <;> simp [bitF, mul_comm]

/-- **The bit weights of `F192` are independent over `GF(2)`.** -/
theorem bitWeightsIndependent_G_Y : BitWeightsIndependent F192.G F192.Y := by
  intro a h j
  rw [sum_bitWeight_G_Y, F192.zero_eq] at h
  obtain ⟨h0, h1, -⟩ := F192.ofLimbs_injective h
  by_cases hj : (j : ℕ) < 64
  · have := F64.bits_eq_false _ h0 ⟨j, hj⟩
    have e : Fin.castAdd 64 (⟨j, hj⟩ : Fin 64) = j := Fin.ext rfl
    rwa [e] at this
  · have := F64.bits_eq_false _ h1 ⟨j - 64, by omega⟩
    have e : Fin.natAdd 64 (⟨j - 64, by omega⟩ : Fin 64) = j := Fin.ext (by simp; omega)
    rwa [e] at this

/-! ## `bit_weight` and `coordinate_weight` of `quotient::protocol` -/

/-- **`quotient::protocol::bit_weight`**, transcribed: `F192::new(1 << j, 0, 0)` for `j < 64`,
`F192::new(0, 1 << (j - 64), 0)` above. -/
def rustBitWeight (j : ℕ) : F192 :=
  if j < 64 then F192.new (1 <<< j.toUInt64) 0 0 else F192.new 0 (1 <<< (j - 64).toUInt64) 0

/-- **`quotient::protocol::coordinate_weight`**, transcribed: `bit_weight(1)` for coordinate 0,
`F192::ZERO` for 1, `bit_weight(1 << (k - 1))` for `2..8`, and `None` (a power of `gamma`) from 8
on. -/
def rustCoordinateWeight (k : ℕ) : Option F192 :=
  if k = 0 then some (rustBitWeight 1) else if k = 1 then some 0
  else if k < 8 then some (rustBitWeight (1 <<< (k - 1))) else none

theorem one_shiftLeft_toUInt64 (j : ℕ) (hj : j < 64) :
    (1 : UInt64) <<< j.toUInt64 = UInt64.ofNat (1 <<< j) :=
  (by decide +kernel : ∀ j : Fin 64, (1 : UInt64) <<< (j : ℕ).toUInt64 = UInt64.ofNat (1 <<< (j : ℕ)))
    ⟨j, hj⟩

/-- `F192::new(1 << j, 0, 0)` is `x^j`. -/
theorem new_one_shiftLeft (j : ℕ) (hj : j < 64) : F192.new (1 <<< j.toUInt64) 0 0 = F192.G ^ j := by
  rw [one_shiftLeft_toUInt64 j hj, ← F192.ofF64_ofU64, F64.ofU64_ofNat, ← F64.G_pow j hj,
    F192.ofF64_pow, ← F192.G_eq]

/-- **`bit_weight(j)` is `bitWeight G Y j`.** -/
theorem rustBitWeight_eq (j : ℕ) (hj : j < 128) : rustBitWeight j = bitWeight F192.G F192.Y j := by
  unfold rustBitWeight bitWeight
  by_cases h : j < 64
  · rw [ite_eq_left h, ite_eq_left h, new_one_shiftLeft j h]
  · rw [ite_eq_right h, ite_eq_right h, ← new_one_shiftLeft (j - 64) (by omega)]
    rw [← F192.ofF64_ofU64, F192.Y_mul_ofF64]
    rfl

/-- **`coordinate_weight(k)` is `coordWeight G Y k`** for `k < 8`, the instance's weights. -/
theorem rustCoordinateWeight_eq (k : ℕ) (hk : k < 8) :
    rustCoordinateWeight k = some (coordWeight F192.G F192.Y k) := by
  unfold rustCoordinateWeight coordWeight
  by_cases h0 : k = 0
  · rw [ite_eq_left h0, ite_eq_left h0, rustBitWeight_eq 1 (by norm_num)]
  by_cases h1 : k = 1
  · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_left h1, ite_eq_left h1]
  rw [ite_eq_right h0, ite_eq_right h0, ite_eq_right h1, ite_eq_right h1, ite_eq_left hk,
    Nat.shiftLeft_eq, one_mul, rustBitWeight_eq _ ?_]
  calc 2 ^ (k - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < 128 := by norm_num

/-- From coordinate 8 on, `coordinate_weight` is `None`: those coordinates take powers of `gamma`
(`regionMu`). -/
theorem rustCoordinateWeight_none (k : ℕ) (hk : 8 ≤ k) : rustCoordinateWeight k = none := by
  unfold rustCoordinateWeight
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The statement's words -/

/-- **`statement::halves`**, one half: `v = u128::from_be_bytes(bytes[16 h..16 h + 16])`
(`halfValue`), then `F192::new(v as u64, (v >> 64) as u64, 0)`. -/
def rustHalf (b : Fin 32 → UInt8) (h : Fin 2) : F192 :=
  F192.new (UInt64.ofNat (halfValue b h)) (UInt64.ofNat (halfValue b h >>> 64)) 0

/-- **The verifier's eight public words for `(y, root)`**: `Statement::halves` (`y` then `root`),
then `1, 0, 0, 0` (`reduce`'s target adds `gamma^4`). -/
def rustStatementWords (y root : Fin 32 → UInt8) : Fin 8 → F192 :=
  ![rustHalf y 0, rustHalf y 1, rustHalf root 0, rustHalf root 1, 1, 0, 0, 0]

/-- `limb x n` at `x = F192.G` is the word `n`. -/
theorem limb_G (n : ℕ) : limb F192.G n = F192.ofF64 (F64.ofNat n) := by
  unfold limb
  rw [← F64.sum_testBit, F192.ofF64_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_ite F192.ofF64, F192.ofF64_zero, F192.ofF64_pow, ← F192.G_eq]

/-- **A half of the statement is `statement::halves`'s.** -/
theorem half_G_Y (b : Fin 32 → UInt8) (h : Fin 2) : half F192.G F192.Y b h = rustHalf b h := by
  unfold half rustHalf
  rw [limb_G, limb_G, F64.ofNat_mod, F64.ofNat_mod, F192.Y_mul_ofF64, F192.ofF64_eq,
    F192.ofLimbs_add_ofLimbs, Nat.shiftRight_eq_div_pow]
  simp only [add_zero, zero_add]
  rfl

/-- **The statement's words are the Rust verifier's.** -/
theorem statementWords_G_Y : statementWords F192.G F192.Y = rustStatementWords := by
  funext y root J
  fin_cases J <;> simp [statementWords, halves, rustStatementWords, half_G_Y]

/-! ## The end theorem over `F192` -/

open OracleSpec OracleComp

/-- **The deployed instance over `F192`**: a Cantor basis `B`, the deployed σ, and
`coordinate_weight`'s weights. -/
noncomputable def deployedInstance (B : CantorBasis F192 (22 + 2)) : Instance F192 :=
  ⟨B, deployedSigma, coordWeight F192.G F192.Y⟩

namespace Instance

/-- **Knowledge soundness of the deployed membership proof over `F192`.** For an instance over
`crates/primitives`'s field `F192`, with `coordinate_weight`'s weights (`coordWeight G Y`,
`rustCoordinateWeight_eq`) and the deployed wiring (`membership.sigma`, the Rust's): for every
adversary making at most `Q` oracle queries, the probability that the verdict is true for the
verifier's public words of some `(y, root)` (`rustStatementWords`: `Statement::halves`, then
`1, 0, 0, 0`) while the proof's cells are not a computation of the deployed circuit whose input
bits are a secret `s` with `H(s.x ‖ 0x11^32) = y` and the Merkle path of `s` from
`H(s.x ‖ 0x22^32)` ending at `root` (`ProvesMembership`, `H` leanerVM's Keccak-256), is at most
`(Q + 3) / 2^128`. -/
theorem soundness_membership_deployed_concrete (I : Instance F192)
    (hc : I.c = coordWeight F192.G F192.Y) (hw : I.wiring = deployedSigma)
    (adv : I.Adversary) (Q : ℕ) (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experiment adv)).run' ∅}[
        r.2 = true ∧ ∃ y root, r.1.stmt = rustStatementWords y root ∧
          ¬ ProvesMembership (I.cellsOf r.1.g.1) y root]
      ≤ (Q + 3 : ENNReal) / 2 ^ 128 := by
  rw [← statementWords_G_Y]
  exact I.soundness_membership_deployed F192.card bitWeightsIndependent_G_Y hc hw adv Q hQ

/-- **The same for `deployedInstance B`**: no hypothesis but the adversary's query bound. -/
theorem soundness_deployedInstance (B : CantorBasis F192 (22 + 2))
    (adv : (deployedInstance B).Adversary) (Q : ℕ) (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experiment adv)).run' ∅}[
        r.2 = true ∧ ∃ y root, r.1.stmt = rustStatementWords y root ∧
          ¬ ProvesMembership ((deployedInstance B).cellsOf r.1.g.1) y root]
      ≤ (Q + 3 : ENNReal) / 2 ^ 128 :=
  soundness_membership_deployed_concrete _ rfl rfl adv Q hQ

end Instance

end QuotientSecurity
