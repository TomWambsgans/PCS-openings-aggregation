-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (F0a/F2/F4 review).
import QuotientSecurity.Statement
import WhirBridge.Sound

/-!
# Review: F0a's field hypotheses hold of the deployed field and constants

`soundness_circuit_bits` assumes `BitWeightsIndependent x Y` and `I.c = coordWeight x Y` of an abstract
field of `2^192` elements. Here they are discharged on mumbai's `E = BF64.Ext3`, the verifier's field
(`K[y]/(y^3 + y + 1)`, `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, the `F192` of `primitives`), with the
deployed constants: `x = g = F64(2)` (`F192::new(2, 0, 0)`) and `Y = y = F192::new(0, 1, 0)`.

* `bitWeight_eq_wt`: `bitWeight x Y j` is `F192::new(1 << j, 0, 0)` for `j < 64` and
  `F192::new(0, 1 << (j - 64), 0)` above, `protocol::bit_weight(j)`, limb for limb;
* `bitWeightsIndependent_E`: the 128 weights are independent over `GF(2)` (each is one coordinate bit);
* `soundness_circuit_bits_E`: `soundness_circuit_bits` on `E`, leaving only the circuit hypotheses
  (`Laid`) and the instance (its Cantor basis and wiring, which F0b must give).
-/

set_option linter.unusedSectionVars false

open QuotientSecurity LeanVM.Parameters OracleSpec OracleComp

namespace QuotientSecurity.Review

/-- `x`: `F64::G = F64(2)` in limb 0. -/
def xE : E := ofK g

/-- `Y`: `F192::Y`, the word `(0, 1, 0)`. -/
def YE : E := E.ofLimbs 0 1 0

/-- `protocol::bit_weight(j)` as limbs. -/
def wt (j : ℕ) : E :=
  if j < 64 then E.ofLimbs (K.ofBits (2 ^ j)) 0 0 else E.ofLimbs 0 (K.ofBits (2 ^ (j - 64))) 0

theorem wt_step : ∀ k : Fin 63, wt k * xE = wt (k + 1) := by decide +kernel

theorem wt_zero : wt 0 = 1 := by decide +kernel

theorem y_step : ∀ k : Fin 64, YE * wt k = wt (k + 64) := by decide +kernel

theorem xE_pow : ∀ k, k < 64 → xE ^ k = wt k
  | 0, _ => by rw [pow_zero, wt_zero]
  | k + 1, h => by
    rw [pow_succ, xE_pow k (by omega)]
    exact wt_step ⟨k, by omega⟩

/-- **`bitWeight x Y j` is `bit_weight(j)`.** -/
theorem bitWeight_eq_wt (j : ℕ) (hj : j < 128) : bitWeight xE YE j = wt j := by
  unfold bitWeight
  split_ifs with h
  · exact xE_pow j h
  · rw [xE_pow (j - 64) (by omega)]
    have := y_step ⟨j - 64, by omega⟩
    simp only at this
    rw [this, show j - 64 + 64 = j by omega]

/-- The limb holding coordinate bit `j`. -/
def limbIdx (j : ℕ) : Fin 3 := if j < 64 then 0 else 1

/-- Coordinate bit `j` of a word: bit `j mod 64` of limb `0` (`j < 64`) or limb `1`. -/
def coord (j : ℕ) (e : E) : Bool := (E.limb e (limbIdx j)).toBitVec.getLsbD (j % 64)

theorem coord_wt : ∀ j k : Fin 128, coord j (wt k) = decide (j = k) := by decide +kernel

theorem limb_add (a b : E) (i : Fin 3) : E.limb (a + b) i = E.limb a i + E.limb b i :=
  CompPoly.Extension.Ext.coeff_add a b i

theorem toBitVec_addK (a b : K) : (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

theorem coord_add (j : ℕ) (a b : E) : coord j (a + b) = xor (coord j a) (coord j b) := by
  unfold coord
  rw [limb_add, toBitVec_addK, BitVec.getLsbD_xor]

theorem coord_zero (j : ℕ) : coord j 0 = false := by
  have h := coord_add j 0 0
  rw [add_zero, Bool.xor_self] at h
  exact h

/-- The coordinate as an additive map to `ZMod 2`. -/
def coordHom (j : ℕ) : E →+ ZMod 2 where
  toFun e := if coord j e then 1 else 0
  map_zero' := by simp [coord_zero]
  map_add' a b := by
    simp only [coord_add]
    cases coord j a <;> cases coord j b <;> decide

/-- **The deployed bit weights are independent over `GF(2)`.** -/
theorem bitWeightsIndependent_E : BitWeightsIndependent xE YE := by
  intro a h j
  have h1 := congrArg (coordHom j) h
  rw [map_sum, map_zero] at h1
  have h2 : ∀ k : Fin 128, coordHom j (bitWeight xE YE k * bitF (a k)) =
      if a k ∧ j = k then 1 else 0 := by
    intro k
    rw [bitWeight_eq_wt k k.isLt]
    cases hk : a k
    · simp [bitF, map_zero]
    · simp only [bitF, ite_true, mul_one, true_and]
      show (if coord j (wt k) then (1 : ZMod 2) else 0) = _
      rw [coord_wt j k]
      by_cases hjk : j = k <;> simp [hjk]
  simp only [h2] at h1
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one] at h1
  by_contra hj
  have hfilt : Finset.univ.filter (fun k : Fin 128 => a k = true ∧ j = k) = {j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩; rfl
    · rintro rfl; exact ⟨by simpa using hj, rfl⟩
  rw [hfilt, Finset.card_singleton, Nat.cast_one] at h1
  exact one_ne_zero h1

theorem card_E : Fintype.card E = 2 ^ 192 := by
  have h := WhirBridge.card_E_ennreal
  exact_mod_cast h

/-- An instance on the deployed field with the deployed public weights exists for any wiring. -/
theorem exists_instance_E (wiring : Equiv.Perm (Fin (22 + 2) → Bool)) :
    ∃ I : Instance E, I.wiring = wiring ∧ I.c = coordWeight xE YE :=
  Instance.exists_instance card_E wiring _

/-- **`soundness_circuit_bits` on the deployed field and constants**: what is left is the circuit
(`C`, `Laid`) and the instance's basis and wiring. -/
theorem soundness_circuit_bits_E (I : Instance E) (hc : I.c = coordWeight xE YE)
    (C : ChiCircuit (Fin (2 ^ 22))) (hC : Laid I.wiring C) (adv : I.Adversary) (Q : ℕ)
    (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (QuotientSecurity.experiment adv)).run' ∅}[
        r.2 = true ∧ ∃ y root, r.1.stmt = statementWords xE YE y root ∧
          ¬ C.ProvesBits (I.cellsOf r.1.g.1) y root]
      ≤ (Q + 3 : ENNReal) / 2 ^ 128 :=
  I.soundness_circuit_bits card_E C bitWeightsIndependent_E hc hC adv Q hQ

/-- `statement::halves` on the deployed field: a half is `F192::new(v as u64, (v >> 64) as u64, 0)`,
checked on sample statements (`#eval`, below). -/
def halfRust (b : Fin 32 → UInt8) (h : Fin 2) : E :=
  E.ofLimbs (K.ofBits (halfValue b h % 2 ^ 64)) (K.ofBits (halfValue b h / 2 ^ 64 % 2 ^ 64)) 0

end QuotientSecurity.Review

open QuotientSecurity.Review in
#eval (List.range 8).all fun s =>
  let b : Fin 32 → UInt8 := fun i => ((37 * s + 101 * i.val * i.val + 13) % 256).toUInt8
  decide (half xE YE b 0 = halfRust b 0) && decide (half xE YE b 1 = halfRust b 1)

#print axioms QuotientSecurity.Review.bitWeightsIndependent_E
#print axioms QuotientSecurity.Review.soundness_circuit_bits_E
