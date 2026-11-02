-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (F0a/F2/F4 review),
-- now a corollary of the production module `QuotientSecurity/DeployedConcrete.lean` (F0c), which
-- proves these facts for `Primitives.F192` (the same type as mumbai's `E`, CompPoly's `BF64.Ext3`).
import QuotientSecurity.DeployedConcrete
import Statement.Field

/-!
# Review: F0a's field hypotheses hold of the deployed field and constants

`soundness_circuit_bits` assumes `BitWeightsIndependent x Y` and `I.c = coordWeight x Y` of an abstract
field of `2^192` elements. Here they are read on mumbai's `E = BF64.Ext3`, the verifier's field
(`K[y]/(y^3 + y + 1)`, `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, the `F192` of `primitives`), with the
deployed constants: `x = g = F64(2)` (`F192::new(2, 0, 0)`) and `Y = y = F192::new(0, 1, 0)`, which are
`F192.G` and `F192.Y` of `Field/F192.lean` (`xE_eq`, `YE_eq`). The proofs are F0c's
(`QuotientSecurity/DeployedConcrete.lean`):

* `bitWeight_eq_wt`: `bitWeight x Y j` is `F192::new(1 << j, 0, 0)` for `j < 64` and
  `F192::new(0, 1 << (j - 64), 0)` above, `protocol::bit_weight(j)`, limb for limb
  (`rustBitWeight_eq`);
* `bitWeightsIndependent_E`: the 128 weights are independent over `GF(2)` (`bitWeightsIndependent_G_Y`);
* `soundness_circuit_bits_E`: `soundness_circuit_bits` on `E`, leaving only the circuit hypotheses
  (`Laid`) and the instance (its Cantor basis and wiring); for the deployed circuit and wiring, with no
  hypothesis on the field, `Instance.soundness_membership_deployed_concrete`;
* `half_eq_halfRust`: `statement::halves` (`half_G_Y`).
-/

set_option linter.unusedSectionVars false

open QuotientSecurity LeanVM.Parameters OracleSpec OracleComp Primitives

namespace QuotientSecurity.Review

/-- `x`: `F64::G = F64(2)` in limb 0. -/
def xE : E := ofK g

/-- `Y`: `F192::Y`, the word `(0, 1, 0)`. -/
def YE : E := E.ofLimbs 0 1 0

theorem xE_eq : xE = F192.G := by decide +kernel

theorem YE_eq : YE = F192.Y := by decide +kernel

/-- `protocol::bit_weight(j)` as limbs. -/
def wt (j : ℕ) : E :=
  if j < 64 then E.ofLimbs (K.ofBits (2 ^ j)) 0 0 else E.ofLimbs 0 (K.ofBits (2 ^ (j - 64))) 0

theorem wt_eq (j : ℕ) (hj : j < 128) : wt j = rustBitWeight j := by
  unfold wt rustBitWeight
  split_ifs with h
  · rw [one_shiftLeft_toUInt64 j h, Nat.shiftLeft_eq, one_mul]; rfl
  · rw [one_shiftLeft_toUInt64 (j - 64) (by omega), Nat.shiftLeft_eq, one_mul]; rfl

/-- **`bitWeight x Y j` is `bit_weight(j)`.** -/
theorem bitWeight_eq_wt (j : ℕ) (hj : j < 128) : bitWeight xE YE j = wt j := by
  rw [xE_eq, YE_eq, wt_eq j hj, rustBitWeight_eq j hj]

/-- **The deployed bit weights are independent over `GF(2)`.** -/
theorem bitWeightsIndependent_E : BitWeightsIndependent xE YE := by
  rw [xE_eq, YE_eq]
  exact bitWeightsIndependent_G_Y

theorem card_E : Fintype.card E = 2 ^ 192 := F192.card

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

/-- `statement::halves` on the deployed field: a half is `F192::new(v as u64, (v >> 64) as u64, 0)`. -/
def halfRust (b : Fin 32 → UInt8) (h : Fin 2) : E :=
  E.ofLimbs (K.ofBits (halfValue b h % 2 ^ 64)) (K.ofBits (halfValue b h / 2 ^ 64 % 2 ^ 64)) 0

theorem half_eq_halfRust (b : Fin 32 → UInt8) (h : Fin 2) : half xE YE b h = halfRust b h := by
  rw [xE_eq, YE_eq, half_G_Y]
  show F192.ofLimbs (F64.ofNat (halfValue b h)) (F64.ofNat (halfValue b h >>> 64)) 0 =
    F192.ofLimbs (F64.ofNat (halfValue b h % 2 ^ 64)) (F64.ofNat (halfValue b h / 2 ^ 64 % 2 ^ 64)) 0
  rw [F64.ofNat_mod, F64.ofNat_mod, Nat.shiftRight_eq_div_pow]

end QuotientSecurity.Review

/-- info: 'QuotientSecurity.Review.bitWeightsIndependent_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Review.bitWeightsIndependent_E

/-- info: 'QuotientSecurity.Review.soundness_circuit_bits_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientSecurity.Review.soundness_circuit_bits_E
