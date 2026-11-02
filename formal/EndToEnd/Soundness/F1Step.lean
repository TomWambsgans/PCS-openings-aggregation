-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.Hypotheses

/-!
# A satisfying assignment proves membership; the reduction's own check

Two facts about F1's instance `inst c h` (`Hypotheses.lean`) that the end theorem needs, proved
from F0's and F1's theorems and the two transcriptions of `quotient::protocol`'s constants
(`Compose/Reduce.lean`'s, `QuotientSecurity/DeployedConcrete.lean`'s):

* **`provesMembership_of_sat`**: a first message whose cells satisfy F1's relation (`Params.Sat`)
  for the statement the deployed wire reads off `y ‖ root` holds a computation of the deployed
  circuit proving membership of `(y, root)` (`ProvesMembership`): F1's `relation_of_sat`, F0b's
  `proves_of_relation_statement` (the deployed circuit `deployed` laid by its wiring,
  `deployed_laid_sigma`), F0c's `Proves.bits` (the bit weights of `F192` independent,
  `bitWeightsIndependent_G_Y`) and `ProvesBits.membership`. The wire's words (`stmtWords`) are
  F0c's (`statementWords G Y`, `stmtWords_eq`), and `reduce`'s `coordinate_weight` is F0c's
  (`coordinateWeight_eq`).
* **`reductionCheck_of_reduce`**: when `reduce` does not reject, the reduction's own check holds
  (`AcceptedV`'s first conjunct): the product it inverts is one of `reduce`'s denominators.
-/

set_option linter.unusedSectionVars false

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash WhirBridge Primitives

/-! ## The two transcriptions of the constants -/

theorem ofBits_eq_ofU64 (n : ℕ) : K.ofBits n = F64.ofU64 (UInt64.ofNat n) := rfl

/-- `reduce`'s `bit_weight` is F0c's (`rustBitWeight`). -/
theorem bitWeight_eq_rust (j : ℕ) (hj128 : j < 128) : Reduce.bitWeight j = rustBitWeight j := by
  unfold Reduce.bitWeight rustBitWeight
  by_cases hj : j < 64
  · simp only [hj, ↓reduceIte]
    rw [one_shiftLeft_toUInt64 j hj]
    rfl
  · simp only [hj, ↓reduceIte]
    rw [one_shiftLeft_toUInt64 (j - 64) (by omega)]
    rfl

/-- `reduce`'s `coordinate_weight` is F0c's below `8`. -/
theorem coordinateWeight_eq (k : ℕ) (hk : k < 8) :
    Reduce.coordinateWeight k = some (coordWeight F192.G F192.Y k) := by
  rw [← rustCoordinateWeight_eq k hk]
  have hb : ∀ k, k < 8 → 1 <<< (k - 1) < 128 := fun k hk => by
    rw [Nat.shiftLeft_eq, one_mul]
    calc 2 ^ (k - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 128 := by norm_num
  unfold Reduce.coordinateWeight rustCoordinateWeight
  simp only [bitWeight_eq_rust 1 (by norm_num), bitWeight_eq_rust _ (hb k hk)]

theorem ofNat_mod (n : ℕ) : UInt64.ofNat (n % 2 ^ 64) = UInt64.ofNat n :=
  UInt64.toNat_inj.mp (by simp)

theorem ofLimbs_eq_new (v : ℕ) :
    E.ofLimbs (K.ofBits (v % 2 ^ 64)) (K.ofBits (v >>> 64)) 0 =
      F192.new (UInt64.ofNat v) (UInt64.ofNat (v >>> 64)) 0 := by
  rw [ofBits_eq_ofU64, ofNat_mod, ofBits_eq_ofU64]
  rfl

/-- `reduce`'s half of the statement is F0c's (`rustHalf`). -/
theorem stmtHalf_eq_rust (b : Fin 32 → UInt8) (h : Fin 2) : stmtHalf b h = rustHalf b h := by
  unfold stmtHalf rustHalf
  exact ofLimbs_eq_new _

/-- **The wire's words are F0c's**: `stmtWords` of `y ‖ root` is `statementWords G Y y root`. -/
theorem stmtWords_eq (sb : Vector UInt8 64) :
    stmtWords sb = statementWords F192.G F192.Y (yOf sb) (Reduce.rootOf sb) := by
  rw [statementWords_G_Y]
  funext J
  fin_cases J <;> simp [stmtWords, stmtHalves, rustStatementWords, stmtHalf_eq_rust]

theorem yOf_append (y root : Vector UInt8 32) : yOf (y ++ root) = fun i => y.get i := by
  funext i
  simp only [yOf, Vector.get, Fin.cast]
  exact Vector.getElem_append_left i.2

theorem rootOf_append (y root : Vector UInt8 32) :
    Reduce.rootOf (y ++ root) = fun i => root.get i := by
  funext i
  simp only [Reduce.rootOf, Vector.get, Fin.cast]
  have h := Vector.getElem_append_right (xs := y) (ys := root) (i := 32 + (i : ℕ)) (by omega)
    (by omega)
  simpa using h

theorem yOf_stmtBytes (stmt : PcsQuotient.Statement) :
    yOf (stmtBytes stmt) = fun i => stmt.y.get i := yOf_append _ _

theorem rootOf_stmtBytes (stmt : PcsQuotient.Statement) :
    Reduce.rootOf (stmtBytes stmt) = fun i => stmt.root.get i := rootOf_append _ _

/-! ## A satisfying assignment proves membership -/

variable (c : Consts) (h : IsCantor c.beta)

/-- **A first message satisfying F1's relation for the statement's words proves membership** of
its `(y, root)`: its cells hold a computation of the deployed circuit whose input bits are a secret
with `H(x ‖ 0x11^32) = y` and the path from `H(x ‖ 0x22^32)` ending at `root`. -/
theorem provesMembership_of_sat (stmt : PcsQuotient.Statement) (g : Params.Witness E)
    (hs : (inst c h).params.Sat ((deployedWire (inst c h)).decode (stmtBytes stmt))
      ((inst c h).params.cells g)) :
    ProvesMembership ((inst c h).cellsOf g) (fun i => stmt.y.get i) (fun i => stmt.root.get i) := by
  have hrel := (inst c h).relation_of_sat _ g hs
  rw [deployedWire_decode, stmtWords_eq, yOf_stmtBytes, rootOf_stmtBytes] at hrel
  have hind := bitWeightsIndependent_G_Y
  exact ProvesBits.membership (((inst c h).proves_of_relation_statement deployed hind.ne_one.1
    hind.ne_one.2 rfl deployed_laid_sigma _ _ _ hrel).bits hind)

/-! ## The reduction's own check -/

/-- **When `reduce` does not reject, the reduction's own check holds** for an instance whose `θ`
is `beta()[1]` and whose rows' vanishing polynomial is `reduce`'s (`Matches`). -/
theorem reductionCheck_of_reduce {P : Params E} (hM : Matches P c 22) (π : RootProof E)
    (ch : Chals E) {x : Reduced} (hx : reduceOf c 22 π ch = some x) :
    reductionCheck P ch.α ch.β ch.t π.v.1 π.v.2 := by
  obtain ⟨hnz, -⟩ := reduce_eq_some hx
  obtain ⟨-, hcopy, hrows⟩ := prod_denominators_ne_zero hnz
  unfold reductionCheck
  simp only
  rw [hM.vCells, digitPoly_eval, hM.rows, ← rowCells_eq c P hM.theta]
  exact mul_ne_zero hcopy hrows

end Soundness
