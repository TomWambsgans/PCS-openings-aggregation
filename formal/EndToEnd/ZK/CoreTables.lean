-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR word `stackWordFast` and the bytes `kBytes` are leanerVM's (branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Ntt.lean`, `Statement/Field.lean`).
import ZK.CoreTablesCode
import ZK.CoreTablesQuot

/-!
# The deployed core's table parts

`CoreSpec.lean`'s statements about the two secret tables, proved:

* **`stackW`**, **`stackQ`** (`CoreTablesStack.lean`, `CoreTablesQuot.lean`): the joint model's stacks
  are the statement's arrays (`wStackD`, `qStackD` at the coins `decodeCoins (eD s)`), the quotient's
  off the degenerate `α, β` (the relation is not used: the honest cells satisfy the gates for every
  witness);
* **`codeW`**, **`codeQ`**, **`rowBytes_eq`** (`CoreTablesCode.lean`): the model's leaf at a position
  is the WHIR word's leaf (at every position), and its bytes are the words' little-endian bytes;
* the arrays' sizes, `size_wStackD`, `size_qStackD`;
* **`pbRow_W`**, **`pbRow_Q`**: hence the deployed prover's secret leaves (`PbRow`, branch `0` the
  witness table, branch `1` the quotient table at the challenges `α, β, γ` of the answers) are the
  bytes of the statement's WHIR words of its stacks.
-/

open Polynomial QuotientSecurity
open LeanVM.Parameters LeanVM.Protocol.KeccakHash LeanVM.Prover
open QuotientZk.Instance
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-- **The witness table's leaves are the bytes of the statement's WHIR word** of its witness stack,
at the positions below `2^20`, whatever the answers. -/
theorem pbRow_W (w : Secret) (s : RandD K) (h : List QuotientZk.Deployed.Out)
    (x : QuotientZk.Deployed.Pos) (hx : (x : ℕ) < 2 ^ 20) :
    PbRow deployedRep P₀D F192.Y (TWD w) (TQD w) s h 0 x =
      (stackWordFast 25 1 (wStackD w (decodeCoins (eD s))) x).flatMap kBytes := by
  have h64 : Lw.lanes.length ≤ 64 := by rw [lanes_W]; norm_num
  rw [PbRow_zero, stackV₁_eq, rowBytes_eq _ h64]
  exact congrArg (List.flatMap kBytes)
    (codeW (stackWm w s) _ (stackW w s) (size_wStackD w _) x hx)

/-- **The quotient table's leaves are the bytes of the statement's WHIR word** of its quotient stack
at the challenges `α, β, γ` of the answers, off the degenerate `α, β`. -/
theorem pbRow_Q (stmt : Statement) (w : Secret) (hw : Relation stmt w) (s : RandD K)
    (h : List QuotientZk.Deployed.Out) (x : QuotientZk.Deployed.Pos)
    (hbad : ¬ BadABD w s.1
      ((chOf deployedRep.limbs h).1.1.1.1, (chOf deployedRep.limbs h).1.1.1.2.1)) :
    PbRow deployedRep P₀D F192.Y (TWD w) (TQD w) s h 1 x =
      (stackWordFast 28 1 (qStackD w (decodeCoins (eD s)) (chOf deployedRep.limbs h).1.1.1)
        x).flatMap kBytes := by
  have h64 : Lq.lanes.length ≤ 64 := by rw [lanes_Q]; norm_num
  rw [PbRow_one, stackV₂_eq, rowBytes_eq _ h64]
  exact congrArg (List.flatMap kBytes)
    (codeQ (stackQm w (chOf deployedRep.limbs h).1.1.1 s) _ (stackQ stmt w hw s _ hbad)
      (size_qStackD w _ _) x x.isLt)

end PcsQuotient.EndToEnd.Core

/-! ## Axioms -/

/-- info: 'PcsQuotient.EndToEnd.Core.stackW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.stackW

/-- info: 'PcsQuotient.EndToEnd.Core.stackQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.stackQ

/-- info: 'PcsQuotient.EndToEnd.Core.codeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.codeW

/-- info: 'PcsQuotient.EndToEnd.Core.codeQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.codeQ

/--
info: 'PcsQuotient.EndToEnd.Core.rowBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.rowBytes_eq

/-- info: 'PcsQuotient.EndToEnd.Core.size_wStackD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.size_wStackD

/--
info: 'PcsQuotient.EndToEnd.Core.size_qStackD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.size_qStackD

/-- info: 'PcsQuotient.EndToEnd.Core.pbRow_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.pbRow_W

/-- info: 'PcsQuotient.EndToEnd.Core.pbRow_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.pbRow_Q
