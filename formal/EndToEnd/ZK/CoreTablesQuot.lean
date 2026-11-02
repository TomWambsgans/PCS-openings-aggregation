-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoreTablesStack

/-!
# The quotient stack (`StackQ`)

The statement's quotient stack (`qStackD`, `E2ECompleteness.quotientStackOf`) is the quotient
layout's stack of `proveSpec`'s `quotientEntry` (`qEntryD`), and the joint model's that of F1's
honest quotient table (`TQD`, `quotTableD`). The two agree where the layout holds an entry, off the
degenerate `α, β`:

* `role_Q_held`: **a lane holds only the chunks' entries and the ends of their last pieces**
  (`quotientHeld`, `PastChunksQ`): a block lane's block lies in a chunk (`blocks_Q`), an overflow
  piece in a chunk's last pieces (`pieces_Q`), by the kernel on the `55` blocks and `167` pieces;
* `entry_Q`: there `proveSpec`'s entries are F1's honest quotient table
  (`E2ECompleteness.ProverQuotient.quotient_table`): its cells are the honest cells
  (`cells_getD`), satisfying the gates (`gate_honest`, for every witness), the wiring the deployed
  σ, `BadABD` is `BadAB` at the honest first message (`gOf`), which is the masked first message
  (`committed_eq`), and Completeness's table of its limbs is `quotTableD` (`quotTable_eq`);
* **`stackQ`**, with `stack_eq`, `fill_eq` (`CoreTablesStack.lean`); the relation is not needed.
-/

open Polynomial QuotientSecurity
open LeanVM.Parameters
open PcsQuotient.Domain
open QuotientZk.Instance
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## The statement's quotient entries -/

/-- **The statement's quotient entries** (`proveSpec`'s `quotientEntry`) of a witness, at the masks
`m` and the challenges `α, β, γ`. -/
noncomputable def qEntryD (w : Secret) (m : Masks) (abc : E × E × E) : ℕ → K :=
  E2ECompleteness.quotientEntry 22
    (coefficients 24 0 (E2ECompleteness.hValues 22 (E2ECompleteness.cellsOf w)
      (membership logRows).sigma abc.1 abc.2.1 abc.2.2))
    (coefficients 26 (betaAt 26)
      (E2ECompleteness.qValuesOf 22
        (E2ECompleteness.wValuesOf 22 (coefficients 24 0 (E2ECompleteness.cellsOf w))
          (maskEntries m))
        (E2ECompleteness.sigmaValuesOf 22
          (coefficients 24 0 ((membership logRows).sigma.map point)))
        (E2ECompleteness.q0Of 22 (coefficients 24 0 (E2ECompleteness.hValues 22
          (E2ECompleteness.cellsOf w) (membership logRows).sigma abc.1 abc.2.1 abc.2.2)))
        (E2ECompleteness.blocksOf 22 abc.2.2) abc.1 abc.2.1))
    (coefficients 26 (betaAt 26)
      (E2ECompleteness.qGateValuesOf 22
        (E2ECompleteness.wValuesOf 22 (coefficients 24 0 (E2ECompleteness.cellsOf w))
          (maskEntries m))
        (E2ECompleteness.blocksOf 22 abc.2.2)))

theorem wiringTable_eq :
    (membership logRows).wiringTable = coefficients 24 0 ((membership logRows).sigma.map point) := by
  rw [Circuit.wiringTable, Bridge.Setup.membership_logRows]
  rfl

/-- **The statement's quotient stack** is the quotient layout's stack of `qEntryD`. -/
theorem qStackD_eq (w : Secret) (c : Masks × Padding × Padding) (abc : E × E × E) :
    qStackD w c abc = (PcsQuotient.quotientLayout logRows).stackOf (qEntryD w c.1 abc) c.2.2 := by
  rw [qStackD, E2ECompleteness.quotientStackOf_eq, E2ECompleteness.quotientStack_eq,
    wiringTable_eq, Bridge.Setup.membership_logRows]
  rfl

/-- **The statement's quotient stack has `63` lanes of `2^22`.** -/
theorem size_qStackD (w : Secret) (c : Masks × Padding × Padding) (abc : E × E × E) :
    (qStackD w c abc).size = 63 * 2 ^ 22 := by
  rw [qStackD_eq, E2ECompleteness.stackOf_eq _ logPiece_SQ, E2ECompleteness.cancelGadget_size,
    Array.size_ofFn, List.size_toArray, lanes_SQ, logLane_SQ]

/-! ## F1's honest quotient table -/

/-- The honest first message of the honest cells is the masked first message. -/
theorem gOf_eq (w : Secret) (m : Masks) :
    E2ECompleteness.ProverQuotient.gOf
      (Completeness.cellBitsK Completeness.deployedMembership (E2ECompleteness.secretOf w)) m =
      committed (E := E) (gKD w) vanD m := by
  rw [committed_eq, ← cellsKD_eq]
  rfl

/-- **Completeness's quotient table of the honest second message is `quotTableD`.** -/
theorem quotTable_eq (w : Secret) (m : Masks) (abc : E × E × E) :
    Completeness.quotientTable Completeness.limbE (22 + 2 + 1 + 1)
        (QuotientSecurity.Params.honest Completeness.deployedInstanceE.params
          (E2ECompleteness.ProverQuotient.gOf
            (Completeness.cellBitsK Completeness.deployedMembership (E2ECompleteness.secretOf w)) m)
          abc.1 abc.2.1 abc.2.2)
        (Completeness.qGateKOf (QuotientSecurity.Params.honest
          Completeness.deployedInstanceE.params
          (E2ECompleteness.ProverQuotient.gOf
            (Completeness.cellBitsK Completeness.deployedMembership (E2ECompleteness.secretOf w)) m)
          abc.1 abc.2.1 abc.2.2)) =
      quotTableD w abc m := by
  rw [gOf_eq]
  rfl

/-! ## The entries a lane holds -/

/-- The quotient layout's block lanes lie in its chunks. -/
theorem blocks_Q : ∀ b ∈ LayoutClaims.laneBlocks Lq, ∃ c ∈ Completeness.qChunks,
    c.1 * 16777216 ≤ b * 4194304 ∧ b * 4194304 + 4194304 ≤ c.1 * 16777216 + c.2 := by
  decide +kernel

/-- Its overflow lane's pieces lie in its chunks' last pieces. -/
theorem pieces_Q : ∀ p ∈ Lq.pieces, ∃ c ∈ PcsQuotient.quotientChunks 24,
    c.1 * 16777216 ≤ p * 256 ∧ p * 256 + 256 ≤ c.1 * 16777216 + (c.2 + 255) / 256 * 256 := by
  decide +kernel

theorem qChunks_eq : PcsQuotient.quotientChunks 24 = Completeness.qChunks := by
  decide +kernel

/-- **A lane of the quotient layout holds only the chunks' entries and the ends of their last
pieces.** -/
theorem role_Q_held {a y i : ℕ} (hy : y < 2 ^ Lq.logLane)
    (hr : LayoutClaims.role Lq a y = some i) :
    Completeness.quotientHeld i ∨
      E2ECompleteness.PastChunksQ 24 8 (PcsQuotient.quotientChunks 24) i := by
  have e22 : (2 : ℕ) ^ Lq.logLane = 4194304 := by rw [logLane_Q]; norm_num
  have e8 : (2 : ℕ) ^ Hiding.Deployed.logPieceD = 256 := rfl
  have hheld : ∀ c ∈ Completeness.qChunks, ∀ j < c.2,
      Completeness.quotientHeld (c.1 * 16777216 + j) :=
    fun c hc j hj => ⟨c, hc, j, hj, rfl⟩
  rcases LayoutClaims.role_some okQ hr with ⟨b, hb, -, rfl⟩ | ⟨-, h1, h2, rfl⟩
  · left
    have hbm : b ∈ LayoutClaims.laneBlocks Lq :=
      LayoutClaims.mem_laneBlocks.mpr (List.mem_of_getElem? hb)
    obtain ⟨c, hc, hc1, hc2⟩ := blocks_Q b hbm
    rw [e22] at hy ⊢
    have := hheld c hc (b * 4194304 + y - c.1 * 16777216) (by omega)
    rwa [show c.1 * 16777216 + (b * 4194304 + y - c.1 * 16777216) = b * 4194304 + y by omega]
      at this
  · rw [e8] at h1 h2 ⊢
    have hk : y / 256 - 1 < Lq.pieces.length := by omega
    have hp : Lq.pieces.getD (y / 256 - 1) 0 ∈ Lq.pieces := by
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    obtain ⟨c, hc, hc1, hc2⟩ := pieces_Q _ hp
    have ho : y % 256 < 256 := Nat.mod_lt _ (by norm_num)
    generalize Lq.pieces.getD (y / 256 - 1) 0 = p at hc1 hc2 ⊢
    by_cases hj : p * 256 + y % 256 - c.1 * 16777216 < c.2
    · left
      have := hheld c (qChunks_eq ▸ hc) _ hj
      rwa [show c.1 * 16777216 + (p * 256 + y % 256 - c.1 * 16777216) = p * 256 + y % 256 by
        omega] at this
    · right
      have e8' : (2 : ℕ) ^ 8 = 256 := rfl
      have e24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
      refine ⟨c, hc, p * 256 + y % 256 - c.1 * 16777216, by omega, ?_, ?_⟩
      · rw [e8']
        omega
      · rw [e24]
        omega

/-- **Where a lane holds it, the statement's quotient entry is F1's honest table's**, off the
degenerate `α, β`. -/
theorem entry_Q (w : Secret) (m : Masks) (abc : E × E × E) (hbad : ¬ BadABD w m (abc.1, abc.2.1))
    {i : ℕ} (hi : Completeness.quotientHeld i ∨
      E2ECompleteness.PastChunksQ 24 8 (PcsQuotient.quotientChunks 24) i) :
    qEntryD w m abc i = natTableD (quotTableD w abc m) i := by
  have h := E2ECompleteness.ProverQuotient.quotient_table E2ECompleteness.constants
    (Completeness.cellBitsK Completeness.deployedMembership (E2ECompleteness.secretOf w))
    (E2ECompleteness.cellsOf w) (E2ECompleteness.cellsOf_size w)
    (E2ECompleteness.ProverCircuit.cells_getD w) (membership logRows).sigma
    E2ECompleteness.ProverCircuit.sigma_size E2ECompleteness.ProverCircuit.sigma_point m
    (E2ECompleteness.gate_honest w) abc.1 abc.2.1 abc.2.2 hbad i hi
  rw [← quotTable_eq]
  exact h

/-! ## The quotient stacks -/

/-- **The quotient stacks agree**, off the degenerate `α, β` (for every witness). -/
theorem stackQ : StackQ := by
  intro stmt w _ s abc hbad l y
  obtain ⟨l, hl⟩ := l
  obtain ⟨y, hy⟩ := y
  have hM : stackQm w abc s ⟨l, hl⟩ ⟨y, hy⟩ =
      Lq.hiddenWord (natTableD (quotTableD w abc s.1)) (rndOf s.2.2) l y := by
    refine Eq.trans ?_
      (Hiding.Deployed.Layout.hiddenWord_eq okQ _ (rndOf s.2.2) ⟨l, hl⟩ ⟨y, hy⟩).symm
    exact congrArg (fun r => ((Lq.toGadget okQ).stackD (TQD w abc s.1) +
      (Lq.toGadget okQ).stackR r) ⟨l, hl⟩ ⟨y, hy⟩) (rndOf_fin s.2.2).symm
  rw [hM]
  show _ = (qStackD w (decodeCoins (eD s)) abc).getD (l * 2 ^ 22 + y) 0
  rw [qStackD_eq, decodeCoins_eD_masks]
  have e22 : (2 : ℕ) ^ 22 = 2 ^ Lq.logLane := by rw [logLane_Q]
  rw [e22]
  have hlog : (PcsQuotient.quotientLayout logRows).logLane = Lq.logLane := by
    rw [logLane_SQ, logLane_Q]
  refine stack_eq okQ lanes_Q_tr hlog logPiece_SQ _ _ _ _ (fun a ha y' hy' => ?_) hl hy
  refine fill_eq okQ lanes_Q_tr pieces_Q_eq hlog _ _ _ _
    (fun _ _ _ _ hy hr => entry_Q w s.1 abc hbad (role_Q_held hy hr)) ?_ ?_ ha hy'
  · intro a ha y hy hn
    have ha' : a < 63 := by rwa [lanes_Q] at ha
    have hy'' : y < 2 ^ 22 := lt_of_lt_of_eq hy (by rw [logLane_Q])
    rw [decodeCoins_eD_pad₂ s a y ha' hy'', rndOf, dite_eq_left ⟨ha, hy⟩]
    refine fin2_congr s.2.2 rfl ?_ _ _ _ _
    unfold padSrc
    rw [ite_eq_right hn]
  · intro y hy hge
    have hy'' : y < 2 ^ 22 := lt_of_lt_of_eq hy (by rw [logLane_Q])
    rw [piecesLen_Q] at hge ⊢
    rw [decodeCoins_eD_pad₂ s 32 (y - 167 * 256) (by norm_num) (by omega), rndOf,
      dite_eq_left ⟨by rw [lanes_Q]; norm_num, hy⟩]
    refine fin2_congr s.2.2 rfl ?_ _ _ _ _
    unfold padSrc
    rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left (by norm_num; omega)]
    omega

end PcsQuotient.EndToEnd.Core
