-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.ProverAccept
import Bridge.Facts
import Bridge.Circuit.Outputs

/-!
# The prover bridge's circuit: the Statement's cells and wiring are F0b's

**`circuitMatch`** (`CircuitMatch`, `ProverAccept.lean`): the Statement's membership circuit's
cells of a witness are `formal/Completeness`'s honest cells, and its wiring's points are the
deployed σ's. Everything goes through `Bridge/Circuit`'s equalities (which never evaluate the
`2^22`-row circuit):

* **the cells** (`cells_getD`): `Bridge.Circuit.membership_cells` gives the Statement's cells as F0b's
  cell bits (`cellBitC`) of `PcsCircuit.Circuit.outputs` on the input bits of `secretTr w`, which is
  `(secretOf w).toPcs` (`secretTr_eq`); a cell bit is the bit of what the cell carries
  (`cellBitC_eq_carried`), every source a constant or a row of the circuit
  (`Bridge.Circuit.membership_slots`), on which `Circuit.outputs` is `deployedAssign`
  (`deployedAssign_eq_outputs`); and what cell `n` of `deployed` carries is that source
  (`deployed_cellSrc_cellOf`);
* **the wiring** (`sigma_point`): the Statement's σ is F0b's (`Bridge.Circuit.membership_sigma`),
  `deployedSigma` moves cell `n` to cell `σ[n]` (`deployedSigma_cellOf`), and the Statement's point of
  `p < 2^24` is the deployed basis's point of `p`'s bits (`point_eq_deployed`: `Bridge.Ntt`'s
  `point_eq_cantor`, the statement's first `24` basis vectors being `deployedBasis`'s,
  `Bridge.betaAt_eq_deployedBasis`);
* **the size** (`sigma_size`): F0b's σ has `2^24` entries (`Bridge.Setup.pcsCircuit_sigma_size`).
-/

open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness

-- The circuits are closed terms of `2^22` rows: nothing below may unfold them.
attribute [local irreducible] PcsQuotient.membership PcsCircuit.membership
  PcsQuotient.membershipBuilder PcsCircuit.membershipBuild

namespace ProverCircuit

/-! ## The secret -/

theorem ofFn_getElem_vector {α : Type} {n : ℕ} (v : Vector α n) :
    List.ofFn (fun i : Fin n => v[i]) = v.toList := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp

/-- **The two readings of a Statement secret as F0b's agree**: `Bridge`'s `secretTr` and
`formal/Completeness`'s `Secret.toPcs` of `secretOf`. -/
theorem secretTr_eq (w : PcsQuotient.Secret) : Bridge.Circuit.secretTr w = (secretOf w).toPcs := by
  obtain ⟨x, sib, dir⟩ := w
  have hx : x.toList = List.ofFn (secretOf ⟨x, sib, dir⟩).x := (ofFn_getElem_vector x).symm
  have hs : sib.toList.map Vector.toList =
      List.ofFn fun i : Fin 32 => List.ofFn ((secretOf ⟨x, sib, dir⟩).siblings i) := by
    apply List.ext_getElem (by rw [List.length_map, List.length_ofFn]; exact Vector.length_toList)
    intro k h1 h2
    simp only [List.getElem_map, Vector.getElem_toList, List.getElem_ofFn]
    rw [← ofFn_getElem_vector]
    rfl
  have hd : dir.toList = List.ofFn (secretOf ⟨x, sib, dir⟩).directions := by
    apply List.ext_getElem (by rw [List.length_ofFn]; exact Vector.length_toList)
    intro k h1 h2
    simp only [Vector.getElem_toList, List.getElem_ofFn]
    rfl
  show PcsCircuit.Secret.mk _ _ _ = PcsCircuit.Secret.mk _ _ _
  rw [hx, hs, hd]
  rfl

/-! ## The cells -/

/-- **A cell bit is the bit of what the cell carries**, for every circuit and outputs. -/
theorem cellBitC_eq_carried (c : PcsCircuit.Circuit) (v : Array Bool) (i : ℕ) :
    Bridge.Circuit.cellBitC c v i = PcsCircuit.readBit v (PcsCircuit.carried c.rows i) := by
  unfold Bridge.Circuit.cellBitC PcsCircuit.carried
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;>
    simp [h, PcsCircuit.readBit]

theorem two_pow_24 : (2 : ℕ) ^ (22 + 2) = 16777216 := by norm_num

theorem two_pow_22 : (2 : ℕ) ^ 22 = 4194304 := by norm_num

/-- What a cell of `membership` carries is a constant or a row of the circuit. -/
theorem slot_carried_lt {n : ℕ} (hn : n < 2 ^ (22 + 2)) :
    PcsCircuit.slot (PcsCircuit.carried PcsCircuit.membership.rows n) < 2 ^ 22 + 2 := by
  have hr : n / 4 < 2 ^ 22 := by rw [two_pow_24] at hn; rw [two_pow_22]; omega
  obtain ⟨hx, hy, hc⟩ := Bridge.Circuit.membership_slots (n / 4) hr
  unfold PcsCircuit.carried
  split_ifs
  · exact hx
  · exact hy
  · exact hc
  · show 2 + n / 4 < 2 ^ 22 + 2
    omega

theorem readBit_row (v : Array Bool) (r : ℕ) : PcsCircuit.readBit v (.row r) = v.getD r false :=
  rfl

theorem read_row (f : ℕ → Bool) (r : ℕ) : PcsCircuit.read f (.row r) = f r := rfl

theorem bitF_eq (x : Bool) : (bitF x : LeanVM.Parameters.K) = if x then 1 else 0 := rfl

/-- **On a constant or a row of the circuit, `Circuit.outputs` reads what `deployedAssign` reads.** -/
theorem readBit_eq (s : PcsCircuit.Secret) (src : PcsCircuit.Src)
    (h : PcsCircuit.slot src < 2 ^ 22 + 2) :
    PcsCircuit.readBit (PcsCircuit.Circuit.outputs PcsCircuit.membership s.inputs) src =
      PcsCircuit.read (natVal (deployedAssign s)) src := by
  cases src with
  | zero => rfl
  | one => rfl
  | row r =>
    have hr : r < 2 ^ 22 := by simp only [PcsCircuit.slot] at h; omega
    rw [readBit_row, read_row, natVal, dite_eq_left hr, deployedAssign_eq_outputs]

/-- The Statement's membership circuit has `2^22` rows. -/
theorem rows_size : (PcsQuotient.membership 22).rows.size = 2 ^ 22 := by
  have h := congrArg Array.size Bridge.Circuit.membership_rows
  rw [Array.size_map, PcsCircuit.membership_rows_size] at h
  exact h

/-- **The Statement's cells of a witness are `formal/Completeness`'s honest cells.** -/
theorem cells_getD (w : PcsQuotient.Secret) (b : Fin (22 + 2) → Bool) :
    (cellsOf w).getD (Completeness.idx b) 0 =
      Completeness.cellBitsK Completeness.deployedMembership (secretOf w) b := by
  have hcells : cellsOf w =
      PcsQuotient.Circuit.cells (PcsQuotient.membership 22) (PcsQuotient.membershipInputs w) := rfl
  have hn : Completeness.idx b < 2 ^ (22 + 2) := Completeness.idx_lt b
  have hlt : Completeness.idx b < 4 * (PcsQuotient.membership 22).rows.size := by
    rw [rows_size]
    rw [two_pow_24] at hn
    rw [two_pow_22]
    omega
  rw [hcells, Bridge.Circuit.membership_cells, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    dite_eq_left hlt, Option.getD_some, secretTr_eq]
  show _ = bitF ((deployed.cellSrc b).bval (deployedAssign (secretOf w).toPcs))
  conv_rhs => rw [← Bridge.Setup.cellOf_idx b]
  rw [deployed_cellSrc_cellOf hn, bval_ofSrc, cellBitC_eq_carried,
    readBit_eq _ _ (slot_carried_lt hn), bitF_eq]

/-! ## The wiring -/

/-- The statement's first `24` basis vectors are a Cantor basis (they are `deployedBasis`'s). -/
theorem cantorUpTo24 : Bridge.Ntt.CantorUpTo 24 :=
  ⟨by rw [Bridge.betaAt_eq_deployedBasis 0 (by norm_num)]; exact deployedBasis.zero,
    fun k hk => by
      rw [Bridge.betaAt_eq_deployedBasis (k + 1) hk, Bridge.betaAt_eq_deployedBasis k (by omega)]
      exact deployedBasis.succ k hk⟩

/-- **The Statement's point of `p < 2^24` is the deployed basis's point of `p`'s bits.** -/
theorem point_eq_deployed {p : ℕ} (hp : p < 2 ^ (22 + 2)) :
    PcsQuotient.Domain.point p = deployedBasis.point (cellOf p) := by
  rw [Bridge.Ntt.point_eq_cantor cantorUpTo24 (by decide) hp]
  unfold CantorBasis.point
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (Bridge.Ntt.cantorOf cantorUpTo24).β j = PcsQuotient.Domain.betaAt j from rfl,
    Bridge.betaAt_eq_deployedBasis j j.isLt]
  rfl

/-- **The Statement's wiring's points are the deployed σ's.** -/
theorem sigma_point (b : Fin (22 + 2) → Bool) :
    PcsQuotient.Domain.point
        ((PcsQuotient.membership PcsQuotient.logRows).sigma.getD (Completeness.idx b) 0) =
      deployedBasis.point (deployedSigma b) := by
  have hσ : (PcsQuotient.membership PcsQuotient.logRows).sigma = PcsCircuit.membership.sigma :=
    Bridge.Circuit.membership_sigma
  have hn : Completeness.idx b < 2 ^ (22 + 2) := Completeness.idx_lt b
  have hm : PcsCircuit.membership.sigma.getD (Completeness.idx b) 0 < 2 ^ (22 + 2) := by
    have h := PcsCircuit.membership_sigma_lt (Completeness.idx b) (by rw [four_mul_rows]; exact hn)
    rwa [four_mul_rows] at h
  rw [hσ, point_eq_deployed hm, ← deployedSigma_cellOf hn, Bridge.Setup.cellOf_idx]

/-- **The Statement's σ has `2^24` entries.** -/
theorem sigma_size : (PcsQuotient.membership PcsQuotient.logRows).sigma.size = 2 ^ 24 := by
  have hσ : (PcsQuotient.membership PcsQuotient.logRows).sigma = PcsCircuit.membership.sigma :=
    Bridge.Circuit.membership_sigma
  rw [hσ]
  exact Bridge.Setup.pcsCircuit_sigma_size

end ProverCircuit

/-! ## The bridge -/

/-- **The membership circuit's cells and wiring are F0b's** (`CircuitMatch`). -/
theorem circuitMatch : CircuitMatch where
  cells := ProverCircuit.cells_getD
  sigma := ProverCircuit.sigma_point
  sigmaSize := ProverCircuit.sigma_size

end E2ECompleteness

/-- info: 'E2ECompleteness.circuitMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.circuitMatch
