-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.End
import Completeness.Honest
import Completeness.Reduction
import Completeness.Circuit
import Bridge.Circuit.Outputs
import QuotientSecurity.DeployedHonest
import QuotientSecurity.DeployedConcrete
import QuotientSecurity.DeployedBasis

/-!
# F1's facts on the deployed instance, for the statement's witnesses

The zero-knowledge end theorem (`zeroKnowledge_deployed_end`) names F1's facts on the reduction's
parameters `P₀`, the statement's words `stmtE stmt` and the witness's polynomials `gK stmt w`,
`van stmt w`. Here they are the deployed ones, and the facts are proved:

* **the parameters** `P₀D`: F1's instance (`QuotientSecurity.Instance.params`) of soundness's
  `deployedInstance` with `beta()`'s Cantor basis (`deployedBasis`, in `K = F64`, embedded in `E`),
  the deployed σ and `coordinate_weight`'s weights (`instD`: Completeness's `deployedInstanceE`);
* **the statement's words** `stmtWD stmt`: `statement::halves` of `y` and `root`, then `1, 0, 0, 0`
  (`statementWords F192.G F192.Y`);
* **the witness**: the cells of F0b's honest assignment of the secret (`cellsKD w`, the deployed
  circuit evaluated on `membership_inputs` of `secretTr w`, F0b's secret of the statement's), the
  witness table (`witTableD w m`: the cells' table over `K` then the masks, Completeness's
  `witnessTable`), its row polynomials without masks (`gKD w`) and the vanishing polynomial
  `vanD = w_22`; the masked first message is the table's (`committed_eq`:
  `gKD w + w_22 · maskPoly (m j)` is the table's row polynomial, the masks lying at entries
  `2^24 + 4i + j`);
* **the facts**: `P₀D.Exact`, `P₀D.nCells = 2^24`, `w_22` vanishing on the rows, nonzero, of degree
  `2^22`, and **`hsatD`**: a witness of the statement's relation (`Relation stmt w`) satisfies F1's
  relation for `stmtWD stmt` (Completeness's `relation_statementWords_keeps` with the deployed
  circuit's forward Keccak correctness, `deployedAssign_public`, and F0b's secret of the
  statement's, `Bridge.Circuit.statement_secretOfInputs`).
-/

open Polynomial QuotientSecurity Primitives Finset
open LeanVM.Parameters

namespace PcsQuotient.EndToEnd

set_option linter.unusedSectionVars false

/-! ## The deployed instance -/

/-- **The deployed instance over `E`**: `beta()`'s Cantor basis in `K`, the deployed σ,
`coordinate_weight`'s weights. -/
noncomputable def instD : QuotientSecurity.Instance E :=
  QuotientSecurity.deployedInstance (deployedBasis.map (algebraMap K E))

theorem instD_basis (k : ℕ) : instD.basis.β k = algebraMap K E (deployedBasis.β k) := rfl

theorem instD_c : instD.c = coordWeight F192.G F192.Y := rfl

theorem instD_wiring : instD.wiring = deployedSigma := rfl

/-- **The reduction's parameters** on the deployed instance. -/
noncomputable abbrev P₀D : Params E := instD.params

/-- **The statement's eight words**: `statement::halves` of `y` and `root`, then `1, 0, 0, 0`. -/
noncomputable def stmtWD (stmt : Statement) : Fin 8 → E :=
  QuotientSecurity.statementWords F192.G F192.Y (fun i => stmt.y[i]) (fun i => stmt.root[i])

/-! ## The witness -/

/-- **The honest cells, over `K`**: what each cell carries in F0b's honest assignment of the
statement's secret. -/
noncomputable def cellsKD (w : Secret) : (Fin (22 + 2) → Bool) → K :=
  fun z => bitF ((deployed.cellSrc z).bval (deployedAssign (Bridge.Circuit.secretTr w)))

/-- **The witness table** (`witness_layout`, `25` variables over `K`): the cells' table, then the
masks at `2^24 + 4i + j`. -/
noncomputable def witTableD (w : Secret) (m : Fin 4 → Fin 3 → K) :
    (Fin (22 + 2 + 1) → Bool) → K :=
  Completeness.witnessTable deployedBasis (cellsKD w) m

/-- **Row polynomial `j` of a table** on `M + 2` coordinates whose first two are the role: the
polynomial of its `M` other coordinates. (Every statement about the deployed tables below is an
instance of one about `rowPart`, stated for any `M`: at a numeral the kernel would compare the
tables' sums over `2^22` entries.) -/
noncomputable def rowPart {M : ℕ} (c : (Fin (M + 2) → Bool) → K) (j : Fin 4) : K[X] :=
  tablePoly fun b : Fin M → Bool => c (Fin.cons (roleBit0 j) (Fin.cons (roleBit1 j) b))

/-- **The witness's row polynomials**, over `K`: the cells' table's. -/
noncomputable def gKD (w : Secret) : Fin 4 → K[X] :=
  rowPart (M := 22) (Completeness.tableOf deployedBasis le_rfl (cellsKD w))

/-- **The masks' vanishing polynomial**, `w_22` over `K`. -/
noncomputable def vanD : K[X] := digitPoly 22

/-! ## The masked first message is the table's -/

theorem idx_cons_cons {M : ℕ} (x y : Bool) (b : Fin M → Bool) :
    Completeness.idx (Fin.cons x (Fin.cons y b) : Fin (M + 1 + 1) → Bool) =
      (if x then 1 else 0) + 2 * (if y then 1 else 0) + 4 * Completeness.idx b := by
  rw [Completeness.idx_cons, Completeness.idx_cons]
  ring

/-- The role of a row polynomial, as a number: `roleBit0 j + 2 roleBit1 j = j`. -/
theorem role_val (j : Fin 4) :
    (if roleBit0 j then 1 else 0) + 2 * (if roleBit1 j then 1 else 0) = (j : ℕ) := by
  fin_cases j <;> rfl

/-- The masks' entries of row polynomial `j`: entry `b` (`22` coordinates) is `m j (idx b)` below
`3`, zero above. -/
theorem maskTable_row (m : Fin 4 → Fin 3 → K) (j : Fin 4) (b : Fin 22 → Bool) :
    Completeness.maskTable m (Fin.cons (roleBit0 j) (Fin.cons (roleBit1 j) b)) =
      if h : Completeness.idx b < 3 then m j ⟨Completeness.idx b, h⟩ else 0 := by
  have hidx : Completeness.idx (Fin.cons (roleBit0 j) (Fin.cons (roleBit1 j) b) :
      Fin (22 + 1 + 1) → Bool) = (j : ℕ) + 4 * Completeness.idx b := by
    rw [idx_cons_cons, role_val]
  have hj := j.isLt
  unfold Completeness.maskTable
  split_ifs with h12 h3 h3
  · exact congrArg₂ m (Fin.ext (by simp only [hidx]; omega)) (Fin.ext (by simp only [hidx]; omega))
  · exfalso
    rw [hidx] at h12
    omega
  · exfalso
    rw [hidx] at h12
    omega
  · rfl

/-- A table on `22` coordinates nonzero only below index `3` holds `c₀ + c₁ X + c₂ (X^2 + X)`. -/
theorem tablePoly_low3 (c : (Fin 22 → Bool) → K) (hc : ∀ b, 3 ≤ Completeness.idx b → c b = 0) :
    tablePoly c = C (c fun _ => false) + C (c fun k => decide ((k : ℕ) = 0)) * X +
      C (c fun k => decide ((k : ℕ) = 1)) * (X ^ 2 + X) := by
  classical
  set b0 : Fin 22 → Bool := fun _ => false with hb0
  set b1 : Fin 22 → Bool := fun k => decide ((k : ℕ) = 0) with hb1
  set b2 : Fin 22 → Bool := fun k => decide ((k : ℕ) = 1) with hb2
  have h01 : b0 ≠ b1 := fun h => by simpa [hb0, hb1] using congrFun h ⟨0, by norm_num⟩
  have h02 : b0 ≠ b2 := fun h => by simpa [hb0, hb2] using congrFun h ⟨1, by norm_num⟩
  have h12 : b1 ≠ b2 := fun h => by simpa [hb1, hb2] using congrFun h ⟨0, by norm_num⟩
  -- the indices below `3` are these three
  have hsupp : ∀ b : Fin 22 → Bool, Completeness.idx b < 3 → b = b0 ∨ b = b1 ∨ b = b2 := by
    intro b hb
    have hle : ∀ k : Fin 22, b k = true → 2 ^ (k : ℕ) ≤ Completeness.idx b := fun k hk => by
      unfold Completeness.idx
      refine le_trans (le_of_eq (by simp [hk])) (Finset.single_le_sum
        (f := fun k : Fin 22 => if b k then 2 ^ (k : ℕ) else 0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k))
    have hhigh : ∀ k : Fin 22, 2 ≤ (k : ℕ) → b k = false := fun k hk => by
      by_contra h
      have := hle k (by simpa using h)
      have : 2 ^ 2 ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hk
      omega
    have hpair : ¬ (b ⟨0, by norm_num⟩ = true ∧ b ⟨1, by norm_num⟩ = true) := by
      rintro ⟨h0, h1⟩
      have hsub : ({⟨0, by norm_num⟩, ⟨1, by norm_num⟩} : Finset (Fin 22)) ⊆ Finset.univ :=
        Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : Fin 22 =>
        if b k then 2 ^ (k : ℕ) else 0) hsub (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair (by decide)] at this
      simp only [h0, h1, ite_true] at this
      have : 3 ≤ Completeness.idx b := by unfold Completeness.idx; simpa using this
      omega
    have hext : ∀ b' : Fin 22 → Bool, (∀ k : Fin 22, 2 ≤ (k : ℕ) → b' k = false) →
        b' ⟨0, by norm_num⟩ = b ⟨0, by norm_num⟩ → b' ⟨1, by norm_num⟩ = b ⟨1, by norm_num⟩ →
        b = b' := fun b' hb' e0 e1 => by
      funext k
      by_cases hk0 : (k : ℕ) = 0
      · have : k = ⟨0, by norm_num⟩ := Fin.ext hk0
        rw [this, e0]
      by_cases hk1 : (k : ℕ) = 1
      · have : k = ⟨1, by norm_num⟩ := Fin.ext hk1
        rw [this, e1]
      rw [hhigh k (by omega), hb' k (by omega)]
    cases h0 : b ⟨0, by norm_num⟩ <;> cases h1 : b ⟨1, by norm_num⟩
    · exact Or.inl (hext b0 (fun _ _ => rfl) (by rw [h0]) (by rw [h1]))
    · exact Or.inr (Or.inr (hext b2 (fun k hk => by simp [hb2]; omega) (by rw [h0]; rfl)
        (by rw [h1]; rfl)))
    · exact Or.inr (Or.inl (hext b1 (fun k hk => by simp [hb1]; omega) (by rw [h0]; rfl)
        (by rw [h1]; rfl)))
    · exact absurd ⟨h0, h1⟩ hpair
  have hsum : tablePoly c = ∑ b ∈ ({b0, b1, b2} : Finset (Fin 22 → Bool)),
      C (c b) * ∏ k : Fin 22, (if b k then (digitPoly (k : ℕ) : K[X]) else 1) := by
    unfold tablePoly
    refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_).symm
    have h3 : 3 ≤ Completeness.idx b := by
      by_contra h
      rcases hsupp b (by omega) with rfl | rfl | rfl <;> simp at hb
    rw [hc b h3, C_0, zero_mul]
  rw [hsum, Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
    Finset.sum_singleton]
  have p0 : ∏ k : Fin 22, (if b0 k then (digitPoly (k : ℕ) : K[X]) else 1) = 1 := by
    simp [hb0]
  have p1 : ∏ k : Fin 22, (if b1 k then (digitPoly (k : ℕ) : K[X]) else 1) = X := by
    rw [Finset.prod_eq_single ⟨0, by norm_num⟩ (fun k _ hk => by
      have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
      have hk' : decide ((k : ℕ) = 0) = false := by simp [this]
      simp only [hb1, hk', Bool.false_eq_true, ite_false]) (by simp)]
    simp [hb1, digitPoly]
  have p2 : ∏ k : Fin 22, (if b2 k then (digitPoly (k : ℕ) : K[X]) else 1) = X ^ 2 + X := by
    rw [Finset.prod_eq_single ⟨1, by norm_num⟩ (fun k _ hk => by
      have : (k : ℕ) ≠ 1 := fun h => hk (Fin.ext h)
      have hk' : decide ((k : ℕ) = 1) = false := by simp [this]
      simp only [hb2, hk', Bool.false_eq_true, ite_false]) (by simp)]
    simp [hb2, digitPoly]
  rw [p0, p1, p2, mul_one]
  ring

/-- **The masks' row polynomial is the mask's polynomial**: the entries `4i + j` of the masks'
chunk hold `maskPoly (m j)` in row polynomial `j` (on `1, X, X^2 + X`). -/
theorem maskRow_eq (m : Fin 4 → Fin 3 → K) (j : Fin 4) :
    rowPart (M := 22) (Completeness.maskTable m) j = maskPoly (m j) := by
  unfold rowPart
  rw [tablePoly_low3 _ fun b hb => by rw [maskTable_row, dite_eq_right (by omega)]]
  have i0 : Completeness.idx (fun _ : Fin 22 => false) = 0 := by simp [Completeness.idx]
  have i1 : Completeness.idx (fun k : Fin 22 => decide ((k : ℕ) = 0)) = 1 := by
    unfold Completeness.idx
    rw [Finset.sum_eq_single ⟨0, by norm_num⟩ (fun k _ hk => by
      have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
      simp [this]) (by simp)]
    simp
  have i2 : Completeness.idx (fun k : Fin 22 => decide ((k : ℕ) = 1)) = 2 := by
    unfold Completeness.idx
    rw [Finset.sum_eq_single ⟨1, by norm_num⟩ (fun k _ hk => by
      have : (k : ℕ) ≠ 1 := fun h => hk (Fin.ext h)
      simp [this]) (by simp)]
    simp
  rw [maskTable_row, maskTable_row, maskTable_row]
  simp only [i0, i1, i2]
  simp only [show (0 : ℕ) < 3 by norm_num, show (1 : ℕ) < 3 by norm_num,
    show (2 : ℕ) < 3 by norm_num, dite_true]
  rfl

/-- A joined table's row polynomial: its low half's, plus `w_M` times its high half's. -/
theorem witnessOfTable_join {M : ℕ} (c₀ c₁ : (Fin (M + 2) → Bool) → K) (j : Fin 4) :
    witnessOfTable (Completeness.joinTable c₀ c₁) j = rowPart c₀ j + digitPoly M * rowPart c₁ j := by
  rw [Completeness.witnessOfTable_apply, tablePoly_snoc]
  have e : ∀ (b : Fin M → Bool) (x : Bool),
      (Fin.cons (roleBit0 j) (Fin.cons (roleBit1 j) (Fin.snoc b x : Fin (M + 1) → Bool)) :
        Fin (M + 1 + 1 + 1) → Bool) =
        Fin.snoc (Fin.cons (roleBit0 j) (Fin.cons (roleBit1 j) b) : Fin (M + 1 + 1) → Bool) x := by
    intro b x
    rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons]
  simp only [e, Completeness.joinTable_snoc, Bool.false_eq_true, ite_false, ite_true]
  rfl

/-- **The witness table's row polynomials**: the cells' part, plus `w_22` times the masks'. -/
theorem witnessOfTable_witTableD (w : Secret) (m : Fin 4 → Fin 3 → K) (j : Fin 4) :
    witnessOfTable (witTableD w m) j = gKD w j + vanD * maskPoly (m j) := by
  have hm := witnessOfTable_join (M := 22)
    (Completeness.tableOf deployedBasis le_rfl (cellsKD w)) (Completeness.maskTable m) j
  rw [maskRow_eq] at hm
  have e1 : rowPart (M := 22) (Completeness.tableOf deployedBasis le_rfl (cellsKD w)) j = gKD w j :=
    rfl
  have e2 : (digitPoly 22 : K[X]) = vanD := rfl
  rw [e1, e2] at hm
  exact hm

/-- A table read in `E` holds the row polynomials mapped to `E`. -/
theorem witnessOfTable_map {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → K) (j : Fin 4) :
    witnessOfTable (fun b => algebraMap K E (c b)) j = (witnessOfTable c j).map (algebraMap K E) := by
  fin_cases j <;> exact Completeness.tablePoly_map (algebraMap K E) _

/-- **The masked first message is the witness table's** (read in `E`). -/
theorem committed_eq (w : Secret) (m : Fin 4 → Fin 3 → K) :
    committed (E := E) (gKD w) vanD m = witnessOfTable fun b => algebraMap K E (witTableD w m b) := by
  funext j
  rw [committed, witnessOfTable_map, witnessOfTable_witTableD]

/-! ## F1's facts -/

theorem hED : P₀D.Exact := instD.exact

theorem hND : P₀D.nCells = 2 ^ 24 := instD.nCells

theorem hvanD : ∀ x : P₀D.T, aeval (rowPoly.eval (x : E)) vanD = 0 :=
  fun x => instD.mask_vanishes (K := K) x

theorem hvan0D : vanD ≠ 0 := (digitPoly_monic_natDegree (F := K) 22).1.ne_zero

theorem hdegD : vanD.natDegree ≤ 2 ^ 22 := (digitPoly_monic_natDegree (F := K) 22).2.le

/-- F0b's secret of the statement's is well formed. -/
theorem secretTr_wellFormed (w : Secret) : (Bridge.Circuit.secretTr w).WellFormed := by
  refine ⟨by simp [Bridge.Circuit.secretTr], fun i hi => ?_⟩
  rw [Bridge.Circuit.secretTr_siblings w ⟨i, hi⟩]
  simp

/-- F0b's statement of the secret is the statement's, byte by byte. -/
theorem bytes32_secretTr (w : Secret) :
    bytes32 (Bridge.Circuit.secretTr w).y = (fun i => w.statement.y[i]) ∧
      bytes32 (Bridge.Circuit.secretTr w).root = (fun i => w.statement.root[i]) := by
  obtain ⟨hy, hr⟩ := Bridge.Circuit.statement_secretOfInputs w (Bridge.Circuit.secretTr w) rfl
    (fun i => (Bridge.Circuit.secretTr_siblings w i).symm)
    (fun i => (Bridge.Circuit.secretTr_directions w i).symm)
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · rw [← hy]
    simp [bytes32]
  · rw [← hr]
    simp [bytes32]

/-- **The masked first message's cells satisfy F1's relation** for a witness of the statement's
relation, whatever the masks: they are the honest assignment's (`cellsOf_honest`), which satisfies
the deployed circuit and whose public words are the statement's (`relation_statementWords_keeps`,
`deployedAssign_public`). -/
theorem relation_honestD (stmt : Statement) (w : Secret) (hw : Relation stmt w)
    (m : Fin 4 → Fin 3 → K) :
    instD.Relation (stmtWD stmt) (instD.cellsOf (committed (E := E) (gKD w) vanD m)) := by
  set s := Bridge.Circuit.secretTr w
  have hcells : instD.cellsOf (committed (E := E) (gKD w) vanD m) =
      deployed.cellsOfBits (deployedAssign s) := by
    funext x
    rw [committed_eq]
    unfold witTableD
    rw [Completeness.cellsOf_honest (algebraMap K E) instD deployedBasis instD_basis]
    unfold cellsKD ChiCircuit.cellsOfBits bitF
    split_ifs <;> simp
  rw [hcells]
  have hstmt : stmtWD stmt =
      QuotientSecurity.statementWords F192.G F192.Y (bytes32 s.y) (bytes32 s.root) := by
    obtain ⟨hy, hr⟩ := bytes32_secretTr w
    rw [stmtWD, hy, hr, hw]
  rw [hstmt]
  refine Completeness.relation_statementWords_keeps instD deployed instD_c
    (fun z => deployedSigma_cellSrc z) deployed_word4_one (fun j hj => deployed_word4 j hj)
    deployed_word5 deployed_word6 deployed_word7 _ (deployedAssign_satisfies s) _ _ fun J => ?_
  rw [halves_eq_sum, ChiCircuit.pubWord]
  exact Finset.sum_congr rfl fun j _ => by rw [deployedAssign_public s (secretTr_wellFormed w) J j]

/-- **A witness of the statement's relation satisfies F1's relation** for the statement's words. -/
theorem hsatD (stmt : Statement) (w : Secret) (hw : Relation stmt w) :
    P₀D.Sat (stmtWD stmt) (P₀D.cells (committed (gKD w) vanD 0)) :=
  instD.sat_of_relation _ _ (relation_honestD stmt w hw 0)

end PcsQuotient.EndToEnd
