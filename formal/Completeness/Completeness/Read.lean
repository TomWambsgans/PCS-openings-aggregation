-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E` and their limbs (`LeanVM/Parameters/Field.lean`), `eqEval`,
-- `boolPoint`, `eqEval_cons`.
import Completeness.Honest
import Completeness.HiddenFill

/-!
# The honest tables as the openings read them

The openings (`WhirBridge`, mumbai's WHIR) see a table as its entries by number (`ℕ → K`, entry
`t` at the cube point of `t`'s bits, `boolPoint`) and a claim as `Σ_t ofK(T t) · eq(t, p)`
(`tableEvalN`, which is `Layout.tableEval` of the table a stack is read back as). F1 sees a table
as a function on `Fin V → Bool` and a claim as `mle`. This file is the dictionary, on mumbai's
`K = GF(2^64)` and `E = GF(2^192)`:

* `limbE`: `E = K + K y + K y^2` (`E.eq_sum_limbs`), the `LimbSystem` of the quotient table;
* `natTable`, `mle_eq_tableEvalN`: a table by numbers, and F1's claim on it is the openings';
* `witness_inChunks`, `quotient_inChunks`: the honest witness and quotient tables vanish off the
  chunks `witness_layout` and `quotient_layout` list (`[(0, 2^24), (1, 16)]` and
  `quotient_chunks(24, Q_SPILL, 64)`), so the hidden layouts read them back whole
  (`HiddenFill.lean`'s `witness_read`, `quotient_read`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier

namespace Completeness

open QuotientSecurity

noncomputable instance : SampleableType E := SampleableType.ofFintype E

/-- **`E` over `K`**: `x = x_0 + x_1 y + x_2 y^2` (`F192`'s limbs). -/
noncomputable def limbE : LimbSystem K E where
  ι := algebraMap K E
  Y := y
  limb x e := x.limb e
  decomp x := by
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
    exact E.eq_sum_limbs x

/-! ## Tables by numbers -/

/-- The cube point of a number: its bits. -/
def bitsOf (V n : ℕ) : Fin V → Bool := fun k => n.testBit k

theorem bitsOf_succ (V n : ℕ) :
    bitsOf (V + 1) n = Fin.cons (n.testBit 0) (bitsOf V (n / 2)) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · simp only [bitsOf, Fin.cons_succ, Fin.val_succ]
    rw [← Nat.testBit_div_two]

theorem idx_bitsOf : ∀ (V n : ℕ), n < 2 ^ V → idx (bitsOf V n) = n
  | 0, n, h => by simp [idx]; omega
  | V + 1, n, h => by
    have h2 : n / 2 < 2 ^ V := by
      rw [pow_succ, mul_comm] at h
      exact Nat.div_lt_of_lt_mul h
    rw [bitsOf_succ, idx_cons, idx_bitsOf V (n / 2) h2]
    have := Nat.mod_add_div n 2
    simp only [Nat.testBit_zero, decide_eq_true_eq]
    split_ifs with h1 <;> omega

theorem testBit_idx : ∀ {V : ℕ} (b : Fin V → Bool) (k : Fin V), (idx b).testBit k = b k
  | 0, _, k => k.elim0
  | V + 1, b, k => by
    obtain ⟨x, c, rfl⟩ : ∃ x c, b = Fin.cons x c := ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
    rw [idx_cons]
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Fin.val_zero, Fin.cons_zero, Nat.testBit_zero]
      cases x <;> simp <;> omega
    · simp only [Fin.val_succ, Fin.cons_succ, Nat.testBit_succ]
      have : ((if x = true then 1 else 0) + 2 * idx c) / 2 = idx c := by split_ifs <;> omega
      rw [this, testBit_idx]

theorem bitsOf_idx {V : ℕ} (b : Fin V → Bool) : bitsOf V (idx b) = b :=
  funext fun k => testBit_idx b k

/-- **A table by numbers**: entry `n` is the table at `n`'s bits, zero past `2^V`. -/
def natTable {V : ℕ} (c : (Fin V → Bool) → K) (n : ℕ) : K :=
  if n < 2 ^ V then c (bitsOf V n) else 0

theorem natTable_idx {V : ℕ} (c : (Fin V → Bool) → K) (b : Fin V → Bool) :
    natTable c (idx b) = c b := by
  rw [natTable, if_pos (idx_lt b), bitsOf_idx]

/-- **A claim on a table by numbers**, as the openings evaluate it: `Σ_t ofK(T t) · eq(bits t, p)`
(`Layout.tableEval` of the table read back). -/
noncomputable def tableEvalN (V : ℕ) (T : ℕ → K) (p : List E) : E :=
  ∑ t ∈ range (2 ^ V), ofK (T t) * eqEval (boolPoint V t) p

theorem boolPoint_succ (m k : ℕ) :
    boolPoint (m + 1) k = (if k.testBit 0 then 1 else 0) :: boolPoint m (k / 2) := by
  apply List.ext_getElem
  · simp [boolPoint]
  · intro i h1 h2
    cases i with
    | zero => simp [boolPoint]
    | succ i => simp [boolPoint, Nat.testBit_succ]

/-- `eq` of a number's bits and a point is the product of `mle`'s factors. -/
theorem eqEval_boolPoint : ∀ (V n : ℕ) (u : Fin V → E),
    eqEval (boolPoint V n) (List.ofFn u) = ∏ k : Fin V, if n.testBit k then u k else 1 + u k
  | 0, n, u => by simp [eqEval, boolPoint]
  | V + 1, n, u => by
    rw [boolPoint_succ, List.ofFn_succ, LeanVM.Protocol.Whir.Complete.eqEval_cons,
      eqEval_boolPoint V (n / 2) (fun k => u k.succ), Fin.prod_univ_succ]
    congr 1
    · simp only [Fin.val_zero]
      by_cases hb : n.testBit 0 = true
      · simp only [hb, ↓reduceIte]
        linear_combination LeanVM.Protocol.Whir.Complete.two_eq_zero_E
      · simp only [hb, ↓reduceIte, Bool.false_eq_true, add_zero]
    · refine prod_congr rfl fun k _ => ?_
      simp only [Fin.val_succ, Nat.testBit_div_two]

/-- **F1's claim is the openings' claim**: the multilinear extension of a table over `K`, read in
`E`, at `u` is `tableEvalN` of the table by numbers at the point `u` as a list. -/
theorem mle_eq_tableEvalN {V : ℕ} (c : (Fin V → Bool) → K) (u : Fin V → E) :
    mle (fun b => ofK (c b)) u = tableEvalN V (natTable c) (List.ofFn u) := by
  unfold mle tableEvalN
  symm
  refine sum_nbij' (fun t => bitsOf V t) idx (fun t _ => mem_univ _)
    (fun b _ => mem_range.mpr (idx_lt b)) (fun t ht => idx_bitsOf V t (mem_range.mp ht))
    (fun b _ => bitsOf_idx b) (fun t ht => ?_)
  have ht' := mem_range.mp ht
  rw [natTable, if_pos ht', eqEval_boolPoint]
  rfl

/-! ## The honest tables vanish off their chunks -/

/-- The witness table's chunks. -/
theorem witness_inChunks (BK : CantorBasis K (22 + 2)) (f : (Fin (22 + 2) → Bool) → K)
    (m : Fin 4 → Fin 3 → K) (n : ℕ) (hn : ¬ InChunks (WhirBridge.cellVars WhirBridge.logRows)
      [(0, 2 ^ WhirBridge.cellVars WhirBridge.logRows), (1, 16)] n) :
    natTable (witnessTable BK f m) n = 0 := by
  unfold natTable
  split_ifs with hlt
  · by_contra hne
    have hs := witnessTable_support BK f m _ hne
    rw [idx_bitsOf _ _ hlt] at hs
    apply hn
    rcases hs with h | ⟨h1, h2⟩
    · refine ⟨(0, 2 ^ 24), by decide, n, h, ?_⟩
      simp
    · refine ⟨(1, 16), by decide, n - 2 ^ 24, ?_, ?_⟩
      · show n - 2 ^ 24 < 16
        omega
      · show n = 1 * 2 ^ (WhirBridge.cellVars WhirBridge.logRows) + (n - 2 ^ 24)
        simp only [WhirBridge.cellVars, WhirBridge.logRows]
        omega
  · rfl

/-- The quotient layout's chunks, at `LOG_ROWS = 22`. -/
abbrev qChunks : List (ℕ × ℕ) :=
  WhirBridge.quotientChunks (WhirBridge.cellVars WhirBridge.logRows) WhirBridge.qSpill 64

theorem cellVars_logRows : WhirBridge.cellVars WhirBridge.logRows = 24 := rfl

theorem inChunks_of {chunks : List (ℕ × ℕ)} {c : ℕ × ℕ} (hc : c ∈ chunks) {j : ℕ} (hj : j < c.2)
    {t : ℕ} (ht : t = c.1 * 2 ^ 24 + j) :
    InChunks (WhirBridge.cellVars WhirBridge.logRows) chunks t := by
  refine ⟨c, hc, j, hj, ?_⟩
  rw [cellVars_logRows]
  exact ht

theorem h_inChunks {e d t : ℕ} (he : e < 3) (hd : d < 2 ^ 24) (ht : t = d + 2 ^ 24 * (16 * e)) :
    InChunks (WhirBridge.cellVars WhirBridge.logRows) qChunks t := by
  refine inChunks_of (c := (16 * e, 2 ^ 24)) ?_ hd (by rw [ht]; ring)
  interval_cases e <;> decide

theorem q_inChunks {e d t : ℕ} (he : e < 3) (hd : d < 3 * 2 ^ 24 + 9280)
    (ht : t = d + 2 ^ 24 * (4 + 16 * e)) :
    InChunks (WhirBridge.cellVars WhirBridge.logRows) qChunks t := by
  by_cases h3 : d < 3 * 2 ^ 24
  · have hdg : d / 2 ^ 24 < 3 := by omega
    have hsplit := Nat.div_add_mod d (2 ^ 24)
    refine inChunks_of (c := (16 * e + 4 + d / 2 ^ 24, 2 ^ 24)) ?_ (j := d % 2 ^ 24)
      (Nat.mod_lt _ (by positivity)) ?_
    · generalize d / 2 ^ 24 = dg at hdg
      interval_cases e <;> interval_cases dg <;> decide
    · rw [ht]
      dsimp only
      linarith
  · refine inChunks_of (c := (16 * e + 7, 9280)) ?_ (j := d - 3 * 2 ^ 24) (by dsimp only; omega)
      (by rw [ht]; dsimp only; omega)
    interval_cases e <;> decide

theorem g_inChunks {d t : ℕ} (hd : d < 7 * 2 ^ 22 + 64) (ht : t = d + 2 ^ 24 * 8) :
    InChunks (WhirBridge.cellVars WhirBridge.logRows) qChunks t := by
  by_cases h1 : d < 2 ^ 24
  · exact inChunks_of (c := (8, 2 ^ 24)) (by decide) h1 (by rw [ht]; ring)
  · exact inChunks_of (c := (9, 3 * 2 ^ 24 / 4 + 64)) (by decide) (j := d - 2 ^ 24)
      (by dsimp only; omega) (by rw [ht]; dsimp only; omega)

/-- Where the quotient table is not zero, by numbers (any number `M` of low digits). -/
theorem quotientTable_support_idx (M : ℕ) (R : Params.Quotients E) (qGateK : K[X])
    (b : Fin (M + 1 + 1 + 1 + 1) → Bool) (hne : quotientTable limbE M R qGateK b ≠ 0) :
    ∃ (d : ℕ) (κ τ e₀ e₁ : Bool),
      idx b = d + 2 ^ M * ((if κ then 1 else 0) + 2 * if τ then 1 else 0) +
        2 ^ (M + 1 + 1) * ((if e₀ then 1 else 0) + 2 * if e₁ then 1 else 0) ∧
      slotLive κ τ (limbIdx e₀ e₁) = true ∧ d < slotBound κ τ := by
  obtain ⟨X, e₀, e₁, rfl⟩ := exists_snoc_snoc b
  obtain ⟨low, κ, τ, rfl⟩ := exists_snoc_snoc X
  obtain ⟨hlive, hbound⟩ := quotientTable_support limbE M R qGateK low κ τ e₀ e₁ hne
  exact ⟨idx low, κ, τ, e₀, e₁, by rw [idx_quad_snoc, idx_quad_snoc], hlive, hbound⟩

/-- The chunks a live limb below its slot's bound lies in. -/
theorem inChunks_of_slot (d : ℕ) (κ τ e₀ e₁ : Bool) (hlive : slotLive κ τ (limbIdx e₀ e₁) = true)
    (hbound : d < slotBound κ τ) :
    InChunks (WhirBridge.cellVars WhirBridge.logRows) qChunks
      (d + 2 ^ 26 * ((if κ then 1 else 0) + 2 * if τ then 1 else 0) +
        2 ^ 28 * ((if e₀ then 1 else 0) + 2 * if e₁ then 1 else 0)) := by
  cases κ <;> cases τ <;> cases e₀ <;> cases e₁ <;>
    simp only [slotLive, limbIdx, slotBound, Bool.false_eq_true, ↓reduceIte,
      decide_eq_true_eq] at hlive hbound <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ite_true, ite_false, zero_mul, add_zero, one_mul] <;>
    first
      | exact absurd hlive (by decide)
      | exact h_inChunks (e := 0) (by norm_num) hbound (by ring1)
      | exact h_inChunks (e := 1) (by norm_num) hbound (by ring1)
      | exact h_inChunks (e := 2) (by norm_num) hbound (by ring1)
      | exact q_inChunks (e := 0) (by norm_num) hbound (by ring1)
      | exact q_inChunks (e := 1) (by norm_num) hbound (by ring1)
      | exact q_inChunks (e := 2) (by norm_num) hbound (by ring1)
      | exact g_inChunks hbound (by ring1)

/-- **The honest quotient table vanishes off its chunks.** -/
theorem quotient_inChunks (R : Params.Quotients E) (qGateK : K[X]) (n : ℕ)
    (hn : ¬ InChunks (WhirBridge.cellVars WhirBridge.logRows) qChunks n) :
    natTable (quotientTable limbE (22 + 2 + 1 + 1) R qGateK) n = 0 := by
  unfold natTable
  split_ifs with hlt
  · by_contra hne
    obtain ⟨d, κ, τ, e₀, e₁, hidx, hlive, hbound⟩ :=
      quotientTable_support_idx (22 + 2 + 1 + 1) R qGateK _ hne
    rw [idx_bitsOf _ _ hlt] at hidx
    rw [hidx] at hn
    exact hn (inChunks_of_slot d κ τ e₀ e₁ hlive hbound)
  · rfl

end Completeness
