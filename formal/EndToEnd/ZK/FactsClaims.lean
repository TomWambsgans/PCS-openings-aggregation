-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The dictionary between tables by numbers and F1's claims, and the honest tables' chunks, follow
-- `formal/Completeness/Completeness/Read.lean` (restated here without its WhirBridge import).
import ZK.FactsF1
import ZK.FactsField
import ZK.FactsLayout

/-!
# The honest tables meet the verifier's claims, off the degenerate challenges and masks

The zero-knowledge end theorem names `hTW`, `hTQ`: the honest witness and quotient tables, laid on
their hidden stacks (`stackD`), have the verifier's claimed values (`valsW`, `valsQ`) at every good
challenge and non-degenerate masks (`ClaimsND`). Here the honest tables are the deployed ones and
both are proved:

* **the tables** (`TWD w m`, `TQD w abc m`): Completeness's witness table of the honest cells and
  the masks (`witTableD`), and quotient table of F1's honest second message (`Params.honest` of the
  masked first message at `α, β, γ`, its gate quotient over `K`), by numbers (`natTableD`), placed
  where the deployed layouts hold them (`Layout.place`; `Table::hidden`'s stack is `stackD (place ·)
  + stackR`, `hiddenWord_eq`);
* **the layouts' claims are the tables' multilinear claims** (`claimsMap_place_witness`,
  `claimsMap_place_quotient`, `FactsLayout.lean`), the tables vanishing off their chunks
  (`witness_supportD`, `quotient_supportD`), and those are F1's `mle` (`mle_eq_sum_eqBits`);
* **F1's claims hold of the honest tables** where nothing is divided by zero: the witness claim by
  `witness_mle` (the claims' scales nonzero, `TND`), the quotient and sum claims by
  `claims_iff_accepts` from F1's completeness (`Reduction.honest_accepts`: the relation, `good`'s
  denominators, `ClaimsND`'s scales and copy denominator) passed to the table holding the second
  message (`accepts_table_of_honest`, `slots_honest`), as Completeness's `honest_claims` does.
-/

open Polynomial QuotientSecurity Primitives Finset
open LeanVM.Parameters
open QuotientZk.Joint QuotientZk.Instance

namespace PcsQuotient.EndToEnd

set_option linter.unusedSectionVars false

/-! ## Tables by numbers -/

/-- The cube point of a number: its bits. -/
def bitsOfD (V n : ℕ) : Fin V → Bool := fun k => n.testBit k

theorem bitsOfD_succ (V n : ℕ) :
    bitsOfD (V + 1) n = Fin.cons (n.testBit 0) (bitsOfD V (n / 2)) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · simp only [bitsOfD, Fin.cons_succ, Fin.val_succ]
    rw [← Nat.testBit_div_two]

theorem idx_bitsOfD : ∀ (V n : ℕ), n < 2 ^ V → Completeness.idx (bitsOfD V n) = n
  | 0, n, h => by simp [Completeness.idx]; omega
  | V + 1, n, h => by
    have h2 : n / 2 < 2 ^ V := by
      rw [pow_succ, mul_comm] at h
      exact Nat.div_lt_of_lt_mul h
    rw [bitsOfD_succ, Completeness.idx_cons, idx_bitsOfD V (n / 2) h2]
    have := Nat.mod_add_div n 2
    simp only [Nat.testBit_zero, decide_eq_true_eq]
    split_ifs with h1 <;> omega

theorem testBit_idxD : ∀ {V : ℕ} (b : Fin V → Bool) (k : Fin V),
    (Completeness.idx b).testBit k = b k
  | 0, _, k => k.elim0
  | V + 1, b, k => by
    obtain ⟨x, c, rfl⟩ : ∃ x c, b = Fin.cons x c := ⟨b 0, Fin.tail b, (Fin.cons_self_tail b).symm⟩
    rw [Completeness.idx_cons]
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Fin.val_zero, Fin.cons_zero, Nat.testBit_zero]
      cases x <;> simp <;> omega
    · simp only [Fin.val_succ, Fin.cons_succ, Nat.testBit_succ]
      have : ((if x = true then 1 else 0) + 2 * Completeness.idx c) / 2 = Completeness.idx c := by
        split_ifs <;> omega
      rw [this, testBit_idxD]

theorem bitsOfD_idx {V : ℕ} (b : Fin V → Bool) : bitsOfD V (Completeness.idx b) = b :=
  funext fun k => testBit_idxD b k

/-- **A table by numbers**: entry `n` is the table at `n`'s bits, zero past `2^V`. -/
def natTableD {V : ℕ} (c : (Fin V → Bool) → K) (n : ℕ) : K :=
  if n < 2 ^ V then c (bitsOfD V n) else 0

/-- **F1's claim is the stack's**: the multilinear extension of a table over `K`, read in `E`, at
`u` is `Σ_n eq(bits n, u) · T n` over the table by numbers (`eqBits`, `opening::verify`'s `eq`). -/
theorem mle_eq_sum_eqBits {V : ℕ} (c : (Fin V → Bool) → K) (u : Fin V → E) :
    mle (fun b => algebraMap K E (c b)) u =
      ∑ i ∈ range (2 ^ V), Hiding.Deployed.eqBits (List.ofFn u) i *
        algebraMap K E (natTableD c i) := by
  unfold mle
  symm
  refine sum_nbij' (fun t => bitsOfD V t) Completeness.idx (fun t _ => mem_univ _)
    (fun b _ => mem_range.mpr (Completeness.idx_lt b))
    (fun t ht => idx_bitsOfD V t (mem_range.mp ht)) (fun b _ => bitsOfD_idx b) (fun t ht => ?_)
  have ht' := mem_range.mp ht
  rw [natTableD, if_pos ht', mul_comm]
  congr 1
  unfold Hiding.Deployed.eqBits
  rw [List.length_ofFn, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun k _ => ?_
  have hk : (List.ofFn u).getD k 0 = u k := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  rw [hk]
  rfl

/-! ## The honest tables vanish off their chunks -/

/-- **The honest witness table vanishes off its chunks** (the cells, the sixteen masks' entries). -/
theorem witness_supportD (w : Secret) (m : Fin 4 → Fin 3 → K) (n : ℕ)
    (hn : ¬ InChunksD 24 [(0, 2 ^ 24), (1, 16)] n) : natTableD (witTableD w m) n = 0 := by
  unfold natTableD
  split_ifs with hlt
  · by_contra hne
    have hs := Completeness.witnessTable_support deployedBasis (cellsKD w) m _ hne
    rw [idx_bitsOfD _ _ hlt] at hs
    apply hn
    rcases hs with h | ⟨h1, h2⟩
    · exact ⟨(0, 2 ^ 24), by simp, n, h, by simp⟩
    · exact ⟨(1, 16), by simp, n - 2 ^ 24, by simp only; omega, by simp only; omega⟩
  · rfl

/-! ## The honest tables -/

/-- **The honest witness table on its stack** (`witness_layout(22)`). -/
noncomputable def TWD (w : Secret) (m : Fin 4 → Fin 3 → K) : ιW → YW → K :=
  fun l y => Lw.place (natTableD (witTableD w m)) l y

/-- **The honest witness table meets the verifier's claim** at every good challenge and
non-degenerate masks: its claim on the stack is the table's multilinear claim at
`(ρ, ρ², u_2, …, u_24)`, which is the masked row polynomials' opening at the row over the claims'
scale (`witness_mle`, the scales nonzero by `TND`). -/
theorem hTWD (w : Secret) : ∀ c, good P₀D (gKD w) vanD c → ∀ m,
    ClaimsND (K := K) P₀D (gKD w) vanD c m →
      (openW deployedRep F192.Y).claims (c, redMsgs P₀D (gKD w) vanD c.1.1.2 m) (TWD w m) =
        valsW c (redMsgs P₀D (gKD w) vanD c.1.1.2 m) := by
  intro c _ m hnd
  funext i
  have htW : ∀ k : Fin (22 + 1), 1 + QuotientSecurity.sq^[(k : ℕ) + 2] c.1.1.2 ≠ 0 :=
    fun k => hnd.1.1 _ (by omega)
  have h1 := claimsMap_place_witness (K := K) (E := E) (natTableD (witTableD w m))
    (witness_supportD w m) (fun _ : Fin 1 => pointW c) i
  have h2 := mle_eq_sum_eqBits (V := 22 + 1 + 1 + 1) (witTableD w m)
    (Fin.cons c.1.2 (Fin.cons (c.1.2 ^ 2) (claimPoint 2 (22 + 1) c.1.1.2)))
  have h3 := witness_mle (k := 22 + 1) (fun b => algebraMap K E (witTableD w m b)) c.1.1.2 c.1.2
    htW
  have e25 : (2 : ℕ) ^ (22 + 1 + 1 + 1) = 2 ^ 25 := by norm_num
  rw [e25] at h2
  have ep : pointW c = List.ofFn (Fin.cons c.1.2 (Fin.cons (c.1.2 ^ 2)
      (claimPoint 2 (22 + 1) c.1.1.2)) : Fin (22 + 1 + 1 + 1) → E) := rfl
  rw [ep] at h1
  have hW := committed_eq w m
  refine h1.trans (h2.symm.trans (h3.trans ?_))
  show _ = (∑ j, Params.opening c.1.2 j * Params.opened (committed (E := E) (gKD w) vanD m)
    c.1.1.2 j) / claimScale 2 (22 + 1) c.1.1.2
  rw [hW]
  rfl

/-! ## The quotient table -/

/-- The gate quotient's polynomial over `K` (the honest one is over `K`, `qGate_mem_lifts`). -/
noncomputable def qGateKOf (R : Params.Quotients E) : K[X] :=
  open Classical in
  if h : R.qGate ∈ lifts (algebraMap K E) then Classical.choose ((lifts_iff_set_range _).mp h)
  else 0

/-- **F1's honest second message** on the masked first message, at `α, β, γ`. -/
noncomputable def RD (w : Secret) (abc : E × E × E) (m : Fin 4 → Fin 3 → K) :
    Params.Quotients E :=
  Params.honest P₀D (committed (E := E) (gKD w) vanD m) abc.1 abc.2.1 abc.2.2

/-- **The honest quotient table** (`quotient_layout`, `30` variables over `K`): Completeness's
table of the second message's slots' limbs. -/
noncomputable def quotTableD (w : Secret) (abc : E × E × E) (m : Fin 4 → Fin 3 → K) :
    (Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → K :=
  Completeness.quotientTable limbSysE (22 + 2 + 1 + 1) (RD w abc m) (qGateKOf (RD w abc m))

/-- **The honest quotient table on its stack** (`quotient_layout(22)`). -/
noncomputable def TQD (w : Secret) (abc : E × E × E) (m : Fin 4 → Fin 3 → K) : ιQ → YQ → K :=
  fun l y => Lq.place (natTableD (quotTableD w abc m)) l y

/-! ### Its chunks -/

/-- The deployed quotient layout's chunks (`quotient_chunks(24, Q_SPILL, 64)`). -/
abbrev qChunksD : List (ℕ × ℕ) :=
  Hiding.Deployed.quotientChunks 24 Hiding.Deployed.qSpill 64

theorem inChunksD_of {c : ℕ × ℕ} (hc : c ∈ qChunksD) {j : ℕ} (hj : j < c.2) {t : ℕ}
    (ht : t = c.1 * 2 ^ 24 + j) : InChunksD 24 qChunksD t :=
  ⟨c, hc, j, hj, ht⟩

theorem h_inChunksD {e d t : ℕ} (he : e < 3) (hd : d < 2 ^ 24) (ht : t = d + 2 ^ 24 * (16 * e)) :
    InChunksD 24 qChunksD t := by
  refine inChunksD_of (c := (16 * e, 2 ^ 24)) ?_ hd (by rw [ht]; ring)
  interval_cases e <;> decide

theorem q_inChunksD {e d t : ℕ} (he : e < 3) (hd : d < 3 * 2 ^ 24 + 9280)
    (ht : t = d + 2 ^ 24 * (4 + 16 * e)) : InChunksD 24 qChunksD t := by
  by_cases h3 : d < 3 * 2 ^ 24
  · have hdg : d / 2 ^ 24 < 3 := by omega
    have hsplit := Nat.div_add_mod d (2 ^ 24)
    refine inChunksD_of (c := (16 * e + 4 + d / 2 ^ 24, 2 ^ 24)) ?_ (j := d % 2 ^ 24)
      (Nat.mod_lt _ (by positivity)) ?_
    · generalize d / 2 ^ 24 = dg at hdg
      interval_cases e <;> interval_cases dg <;> decide
    · rw [ht]
      dsimp only
      linarith
  · refine inChunksD_of (c := (16 * e + 7, 9280)) ?_ (j := d - 3 * 2 ^ 24) (by dsimp only; omega)
      (by rw [ht]; dsimp only; omega)
    interval_cases e <;> decide

theorem g_inChunksD {d t : ℕ} (hd : d < 7 * 2 ^ 22 + 64) (ht : t = d + 2 ^ 24 * 8) :
    InChunksD 24 qChunksD t := by
  by_cases h1 : d < 2 ^ 24
  · exact inChunksD_of (c := (8, 2 ^ 24)) (by decide) h1 (by rw [ht]; ring)
  · exact inChunksD_of (c := (9, 3 * 2 ^ 24 / 4 + 64)) (by decide) (j := d - 2 ^ 24)
      (by dsimp only; omega) (by rw [ht]; dsimp only; omega)

/-- Where the quotient table is not zero, by numbers. -/
theorem quotientTable_support_idxD (M : ℕ) (R : Params.Quotients E) (qGateK : K[X])
    (b : Fin (M + 1 + 1 + 1 + 1) → Bool)
    (hne : Completeness.quotientTable limbSysE M R qGateK b ≠ 0) :
    ∃ (d : ℕ) (κ τ e₀ e₁ : Bool),
      Completeness.idx b = d + 2 ^ M * ((if κ then 1 else 0) + 2 * if τ then 1 else 0) +
        2 ^ (M + 1 + 1) * ((if e₀ then 1 else 0) + 2 * if e₁ then 1 else 0) ∧
      Completeness.slotLive κ τ (Completeness.limbIdx e₀ e₁) = true ∧
        d < Completeness.slotBound κ τ := by
  obtain ⟨X, e₀, e₁, rfl⟩ := Completeness.exists_snoc_snoc b
  obtain ⟨low, κ, τ, rfl⟩ := Completeness.exists_snoc_snoc X
  obtain ⟨hlive, hbound⟩ := Completeness.quotientTable_support limbSysE M R qGateK low κ τ e₀ e₁ hne
  exact ⟨Completeness.idx low, κ, τ, e₀, e₁, by
    rw [Completeness.idx_quad_snoc, Completeness.idx_quad_snoc], hlive, hbound⟩

/-- The chunks a live limb below its slot's bound lies in. -/
theorem inChunks_of_slotD (d : ℕ) (κ τ e₀ e₁ : Bool)
    (hlive : Completeness.slotLive κ τ (Completeness.limbIdx e₀ e₁) = true)
    (hbound : d < Completeness.slotBound κ τ) :
    InChunksD 24 qChunksD
      (d + 2 ^ 26 * ((if κ then 1 else 0) + 2 * if τ then 1 else 0) +
        2 ^ 28 * ((if e₀ then 1 else 0) + 2 * if e₁ then 1 else 0)) := by
  cases κ <;> cases τ <;> cases e₀ <;> cases e₁ <;>
    simp only [Completeness.slotLive, Completeness.limbIdx, Completeness.slotBound,
      Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hlive hbound <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ite_true, ite_false, zero_mul, add_zero,
      one_mul] <;>
    first
      | exact absurd hlive (by decide)
      | exact h_inChunksD (e := 0) (by norm_num) hbound (by ring1)
      | exact h_inChunksD (e := 1) (by norm_num) hbound (by ring1)
      | exact h_inChunksD (e := 2) (by norm_num) hbound (by ring1)
      | exact q_inChunksD (e := 0) (by norm_num) hbound (by ring1)
      | exact q_inChunksD (e := 1) (by norm_num) hbound (by ring1)
      | exact q_inChunksD (e := 2) (by norm_num) hbound (by ring1)
      | exact g_inChunksD hbound (by ring1)

/-- **The honest quotient table vanishes off its chunks.** -/
theorem quotient_supportD (R : Params.Quotients E) (qGateK : K[X]) (n : ℕ)
    (hn : ¬ InChunksD 24 qChunksD n) :
    natTableD (Completeness.quotientTable limbSysE (22 + 2 + 1 + 1) R qGateK) n = 0 := by
  unfold natTableD
  split_ifs with hlt
  · by_contra hne
    obtain ⟨d, κ, τ, e₀, e₁, hidx, hlive, hbound⟩ :=
      quotientTable_support_idxD (22 + 2 + 1 + 1) R qGateK _ hne
    rw [idx_bitsOfD _ _ hlt] at hidx
    rw [hidx] at hn
    exact hn (inChunks_of_slotD d κ τ e₀ e₁ hlive hbound)
  · rfl

/-! ### Its claims -/

theorem one_add_Y_ne : (1 + F192.Y : E) ≠ 0 := by
  intro h
  have h3 := F192.Y_pow_three
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  have hy : F192.Y = 1 := by linear_combination h - two
  rw [hy] at h3
  exact one_ne_zero (by linear_combination -h3 : (1 : E) = 0)

theorem one_add_Y_sq_ne : (1 + F192.Y ^ 2 : E) ≠ 0 := by
  intro h
  have h3 := F192.Y_pow_three
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  have hy2 : F192.Y ^ 2 = 1 := by linear_combination h - two
  exact one_ne_zero (by linear_combination -h3 + F192.Y * hy2 : (1 : E) = 0)

/-- **The honest quotient table meets the verifier's two claims** (the quotient claim and the sum
claim) at every good challenge and non-degenerate masks, for a witness of the statement's relation:
F1's completeness (`honest_accepts`) at the masked first message, passed to the table holding the
second message (`accepts_table_of_honest`), read as claims (`claims_iff_accepts`), which are the
stack's (`claimsMap_place_quotient`, `mle_eq_sum_eqBits`). -/
theorem hTQD (stmt : Statement) (w : Secret) (hw : Relation stmt w) :
    ∀ c, good P₀D (gKD w) vanD c → ∀ m, ClaimsND (K := K) P₀D (gKD w) vanD c m →
      (openQ deployedRep P₀D F192.Y).claims (c, redMsgs P₀D (gKD w) vanD c.1.1.2 m)
          (TQD w c.1.1.1 m) =
        valsQ P₀D (stmtWD stmt) F192.Y c (redMsgs P₀D (gKD w) vanD c.1.1.2 m) := by
  intro c hc m hnd
  -- F1's completeness at the masked first message
  have hsat := relation_honestD stmt w hw m
  have hcells := cells_committed P₀D (gKD w) vanD hvanD m 0
  have hab : ¬ Completeness.Reduction.BadAB instD (committed (E := E) (gKD w) vanD m)
      c.1.1.1.1 c.1.1.1.2.1 := by
    rintro ⟨i, hi | hi⟩
    · exact hc.1.1 i (by rw [← hcells]; exact hi)
    · exact hc.1.2.1 i (by rw [← hcells]; exact hi)
  have hdg : ¬ Completeness.Reduction.Degenerate instD (committed (E := E) (gKD w) vanD m)
      c.1.1.1.1 c.1.1.1.2.1 c.1.1.2 := by
    rintro (⟨k, hk⟩ | h0)
    · exact hnd.1.1 k k.isLt hk
    · rw [← Completeness.Reduction.claimDen_honest] at h0
      exact hnd.2 h0
  have hacc := Completeness.Reduction.honest_accepts instD (stmtWD stmt)
    (committed (E := E) (gKD w) vanD m) hsat c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2 hab hdg
  -- the second message's degrees, its gate quotient over `K`
  have hg22 : ∀ j, (committed (E := E) (gKD w) vanD m j).natDegree ≤ 2 ^ 22 + 2 := by
    rw [committed_eq]
    exact Completeness.natDegree_witnessOfTable_le (algebraMap K E) deployedBasis (cellsKD w) m
  obtain ⟨hh, hq, hgd⟩ := Completeness.honest_degrees instD (committed (E := E) (gKD w) vanD m)
    hg22 c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2
  have hlifts : ∀ j, committed (E := E) (gKD w) vanD m j ∈ lifts (algebraMap K E) := by
    rw [committed_eq]
    exact Completeness.witnessOfTable_mem_lifts (algebraMap K E) instD deployedBasis instD_basis _
  have hmem : (RD w c.1.1.1 m).qGate ∈ lifts (algebraMap K E) :=
    Completeness.qGate_mem_lifts (algebraMap K E) instD deployedBasis instD_basis _ hlifts
      c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2
  have hqK : (qGateKOf (RD w c.1.1.1 m)).map (algebraMap K E) = (RD w c.1.1.1 m).qGate := by
    unfold qGateKOf
    rw [dif_pos hmem]
    exact Classical.choose_spec ((lifts_iff_set_range _).mp hmem)
  have hgK : (qGateKOf (RD w c.1.1.1 m)).natDegree < 7 * 2 ^ 22 + 64 := by
    rw [← natDegree_map_eq_of_injective (algebraMap K E).injective, hqK]
    exact lt_of_le_of_lt hgd (by norm_num)
  obtain ⟨s1, s2, s3, s4⟩ := Completeness.slots_honest limbSysE (22 + 2 + 1 + 1) (by norm_num)
    (RD w c.1.1.1 m) (qGateKOf (RD w c.1.1.1 m)) hh (lt_of_le_of_lt hq (by norm_num)) hgK
  have hacc' := Completeness.accepts_table_of_honest (m := 22 + 2) instD.params rfl limbSysE.Y
    (fun b => limbSysE.ι (quotTableD w c.1.1.1 m b)) (stmtWD stmt)
    (committed (E := E) (gKD w) vanD m) c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2
    (instD.params.sigmaPoly.eval c.1.1.2) (Params.opened (committed (E := E) (gKD w) vanD m) c.1.1.2)
    s1 s2 (s3.trans hqK) s4 hacc
  rw [committed_eq] at hacc'
  -- the four claims
  have htt : ∀ i : Fin (22 + 2 + 1 + 1), 1 + QuotientSecurity.sq^[(i : ℕ)] c.1.1.2 ≠ 0 :=
    fun i => hnd.1.1 i i.isLt
  have hσ := Completeness.sigmaPoly_eq_wiringTableK (algebraMap K E) instD deployedBasis instD_basis
  have hv : redMsgs P₀D (gKD w) vanD c.1.1.2 m =
      (Params.opened (witnessOfTable fun b => algebraMap K E (witTableD w m b)) c.1.1.2,
        P₀D.sigmaPoly.eval c.1.1.2) := by
    unfold redMsgs
    rw [committed_eq]
  have hnz := hnd.2
  rw [hv] at hnz
  obtain ⟨-, -, c3, c4⟩ := (claims_iff_accepts instD.params instD.basis le24 instD.cellEquiv
    (fun x => cantorCells_point (n := 22) instD.basis le24 x) rfl
    (fun b => algebraMap K E (witTableD w m b))
    (fun b => algebraMap K E (Completeness.wiringTableK deployedBasis instD.wiring b)) hσ
    (fun b => limbSysE.ι (quotTableD w c.1.1.1 m b)) F192.Y one_add_Y_ne one_add_Y_sq_ne
    (stmtWD stmt) c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2
    (instD.params.sigmaPoly.eval c.1.1.2)
    (Params.opened (witnessOfTable fun b => algebraMap K E (witTableD w m b)) c.1.1.2)
    htt hnz).mpr hacc'
  -- the stack's claims are the table's
  have e30 : (2 : ℕ) ^ (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) = 2 ^ 30 := by norm_num
  have hQ := quotient_supportD (RD w c.1.1.1 m) (qGateKOf (RD w c.1.1.1 m))
  funext i
  fin_cases i
  · have h1 := claimsMap_place_quotient (K := K) (E := E) (natTableD (quotTableD w c.1.1.1 m)) hQ
      ![pointQ P₀D F192.Y c (redMsgs P₀D (gKD w) vanD c.1.1.2 m), pointS F192.Y] 0
    have h2 := mle_eq_sum_eqBits (V := 22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) (quotTableD w c.1.1.1 m)
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) c.1.1.2)
        (P₀D.vCells.eval c.1.1.2 / P₀D.claimDen c.1.1.1.1 c.1.1.1.2.1 c.1.1.2
          (redMsgs P₀D (gKD w) vanD c.1.1.2 m).1 (redMsgs P₀D (gKD w) vanD c.1.1.2 m).2)) c.1.2)
        (F192.Y / (1 + F192.Y))) (F192.Y ^ 2 / (1 + F192.Y ^ 2)))
    rw [e30] at h2
    refine h1.trans (h2.symm.trans ?_)
    rw [hv]
    exact c3
  · have h1 := claimsMap_place_quotient (K := K) (E := E) (natTableD (quotTableD w c.1.1.1 m)) hQ
      ![pointQ P₀D F192.Y c (redMsgs P₀D (gKD w) vanD c.1.1.2 m), pointS F192.Y] 1
    have h2 := mle_eq_sum_eqBits (V := 22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) (quotTableD w c.1.1.1 m)
      (QuotientSecurity.sumPoint (22 + 2) F192.Y)
    rw [e30] at h2
    refine h1.trans (h2.symm.trans ?_)
    exact c4

end PcsQuotient.EndToEnd
