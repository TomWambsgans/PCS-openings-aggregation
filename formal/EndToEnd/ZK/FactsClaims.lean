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

end PcsQuotient.EndToEnd
