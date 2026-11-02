-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Opening
import Bridge.Ntt
import Soundness.Hypotheses
import Completeness.Tables

/-!
# The extractor's reading of a stack

`PcsQuotient.secretOfStack` reads the witness table back from a stack through the hidden layout
(`Layout.readEntry`), takes the cells' polynomial to its values (`Domain.values`) and reads the input
rows' `V` cells. Here:

* the entries it reads are F2's `Layout.table` of the stack (`witnessEntries_eq`), the table
  `Compose.tabOf` holds;
* the cells it computes are, in `E`, F1's cells (`Instance.cellsOf`) of the first message
  `Compose.readW` reads off that table (`cells_eq`, through the additive transform's correctness,
  `Bridge/Ntt.lean`);
* so the input bits it reads are the bits, at the input rows, of any computation the cells hold
  (`inputBits_eq`).
-/

namespace Bridge

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- `readEntry_eq` at a layout given up to `layoutTr`. -/
theorem readEntry_eq' (L : PcsQuotient.Layout) (L' : WhirBridge.Layout) (hLL : layoutTr L = L')
    {s : ℕ} (hs : L.logPiece = some s) (hov : (layoutTr L).overflow < L.lanes.length)
    (q : Column L'.logN) (i : ℕ) :
    L.readEntry (fun j => q.values.toArray.getD j 0) i = L'.table q i := by
  subst hLL
  exact readEntry_eq L hs hov q i

/-- **The witness table's entries the extractor reads are F4's table of the stack**: entry `i` of
`inputBitsOfStack`'s `wHat` (the statement's read-back through the hidden witness layout) is
`Compose.tabOf (witnessLayout 22) q`'s, for every stack `q`. -/
theorem witnessEntries_eq (q : Column (WhirBridge.witnessLayout 22).logN) (i : ℕ) :
    (PcsQuotient.witnessLayout 22).readEntry (q.values.toArray.getD · 0) i =
      (WhirBridge.witnessLayout 22).table q i := by
  obtain ⟨oW, -, -⟩ := layoutOK_layouts 22 (by decide) (by decide)
  have hov : (layoutTr (PcsQuotient.witnessLayout 22)).overflow <
      (PcsQuotient.witnessLayout 22).lanes.length := by
    rcases oW with h | h
    · exact absurd h (by decide)
    · exact h.1
  exact readEntry_eq' _ _ (layoutTr_witnessLayout 22) (s := 8) rfl hov q i

theorem tabOf_get (q : Column (WhirBridge.witnessLayout 22).logN)
    (t : Fin (2 ^ (WhirBridge.witnessLayout 22).vars)) :
    (Compose.tabOf (WhirBridge.witnessLayout 22) q)[t] = (WhirBridge.witnessLayout 22).table q t.val := by
  simp [Compose.tabOf]

/-! ## The cells the extractor reads are F1's -/

/-- `inputBitsOfStack`'s table entries (`wHat`): the first `2^24` entries read back from the stack. -/
def witnessHat (q : Column (WhirBridge.witnessLayout 22).logN) : Array K :=
  Array.ofFn (n := 2 ^ 24) fun i =>
    (PcsQuotient.witnessLayout 22).readEntry (q.values.toArray.getD · 0) i.val

theorem witnessHat_size (q : Column (WhirBridge.witnessLayout 22).logN) :
    (witnessHat q).size = 2 ^ 24 := by simp [witnessHat]

theorem witnessHat_getD (q : Column (WhirBridge.witnessLayout 22).logN) {i : ℕ} (hi : i < 2 ^ 24) :
    (witnessHat q).getD i 0 = (WhirBridge.witnessLayout 22).table q i := by
  rw [← witnessEntries_eq q i]
  simp only [witnessHat, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, ↓reduceDIte,
    Option.getD_some]

theorem bitsToNat_snoc_false (b : Fin 24 → Bool) :
    LeanVM.Protocol.Whir.bitsToNat (Fin.snoc b false : Fin 25 → Bool) = Completeness.idx b := by
  unfold LeanVM.Protocol.Whir.bitsToNat Completeness.idx
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Bool.toNat_false, zero_mul, add_zero,
    Fin.coe_castSucc]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases b k <;> simp

/-- **The cells the extractor reads are F1's cells of the table**: for constants `c` whose basis is the
statement's `betaAt`, entry `p < 2^24` of `Domain.values 24 0 (witnessHat q)` (the statement's cells)
is, in `E`, F1's cell `p` (`cellsOf`) of the first message `readW` reads off F4's table of `q`. -/
theorem cells_eq (c : Compose.Reduce.Consts) (hβ : c.beta = PcsQuotient.Domain.betaAt)
    (h : Compose.IsCantor c.beta) (q : Column (WhirBridge.witnessLayout 22).logN) {p : ℕ}
    (hp : p < 2 ^ 24) :
    ofK ((PcsQuotient.Domain.values 24 0 (witnessHat q)).getD p 0) =
      (Soundness.inst c h).cellsOf
        (Compose.readW (Soundness.inst c h) (Compose.tabOf (WhirBridge.witnessLayout 22) q)).1
        (QuotientSecurity.cellOf p) := by
  have hB : Ntt.CantorUpTo 24 := by
    refine ⟨by rw [← hβ]; exact h.1, fun k hk => ?_⟩
    rw [← hβ]; exact h.2 k hk
  rw [Ntt.values_getD_tablePoly hB (by decide) 0 (witnessHat q) (witnessHat_size q) hp, zero_add,
    Ntt.point_eq_cantor hB (by decide) hp]
  show _ = (Soundness.inst c h).cellsOf (QuotientSecurity.witnessOfTable
    (Compose.tabFn (Compose.tabOf (WhirBridge.witnessLayout 22) q))) (QuotientSecurity.cellOf p)
  rw [Completeness.cellsOf_witnessTable]
  have hpt : (Ntt.cantorOf hB).point (Completeness.bitsOf 24 p) =
      (Compose.basisK c h).point (QuotientSecurity.cellOf p) := by
    simp only [QuotientSecurity.CantorBasis.point, Ntt.cantorOf, Compose.basisK, hβ]
    rfl
  have hent : (fun b : Fin 24 → Bool =>
      Compose.tabFn (Compose.tabOf (WhirBridge.witnessLayout 22) q) (Fin.snoc b false)) =
        fun b => ofK ((witnessHat q).getD (Completeness.idx b) 0) := by
    funext b
    rw [witnessHat_getD q (Completeness.idx_lt b)]
    have hi : ((LeanVM.Protocol.Whir.bitsEquiv 25 (Fin.snoc b false : Fin 25 → Bool)) : ℕ) =
        Completeness.idx b := by
      rw [LeanVM.Protocol.Whir.bitsEquiv_val]
      exact bitsToNat_snoc_false b
    simp only [Compose.tabFn, tabOf_get]
    exact congrArg (fun i => ofK ((WhirBridge.witnessLayout 22).table q i)) hi
  have e1 : ∀ (X : K) (P : Polynomial K),
      ofK (Polynomial.eval X P) = Polynomial.eval (ofK X) (P.map (algebraMap K E)) := by
    intro X P
    rw [Polynomial.eval_map]
    show algebraMap K E (Polynomial.eval X P) = Polynomial.eval₂ (algebraMap K E) (algebraMap K E X) P
    rw [Polynomial.eval₂_hom]
  rw [e1, Compose.map_tablePoly, hpt, ← Compose.point_basisE]
  exact congrArg (fun f => Polynomial.eval ((Compose.basisE c h).point (QuotientSecurity.cellOf p))
    (QuotientSecurity.tablePoly f)) hent.symm

theorem membership_logRows' (L : ℕ) : (PcsQuotient.membership L).logRows = L := rfl

theorem ofK_eq_bitF {x : K} {b : Bool} (h : ofK x = QuotientSecurity.bitF b) : decide (x = 1) = b := by
  have hinj : Function.Injective (algebraMap K E) := (algebraMap K E).injective
  cases b
  · have h0 : algebraMap K E x = algebraMap K E 0 := by
      rw [map_zero]; exact h
    have := hinj h0
    simp [this]
  · have h1 : algebraMap K E x = algebraMap K E 1 := by
      rw [map_one]; exact h
    simp [hinj h1]

/-- **The input bits the extractor reads off a stack are the computation's**: if F1's cells of the
table `q` holds (read by `readW`) hold a computation `v` of the deployed circuit (`Computes`), the
statement's `inputBitsOfStack` of `q` are `v`'s bits at the input rows. -/
theorem inputBits_eq (c : Compose.Reduce.Consts) (hβ : c.beta = PcsQuotient.Domain.betaAt)
    (h : Compose.IsCantor c.beta) (q : Column (WhirBridge.witnessLayout 22).logN)
    (v : Fin (2 ^ 22) → Bool)
    (hcomp : QuotientSecurity.deployed.Computes ((Soundness.inst c h).cellsOf
      (Compose.readW (Soundness.inst c h) (Compose.tabOf (WhirBridge.witnessLayout 22) q)).1) v)
    (hin : ∀ r ∈ (PcsQuotient.membership 22).inputs, r < 2 ^ 22) :
    PcsQuotient.inputBitsOfStack (PcsQuotient.membership 22) q.values =
      (PcsQuotient.membership 22).inputs.toList.map (QuotientSecurity.natVal v) := by
  have hlog := membership_logRows' 22
  unfold PcsQuotient.inputBitsOfStack
  simp only [hlog]
  refine List.map_congr_left fun r hr => ?_
  have hr' : r < 2 ^ 22 := hin r (Array.mem_def.mpr hr)
  have h4 : 4 * r + 3 < 2 ^ 24 := by omega
  have hc := cells_eq c hβ h q h4
  have hrow := (hcomp.2 ⟨r, hr'⟩).2.2.2
  rw [QuotientSecurity.rowCell_eq_cellOf] at hrow
  have e3 : (4 * (⟨r, hr'⟩ : Fin (2 ^ 22)).val + ((3 : Fin 4) : ℕ)) = 4 * r + 3 := rfl
  rw [e3, ← hc] at hrow
  rw [QuotientSecurity.natVal, dif_pos hr']
  exact ofK_eq_bitF hrow

end Bridge

/-- info: 'Bridge.witnessEntries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.witnessEntries_eq

/-- info: 'Bridge.cells_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.cells_eq

/-- info: 'Bridge.inputBits_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.inputBits_eq
