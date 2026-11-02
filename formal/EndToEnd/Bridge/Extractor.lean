-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Opening
import Soundness.Hypotheses

/-!
# The extractor's reading of a stack

`PcsQuotient.secretOfStack` reads the witness table back from a stack through the hidden layout
(`Layout.readEntry`), takes the cells' polynomial to its values (`Domain.values`) and reads the input
rows' `V` cells. Here its first step is F2's/F4's: the entries it reads are F2's `Layout.table` of the
stack (`witnessEntries_eq`), the table `Compose.tabOf` holds.
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

end Bridge

/-- info: 'Bridge.witnessEntries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.witnessEntries_eq
