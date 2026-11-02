-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Test.Builder

/-!
# Running the quotient table's builder

`Builder.lean`'s second run: `simTQ`'s elimination on `quotient_layout(22)` (`63` lanes of `2^22`
entries), its two claims at a sample point of the quotient claim's shape and at the sum claim's fixed
point, on `F192`. Interpreted, it takes about half an hour (a claim's weight at an entry is about
`7·10^3` products in `F192` there).
-/

open QuotientZk.Instance QuotientZk.Instance.Builder Primitives

namespace QuotientZk.Test.Builder

/-- A sample point of the quotient claim's shape (`30` coordinates, the extension's two last). -/
def pointQs : List F192 :=
  (List.range 28).map (fun i => el (UInt64.ofNat (2 * i + 3)) (UInt64.ofNat (i * i + 1)) 7) ++
    [F192.Y / (1 + F192.Y), F192.Y ^ 2 / (1 + F192.Y ^ 2)]

/-- **The quotient run**: `simTQ`'s elimination, two claims. -/
def runQ : IO Unit := do
  let w : Fin 2 → ιQ → YQ → F192 := Lq.claimW ![pointQs, pointSc F192.Y]
  let val : Fin 2 → F192 := ![el 0xdeadbeef 1 2, el 5 0xcafe 6]
  let sol := solveElim (r := 2 * 3) (colOf coordsF w) (entryAt candsQ (enumL Lq okQ))
    (candsQ.length + 63 * 2 ^ 22) (tgtOf coordsF val)
  IO.println s!"quotient table: {sol.map fun p => ((p.1.1 : ℕ), (p.1.2 : ℕ), p.2.toU64)}"
  IO.println s!"claims met: {decide (claimsOf w sol = [val 0, val 1])}"

#eval runQ

end QuotientZk.Test.Builder
