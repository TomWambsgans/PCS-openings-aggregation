-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.Builder
import Field.F192

/-!
# Running the simulator's table builder

`Instance/Builder.lean`'s elimination, compiled and run on `F64 ⊂ F192` (`Field/F192.lean`, `E`'s
coordinates over `K` its limbs, `coordsF`), on the deployed layouts:

* `witness_layout(22)` (`40` lanes of `2^19` entries), the witness claim at the verifier's point
  `pointWc c` with its value `valWc c v`, for a sample challenge `c` and five values `v` — exactly
  `simTW`'s computation with `rep.coords` the limbs;
* (`BuilderQ.lean`) `quotient_layout(22)` (`63` lanes of `2^22` entries), its two claims at a sample
  point of the quotient claim's shape and at the sum claim's fixed point `pointSc Y`, for sample
  values — `simTQ`'s computation, at a point and values not tied to a `Params`.

Each run prints the entries and values of the table it builds (zero elsewhere) and whether its claims,
computed from the weights at those entries, are the claimed values. `#eval` interprets the code: a
claim's weight at one entry is about `10^3`–`10^4` products in `F192`, which take seconds here (the
witness run about two minutes, the quotient run, `BuilderQ.lean`, about half an hour).
-/

open QuotientZk.Instance QuotientZk.Instance.Builder Primitives

namespace QuotientZk.Test.Builder

/-- `F192`'s coordinates over `F64`: its limbs, `x = c₀ + c₁ Y + c₂ Y²`. -/
def coordsF (x : F192) : Fin 3 → F64 := ![x.limb 0, x.limb 1, x.limb 2]

/-- A sample element. -/
def el (a b c : UInt64) : F192 := F192.new a b c

/-- An oracle answer. -/
def out0 : QuotientZk.Deployed.Out := default

/-- A sample challenge: `α, β, γ, t, ρ`, the rest zero. -/
def chal : DChal F192 :=
  ((((el 3 5 7, el 11 13 17, el 19 23 29), el 0x9e3779b97f4a7c15 0x6a09e667f3bcc908 0xbb67ae8584caa73b),
      el 0x3c6ef372fe94f82b 0xa54ff53a5f1d36f1 0x510e527fade682d1),
    ((0, fun _ => out0), fun _ => 0), ((0, fun _ => out0), fun _ => 0), fun _ => out0)

/-- Sample five values. -/
def vals : Vals F192 := (![el 1 2 3, el 4 5 6, el 7 8 9, el 10 11 12], el 13 14 15)

/-- The claims of a sparse table, the weights evaluated once per distinct entry. -/
def claimsOf {ι Y : Type} [DecidableEq ι] [DecidableEq Y] {m : ℕ} (W : Fin m → ι → Y → F192)
    (sol : List ((ι × Y) × F64)) : List F192 :=
  let es := (sol.map Prod.fst).dedup
  (List.finRange m).map fun j => (es.map fun e => sparse sol e.1 e.2 • W j e.1 e.2).sum

/-- **The witness run**: `simTW`'s elimination. -/
def runW : IO Unit := do
  let w := wW chal
  let val := valWc chal vals
  let sol := solveElim (r := 1 * 3) (colOf coordsF w) (entryAt candsW (enumL Lw okW))
    (candsW.length + 40 * 2 ^ 19) (tgtOf coordsF fun _ : Fin 1 => val)
  IO.println s!"witness table: {sol.map fun p => ((p.1.1 : ℕ), (p.1.2 : ℕ), p.2.toU64)}"
  IO.println s!"claim met: {decide (claimsOf w sol = [val])}"

#eval runW

end QuotientZk.Test.Builder
