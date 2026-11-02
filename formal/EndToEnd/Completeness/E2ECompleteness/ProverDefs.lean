-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Restates `E2ECompleteness.proveWithH` (`WithHash.lean`, itself `formal/Statement`'s `Prover.lean`
-- with Keccak-256 explicit) with its pure computations named. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- `Column`, the runners with a hash.
import E2ECompleteness.WithHash

/-!
# The honest prover's computations, named

`proveWithH` (`WithHash.lean`) computes its tables in `let`s. Here each pure computation is a
definition of its own, so that the bridge to the proof layers (`Prover*.lean`) can speak of it:

* `colOf μ a`: a stack array as WHIR's column of `2^μ` words (zero past the array: `commitWith`
  reads the stack with `getD`);
* the witness table: `witnessEntry n wHat mask` (the cells' coefficients, then the masks), its values
  on the coset `wValuesOf`;
* the sum's polynomial on the cells, `hValues`; the wiring polynomial on the coset, `sigmaValuesOf`;
  the sum's polynomial on the coset, `q0Of`; the public weights, `1/Z_cells` and `1/Z_rows` per block
  of `2^11` coset points, `blocksOf`; the two quotients' values on the coset, `qValuesOf`,
  `qGateValuesOf`; the quotient table's entry, `quotientEntry`;
* the four row values and the wiring value at `t`, `rowValuesAt`, `nextAt`;

and `proveSpec`, `proveWithH` written with them: **`proveWithH_eq_spec`** (`rfl`).
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

/-- **A stack as WHIR's column** of `2^μ` words: word `x` is the array's, zero past it (the
commitment reads the stack with `getD`, `stackWordFast`). -/
def colOf (μ : ℕ) (a : Array K) : Column μ := ⟨Vector.ofFn fun x ↦ a.getD x.val 0⟩

/-! ## The witness table -/

/-- **The witness table's entry `i`** (`witnessStack`, `Prover.lean`): the cells' coefficients
`wHat` below `n`, then the masks' entries. -/
def witnessEntry (n : ℕ) (wHat mask : Array K) (i : ℕ) : K :=
  if i < n then wHat.getD i 0 else mask.getD (i - n) 0

/-- **The witness table on the coset** `β_{m+2} + span(β₀ … β_{m+1})`, four times the cells. -/
def wValuesOf (logRows : ℕ) (wHat mask : Array K) : Array K :=
  values (cellVars logRows + 2) (betaAt (cellVars logRows + 2))
    (Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦
      if i.val < 2 ^ cellVars logRows then wHat.getD i.val 0
      else mask.getD (i.val - 2 ^ cellVars logRows) 0)

/-! ## The quotient table -/

/-- **The sum's polynomial on the cells**: at cell `i`, `1/(α + w_i + β B(i)) +
1/(α + w_i + β B(σ(i)))`, plus the public weight times the cell on the public region. -/
def hValues (logRows : ℕ) (cells : Array K) (sigma : Array ℕ) (α β γ : E) : Array E :=
  Array.ofFn (n := 2 ^ cellVars logRows) fun i ↦
    let common := α + ofK (cells.getD i.val 0)
    (common + β * ofK (point i.val))⁻¹ + (common + β * ofK (point (sigma.getD i.val 0)))⁻¹ +
      if i.val < 2 ^ region then publicCellWeight i.val γ * ofK (cells.getD i.val 0) else 0

/-- **The wiring polynomial on the coset.** -/
def sigmaValuesOf (logRows : ℕ) (sigmaHat : Array K) : Array K :=
  values (cellVars logRows + 2) (betaAt (cellVars logRows + 2))
    (Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦ sigmaHat.getD i.val 0)

/-- **The sum's polynomial on the coset.** -/
def q0Of (logRows : ℕ) (hHat : Array E) : Array E :=
  values (cellVars logRows + 2) (betaAt (cellVars logRows + 2))
    (Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦ hHat.getD i.val 0)

/-- The rows' polynomial at `x`, `Σ_{k < m−1} τ_k · w_k(x)` (`row_poly` of `prove`). -/
def rowPolyOf (logRows : ℕ) (x : K) : K :=
  ((chain x (cellVars logRows - 1)).zip (rowVanishing (cellVars logRows))).foldl
    (fun acc (w, t) ↦ acc + t * w) 0

/-- **Per block of `2^11` coset points**: the public weights, `1/Z_cells` and `1/Z_rows` by role. -/
def blocksOf (logRows : ℕ) (γ : E) : Array (Array E × K × Array K) :=
  Array.ofFn (n := 4 * 2 ^ cellVars logRows / 2 ^ region) fun hi ↦
    let base := hi.val * 2 ^ region
    let wAt (k : ℕ) : K :=
      (chain (betaAt (cellVars logRows + 2)) (cellVars logRows + 1)).getD k 0 + point (base >>> k)
    let indicator :=
      (List.range' region (cellVars logRows - region)).foldl (fun acc k ↦ acc * (1 + wAt k)) 1
    let weights : Array E :=
      if indicator = 0 then #[ofK indicator]
      else (List.range region).foldl
        (fun ws k ↦
          let shift := (List.range' k (region - k)).foldl
            (fun acc j ↦ acc + (coordinates region).getD (j - k) 0 * wAt j) 0
          let slope : E := 1 + (coordinateWeight k).getD ([γ, γ * γ, (γ * γ) * (γ * γ)].getD (k - 8) 0)
          let low := 1 + slope * ofK shift
          ws.map (· * low) ++ ws.map (· * (low + slope)))
        #[ofK indicator]
    let rowBase := rowPolyOf logRows (betaAt (cellVars logRows + 2) + point base)
    (weights, (wAt (cellVars logRows))⁻¹,
      Array.ofFn (n := 4) fun r ↦ (rowBase + rowPolyOf logRows (point r.val))⁻¹)

/-- **The copy identity's quotient on the coset**:
`((h + public)·d·d' + d + d') / Z_cells`. -/
def qValuesOf (logRows : ℕ) (wValues sigmaValues : Array K) (q₀ : Array E)
    (blocks : Array (Array E × K × Array K)) (α β : E) : Array E :=
  Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦
    let (weights, cellVanishing, _) := blocks.getD (i.val / 2 ^ region) (#[], 0, #[])
    let w := wValues.getD i.val 0
    let common := α + ofK w
    let d := common + β * ofK (betaAt (cellVars logRows + 2) + point i.val)
    let dNext := common + β * ofK (sigmaValues.getD i.val 0)
    let pub := if i.val % 2 ^ region < weights.size then
      weights.getD (i.val % 2 ^ region) 0 * ofK w else 0
    ((q₀.getD i.val 0 + pub) * d * dNext + d + dNext) * ofK cellVanishing

/-- **The gate's quotient on the coset**: `(V + X + C + Y·C) / Z_rows`, the four cells of a coset
point's row at its index with the low two bits flipped. -/
def qGateValuesOf (logRows : ℕ) (wValues : Array K) (blocks : Array (Array E × K × Array K)) :
    Array K :=
  Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦
    let (_, _, rowInv) := blocks.getD (i.val / 2 ^ region) (#[], 0, #[])
    let at_ (j : ℕ) : K := wValues.getD j 0
    let (x, y, cc, v) := (at_ i.val, at_ (i.val ^^^ 1), at_ (i.val ^^^ 2), at_ (i.val ^^^ 3))
    (v + x + cc + y * cc) * rowInv.getD (i.val % 4) 0

/-- **The quotient table's entry `i`** (`quotientStack`, `Prover.lean`): chunk `c = ⌊i / 2^m⌋`
holds limb `⌊c / 16⌋` of `h` (`c & 12 = 0`) or of `q` (`c & 12 = 4`), or the gate's quotient. -/
def quotientEntry (logRows : ℕ) (hHat qHat : Array E) (qGateHat : Array K) (i : ℕ) : K :=
  let n := 2 ^ cellVars logRows
  let c := i / n
  let src := c % 4 * n + i % n
  if c &&& 12 = 0 then limbOf (hHat.getD src 0) (c / 16)
  else if c &&& 12 = 4 then limbOf (qHat.getD src 0) (c / 16)
  else qGateHat.getD src 0

/-! ## The values at `t` -/

/-- **The four row values at `t`** (`a_j`): the row polynomials, with their masks. -/
def rowValuesAt (logRows : ℕ) (wHat mask : Array K) (t : E) : Vector E 4 :=
  let digits := digitsOf t (cellVars logRows)
  Vector.ofFn fun j ↦
    novelEval wHat j.val 4 ((digits.drop 2).take (cellVars logRows - 2)) +
      digits.getD (cellVars logRows) 0 * novelEval mask j.val 4 ((digits.drop 2).take 2)

/-- **The wiring polynomial at `t`** (`next`). -/
def nextAt (logRows : ℕ) (sigmaHat : Array K) (t : E) : E :=
  novelEval sigmaHat 0 1 ((digitsOf t (cellVars logRows)).take (cellVars logRows))

/-! ## The prover, with its computations named -/

section Spec

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **`proveWithH` with its computations named.** -/
def proveSpec (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells : Array K) (masks : Masks)
    (witnessPad quotientPad : Padding) : m (Option PcsQuotient.Proof) := do
  let mv := cellVars circuit.logRows
  let sigmaHat := circuit.wiringTable
  let indexTree ← commitWithH H mv sigmaHat
  let wHat := coefficients mv 0 cells
  let mask := maskEntries masks
  let wStack := witnessStack circuit.logRows wHat mask witnessPad
  let witnessTree ← commitWithH H (mv + 1) wStack
  let c ← startWithH H (label indexTree.root stmt)
  let witnessRoot := digestScalars witnessTree.root
  let c := (c.absorb witnessRoot.1).absorb witnessRoot.2
  let (α, c) ← squeezeWithH H c
  let (β, c) ← squeezeWithH H c
  let (γ, c) ← squeezeWithH H c
  let hHat := coefficients mv 0 (hValues circuit.logRows cells circuit.sigma α β γ)
  let wValues := wValuesOf circuit.logRows wHat mask
  let blocks := blocksOf circuit.logRows γ
  let qHat := coefficients (mv + 2) (betaAt (mv + 2))
    (qValuesOf circuit.logRows wValues (sigmaValuesOf circuit.logRows sigmaHat)
      (q0Of circuit.logRows hHat) blocks α β)
  let qGateHat := coefficients (mv + 2) (betaAt (mv + 2)) (qGateValuesOf circuit.logRows wValues blocks)
  let qStack := quotientStack circuit.logRows hHat qHat qGateHat quotientPad
  let quotientTree ← commitWithH H (mv + 4) qStack
  let quotientRoot := digestScalars quotientTree.root
  let c := (c.absorb quotientRoot.1).absorb quotientRoot.2
  let (t, _) ← squeezeWithH H c
  let proof : ReductionProof := ⟨witnessRoot, quotientRoot, rowValuesAt circuit.logRows wHat mask t,
    nextAt circuit.logRows sigmaHat t⟩
  match ← reduceWithH H circuit.logRows indexTree.root stmt proof with
  | none => return none
  | some r =>
    let some witness ← proveOpeningWithH H F fuel (witnessLayout circuit.logRows) witnessTree wStack
      [r.claims.witness] | return none
    let some wiring ← proveOpeningWithH H F fuel (wiringLayout circuit.logRows) indexTree sigmaHat
      [r.claims.wiring] | return none
    let some quotient ← proveOpeningWithH H F fuel (quotientLayout circuit.logRows) quotientTree
      qStack [r.claims.quotient, r.claims.sum] | return none
    return some ⟨proof, witness, wiring, quotient⟩

/-- **`proveWithH` is `proveSpec`**: the same program, its computations named. -/
theorem proveWithH_eq_spec (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells : Array K)
    (masks : Masks) (witnessPad quotientPad : Padding) :
    proveWithH H F fuel circuit stmt cells masks witnessPad quotientPad =
      proveSpec H F fuel circuit stmt cells masks witnessPad quotientPad := rfl

end Spec

end E2ECompleteness
