-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/protocol.rs` (`prove`, `open`, `public_weight`) and
-- `crates/quotient/src/opening.rs` (`open`). The WHIR opening's prover is leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Whir.lean`'s `levelsA`, `roundA`, `stackTableA`,
-- `eqKernelA`, run by `Statement/Prover/Run.lean`'s `runFrom`); `openingScript` is its `openingFast`
-- with this protocol's weight table.
module

public import PcsQuotient.Verifier
public import PcsQuotient.Circuit
public import Statement.Prover.Whir

/-!
# The honest prover

The prover `Completeness` names (`Security.lean`), an executable program over a permutation `F` in any
monad, Keccak-256 the sponge over `F`: `proveWith F fuel circuit stmt cells masks witnessPad quotientPad`, the Rust's `prove`
then `open` (`protocol.rs`) step by step.

1. **The witness table**: the cells' polynomial in the novel basis (`Domain.coefficients`), and its
   masks, sixteen entries of the next chunk (entry `4i + j` the coefficient `i` of row polynomial
   `j`); stacked in its hidden layout with its padding (`Layout.stackOf`), committed by WHIR
   (`commitWith`), its root sent; `α, β, γ` drawn.
2. **The sum's polynomial** `h`: at cell `i`, `1/(α + w_i + β B(i)) + 1/(α + w_i + β B(σ(i)))`, plus
   the public weight times the cell on the public region; in the novel basis.
3. **The quotients** on the coset `β_{m+2} + span(β₀ … β_{m+1})`, four times the cells: the copy
   identity's quotient `q = ((h + public)·d·d' + d + d')/Z_cells` and the gate's
   `(V + X + C + Y·C)/Z_rows`, back to the novel basis; the **quotient table** (`h`, `q` and the gate's
   quotient by limbs, `quotientLayout`) committed, its root sent; `t` drawn.
4. **The values**: the four row polynomials (with their masks) and the wiring polynomial at `t`;
   the claims are the verifier's (`reduceWith`).
5. **The openings** (`proveOpeningWith`): leanVM's WHIR prover (`openingScript`) on each table's
   stack, run against the verifier's own program (mumbai's `runFrom`: the challenges squeezed from the
   sponge, each proof of work the first passing nonce below `fuel`).

The prover branches on no permutation answer other than through the challenges, and its only search
is the nonce search (mumbai's `runFrom`). It does not check that the quotients fit their layout (the
Rust's `fits`, true for a witness); the inverses are taken one by one (`x⁻¹`, `0⁻¹ = 0`) where the
Rust batches them, which differs only at a challenge where a denominator vanishes.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient.Domain PcsQuotient.Transcript

/-! ### Tables as stacks -/

/-- **A table's padding**: for each lane `l`, the words of its randomness `pad l 0, pad l 1, …`, in the order a
hidden stack takes them (`Table::hidden`: the Rust draws them from the lane's generator, ChaCha12 keyed by
Keccak-256 of the table's seed and the lane; the honest prover of the statement takes them uniform). -/
abbrev Padding : Type := ℕ → ℕ → K

/-- **The stack of a table** whose entry `i` is `entry i` (`Table::new`, `Table::hidden`, `opening.rs`). Public
layout: lane `l` holds block `b` whole. Hidden layout, pieces of `2^s`: a block lane's first piece is padding,
then its block, its pieces in pairs swapped on an odd lane (piece `k` holds the block's piece `k ⊕ 1`); the
overflow lane's first piece is padding, its pieces `1 … H` the held pieces plus the share lane's padding there
(`ρ`), the rest padding (its stream continuing); a random lane is padding. -/
def Layout.stackOf (L : Layout) (entry : ℕ → K) (pad : Padding) : Array K :=
  let lane := 2 ^ L.logLane
  let kinds := L.lanes.toArray
  match L.logPiece with
  | none => Array.ofFn (n := kinds.size * lane) fun p ↦
    match kinds.getD (p.val / lane) .random with
    | .block b => entry (b * lane + p.val % lane)
    | _ => 0
  | some s =>
    let piece := 2 ^ s
    let pieces := L.pieces.toArray
    let held := pieces.size
    let share := L.share.getD 0
    Array.ofFn (n := kinds.size * lane) fun p ↦
      let (l, i) := (p.val / lane, p.val % lane)
      match kinds.getD l .random with
      | .block b =>
        if i < piece then pad l i
        else if l % 2 = 0 then entry (b * lane + i)
        else entry (b * lane + ((i / piece) ^^^ 1) * piece + i % piece)
      | .overflow =>
        if i < piece then pad l i
        else if i < (held + 1) * piece then
          entry (pieces.getD (i / piece - 1) 0 * piece + i % piece) + pad share i
        else pad l (i - held * piece)
      | .random => pad l i

/-- A claim's weight on a stack, tabulated once (`Layout::tensors`, `opening.rs`): its lane and piece scales
(`Layout.scales`), and the `eq` tables of its lane coordinates and of its coordinates below a piece. -/
structure ClaimWeights where
  /-- What each lane holds, and the share lane (the layout's, as arrays: one lookup a position). -/
  kinds : Array Lane
  share : Option ℕ
  /-- The layout's piece. -/
  logPiece : Option ℕ
  lanes : Array E
  pieces : Array E
  low : Array E
  pieceLow : Array E

/-- The tables of a claim's weight on `L`. -/
def Layout.claimWeights (L : Layout) (c : Claim) : ClaimWeights :=
  ⟨L.lanes.toArray, L.share, L.logPiece, (L.scales c.point).1.toArray, (L.scales c.point).2.toArray,
    eqKernelA (c.point.take L.logLane), eqKernelA (c.point.take (L.logPiece.getD 0))⟩

/-- **A claim's weight at entry `y` of lane `l`** (`Layout::weight_at`, `opening.rs`), from its tables
(`Layout.claimWeights L c`): public layout, its lane scale times its `eq` at `y`; hidden layout, zero on a
first piece; on a block lane, its lane scale times its `eq` at `y` with the piece pair swapped on an odd lane;
on the overflow and share lanes, the held piece's scale times its `eq` below the piece; zero on the other
random lanes. -/
def Layout.weightAt (_L : Layout) (w : ClaimWeights) (l y : ℕ) : E :=
  match w.logPiece with
  | none => w.lanes.getD l 0 * w.low.getD y 0
  | some s =>
    let piece := y >>> s
    if piece = 0 then 0
    else
      match w.kinds.getD l .random with
      | .block _ => w.lanes.getD l 0 * w.low.getD (y ^^^ ((l % 2) <<< s)) 0
      | .overflow => w.pieces.getD (piece - 1) 0 * w.pieceLow.getD (y % 2 ^ s) 0
      | .random =>
        if w.share = some l then w.pieces.getD (piece - 1) 0 * w.pieceLow.getD (y % 2 ^ s) 0 else 0

/-- The witness table's masks: three coefficients of `K` for each of the four row polynomials. -/
abbrev Masks : Type := Fin 4 → Fin 3 → K

/-- The sixteen mask entries (`prove`, `protocol.rs`): entry `4i + j` is coefficient `i` of row
polynomial `j`, `i < 3`; the last four are zero. -/
def maskEntries (masks : Masks) : Array K :=
  Array.ofFn (n := 16) fun e ↦
    if e.val / 4 < 3 then masks (Fin.ofNat 4 (e.val % 4)) (Fin.ofNat 3 (e.val / 4)) else 0

/-- `public_weight` (`protocol.rs`): the weight of cell `i` of the public region, `γ^J` times its
bit's weight, `J = ⌊i / 2^8⌋` the word, or zero off the `X` and `Y` cells. -/
def publicCellWeight (i : ℕ) (γ : E) : E :=
  if i &&& 2 ≠ 0 then 0
  else bitWeight ((i &&& 1) ||| (((i >>> 2) &&& 63) <<< 1)) * γ ^ (i >>> 8)

/-- Limb `l` of an element of `E`. -/
def limbOf (x : E) (l : ℕ) : K := LeanVM.Prover.limbAt x l

/-! ### The WHIR opening -/

/-- **The weight table of the batched claims** in WHIR's variable order: entry `i` is the stack position
`⌊i / 64⌋ + 2^(logN−6)·(i mod 64)`, entry `⌊i / 64⌋` of lane `i mod 64`, where each claim weighs
`Layout.weightAt` (`open`, `opening.rs`). -/
def weightTable (L : Layout) (scales : List E) (claims : List Claim) : Array E :=
  let parts := (claims.zip scales).map fun (c, s) ↦ (L.claimWeights c, s)
  Array.ofFn (n := 2 ^ L.logN) fun i ↦
    parts.foldl (fun acc (w, s) ↦ acc + s * L.weightAt w (i.val % 64) (i.val / 64)) 0

/-- **The honest WHIR opening** of `claims` on the stack `stack`, as a script of the prover's moves
(mumbai's `openingFast` with this weight table): receive the batching challenge, then run the levels
from the batched claim with the stack table and the weight table. -/
def openingScript (L : Layout) (stack : Array K) (claims : List Claim) : Script Unit := do
  let c ← Script.sampleE
  let scales := powers c claims.length
  match Whir.ladder L.logN logInvRate with
  | none => return ()
  | some config =>
    let f₀ := stackTableA L.logN stack
    let W₀ := weightTable L scales claims
    let target := dot scales (claims.map (·.value))
    let quad ← roundA target W₀ f₀
    levelsA L.logN 0 config ⟨quad, [], []⟩ W₀ f₀

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **An opening proof** of `claims` on the table committed by `tree` (its stack `stack`): the root's two
halves sent first (`ProverState::add_root`), then the script run against the verifier's program from the
opening's sponge, with the table's tree as commitment `0`; `none` if a proof of work finds no nonce below
`fuel`. -/
def proveOpeningWith (fuel : ℕ) (L : Layout) (tree : Tree) (stack : Array K) (claims : List Claim) :
    m (Option Compile.Proof) := do
  let (r0, r1) := digestScalars tree.root
  let sp ← openingSpongeWith F L claims
  let sp ← absorb F sp r0 dsObserve
  let sp ← absorb F sp r1 dsObserve
  let program := verifyStackedOpening L.logN logInvRate
    (claims.map fun c ↦ (stackWeight L c, c.value))
  let r ← runFrom F fuel program (some (openingScript L stack claims)) sp [tree]
  return r.map fun t ↦ ⟨r0 :: r1 :: t.1, t.2⟩

/-! ### The reduction's prover -/

/-- The witness table's stack: the cells' coefficients `wHat`, then the masks, hidden with `pad`. -/
def witnessStack (logRows : ℕ) (wHat mask : Array K) (pad : Padding) : Array K :=
  let n := 2 ^ cellVars logRows
  (witnessLayout logRows).stackOf (fun i ↦ if i < n then wHat.getD i 0 else mask.getD (i - n) 0) pad

/-- **The quotient table's stack** (`prove`, `protocol.rs`), hidden with `pad`: chunk `c` of `2^m` entries
holds limb `⌊c / 16⌋` of `h` (`c mod 16 = 0`) or of `q` (`c mod 16 ∈ 4 … 7`, its digit `c mod 4`), or the
gate's quotient (`c ∈ {8, 9}`, its digit `c mod 4`). -/
def quotientStack (logRows : ℕ) (hHat qHat : Array E) (qGateHat : Array K) (pad : Padding) :
    Array K :=
  let n := 2 ^ cellVars logRows
  (quotientLayout logRows).stackOf (pad := pad) fun i ↦
    let c := i / n
    let src := c % 4 * n + i % n
    if c &&& 12 = 0 then limbOf (hHat.getD src 0) (c / 16)
    else if c &&& 12 = 4 then limbOf (qHat.getD src 0) (c / 16)
    else qGateHat.getD src 0

/-- `w_k(t)` for `k ≤ count`. -/
def digitsOf (t : E) (count : ℕ) : List E :=
  (List.range count).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t + ws.getLastD t]) [t]

/-- **The honest prover** over `F` (`prove` then `open`, `protocol.rs`): the proof of
`stmt` from the cells of a witness of `circuit`, with the masks `masks` and the tables' padding `witnessPad`, `quotientPad` (uniform, for zero knowledge),
trying `fuel` nonces per proof of work; `none` if a proof of work fails or the reduction rejects its own
challenges (the Rust panics). -/
def proveWith (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells : Array K) (masks : Masks)
    (witnessPad quotientPad : Padding) :
    m (Option Proof) := do
  let mv := cellVars circuit.logRows
  let n := 2 ^ mv
  let big := 4 * n
  let block := 2 ^ region
  -- The circuit's commitment, public.
  let sigmaHat := circuit.wiringTable
  let indexTree ← commitWith F mv sigmaHat
  -- 1. The witness table.
  let wHat := coefficients mv 0 cells
  let mask := maskEntries masks
  let wStack := witnessStack circuit.logRows wHat mask witnessPad
  let witnessTree ← commitWith F (mv + 1) wStack
  let c ← Chain.startWith F (label indexTree.root stmt)
  let witnessRoot := digestScalars witnessTree.root
  let c := (c.absorb witnessRoot.1).absorb witnessRoot.2
  let (α, c) ← c.squeezeWith F
  let (β, c) ← c.squeezeWith F
  let (γ, c) ← c.squeezeWith F
  -- 2. The sum's polynomial on the cells.
  let h : Array E := Array.ofFn (n := n) fun i ↦
    let common := α + ofK (cells.getD i.val 0)
    (common + β * ofK (point i.val))⁻¹ + (common + β * ofK (point (circuit.sigma.getD i.val 0)))⁻¹ +
      if i.val < block then publicCellWeight i.val γ * ofK (cells.getD i.val 0) else 0
  let hHat := coefficients mv 0 h
  -- 3. Both quotients, on a coset four times the cells.
  let offset := betaAt (mv + 2)
  let offsets := chain offset (mv + 1)
  let wValues : Array K := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦
    if i.val < n then wHat.getD i.val 0 else mask.getD (i.val - n) 0)
  let sigmaValues : Array K := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦
    sigmaHat.getD i.val 0)
  let q₀ : Array E := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦ hHat.getD i.val 0)
  let b := coordinates region
  let tau := rowVanishing mv
  let rowPoly (x : K) : K := ((chain x (mv - 1)).zip tau).foldl (fun acc (w, t) ↦ acc + t * w) 0
  let gammas : List E := [γ, γ * γ, (γ * γ) * (γ * γ)]
  -- Per block of `2^11` coset points: the public weights, `1/Z_cells`, and `1/Z_rows` by role.
  let blocks : Array (Array E × K × Array K) := Array.ofFn (n := big / block) fun hi ↦
    let base := hi.val * block
    let wAt (k : ℕ) : K := offsets.getD k 0 + point (base >>> k)
    let indicator := (List.range' region (mv - region)).foldl (fun acc k ↦ acc * (1 + wAt k)) 1
    let weights : Array E :=
      if indicator = 0 then #[ofK indicator]
      else (List.range region).foldl
        (fun ws k ↦
          let shift := (List.range' k (region - k)).foldl
            (fun acc j ↦ acc + b.getD (j - k) 0 * wAt j) 0
          let slope : E := 1 + (coordinateWeight k).getD (gammas.getD (k - 8) 0)
          let low := 1 + slope * ofK shift
          ws.map (· * low) ++ ws.map (· * (low + slope)))
        #[ofK indicator]
    let rowBase := rowPoly (offset + point base)
    (weights, (wAt mv)⁻¹, Array.ofFn (n := 4) fun r ↦ (rowBase + rowPoly (point r.val))⁻¹)
  let qValues : Array E := Array.ofFn (n := big) fun i ↦
    let (weights, cellVanishing, _) := blocks.getD (i.val / block) (#[], 0, #[])
    let w := wValues.getD i.val 0
    let common := α + ofK w
    let d := common + β * ofK (offset + point i.val)
    let dNext := common + β * ofK (sigmaValues.getD i.val 0)
    let pub := if i.val % block < weights.size then weights.getD (i.val % block) 0 * ofK w else 0
    ((q₀.getD i.val 0 + pub) * d * dNext + d + dNext) * ofK cellVanishing
  let qGateValues : Array K := Array.ofFn (n := big) fun i ↦
    let (_, _, rowInv) := blocks.getD (i.val / block) (#[], 0, #[])
    let at_ (j : ℕ) : K := wValues.getD j 0
    let (x, y, cc, v) := (at_ i.val, at_ (i.val ^^^ 1), at_ (i.val ^^^ 2), at_ (i.val ^^^ 3))
    (v + x + cc + y * cc) * rowInv.getD (i.val % 4) 0
  let qHat := coefficients (mv + 2) offset qValues
  let qGateHat := coefficients (mv + 2) offset qGateValues
  let qStack := quotientStack circuit.logRows hHat qHat qGateHat quotientPad
  let quotientTree ← commitWith F (mv + 4) qStack
  let quotientRoot := digestScalars quotientTree.root
  let c := (c.absorb quotientRoot.1).absorb quotientRoot.2
  let (t, _) ← c.squeezeWith F
  -- 4. The values at `t`.
  let digits := digitsOf t mv
  let a : Vector E 4 := Vector.ofFn fun j ↦
    novelEval wHat j.val 4 ((digits.drop 2).take (mv - 2)) +
      digits.getD mv 0 * novelEval mask j.val 4 ((digits.drop 2).take 2)
  let next := novelEval sigmaHat 0 1 (digits.take mv)
  let proof : ReductionProof := ⟨witnessRoot, quotientRoot, a, next⟩
  -- 5. The claims, and their openings.
  match ← reduceWith F circuit.logRows indexTree.root stmt proof with
  | none => return none
  | some r =>
    let some witness ← proveOpeningWith F fuel (witnessLayout circuit.logRows) witnessTree wStack
      [r.claims.witness] | return none
    let some wiring ← proveOpeningWith F fuel (wiringLayout circuit.logRows) indexTree sigmaHat
      [r.claims.wiring] | return none
    let some quotient ← proveOpeningWith F fuel (quotientLayout circuit.logRows) quotientTree qStack
      [r.claims.quotient, r.claims.sum] | return none
    return some ⟨proof, witness, wiring, quotient⟩

/-- **The honest prover of the membership statement** over `F`: `proveWith` on the membership circuit's
cells for the secret `w` (`membershipInputs`, `Circuit.cells`). -/
def proverWith (fuel : ℕ) (stmt : Statement) (w : Secret) (masks : Masks)
    (witnessPad quotientPad : Padding) : m (Option Proof) :=
  let circuit := membership logRows
  proveWith F fuel circuit stmt (circuit.cells (membershipInputs w)) masks witnessPad
    quotientPad

end With

end PcsQuotient

end
