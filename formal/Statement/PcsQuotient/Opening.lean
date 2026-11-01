-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/opening.rs` (`Layout`, `Layout::new`, `Layout::hidden`, `scales`,
-- `seed`, `verify`) and `crates/quotient/src/protocol.rs` (`witness_layout`, `wiring_layout`,
-- `quotient_layout`, `quotient_chunks`); the hidden layout is `crates/quotient/HIDING.md`'s. The WHIR verifier
-- is leanerVM's (`Statement/LeanVmVerifier.lean`, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `verifyStackedOpening`, `verifyWhir`, the program `Prog` and its run).
module

public import PcsQuotient.Reduction
public import Statement.LeanVmVerifier

/-!
# The openings: leanVM's WHIR, unchanged

A claim is on a **table**, a multilinear in `vars` variables over `K` that vanishes outside some
blocks of `2^ℓ` entries, `ℓ = logN − 6`; the table is committed as a **stack** of at most `64` lanes of
`2^ℓ` words, as its `Layout` says. A claim stays a plain multilinear claim on the whole table: its weight
on the stack is the claim's `eq`, read wherever the stack holds the table's entries (`stackWeight`). All
the claims on one commitment are opened together, batched by the powers of one challenge, in one WHIR
opening.

* A **public** layout (`Layout.ofChunks`, `Layout::new`; the wiring table): lane `l` holds block
  `blocks[l]` whole.
* A **hidden** layout (`Layout.hidden`, `Layout::hidden`; the witness and the quotient tables, so that
  their roots and openings hide them, `HIDING.md`): pieces of `2^8` entries; every lane's first piece is
  random; block lane `l` holds its block's piece `k ⊕ (l mod 2)` at its piece `k ≥ 1`; the **overflow**
  lane (`L − 2`) holds, at its pieces `1, 2, …`, the pieces the block lanes give up and the chunks'
  tails, each plus a share `ρ`; the **share** lane (`L − 1`) is random, `ρ` at those pieces; the other
  random lanes sit on odd lanes. The weight is zero on the randomness and the same on the overflow and
  share lanes' held pieces, where `ρ` cancels (characteristic two): the claims are the table's.

**The WHIR verifier is mumbai's** `verifyStackedOpening`, a transcription of leanVM's
`python-verifier/verifier.py` (`verify_stacked_opening`, `verify_whir`) at leanVM `c445e3d5`, the commit
`crates/verifier` vendors: it is generic in the weight (`StackClaim`, a weight on the stack and a value),
which is what `opening::verify` gives `verifier::whir::verify_whir`. It runs on mumbai's proof format
(`LeanVM.Protocol.Compile.Proof`): the scalar stream and **one full Merkle path per query** (the raw form
of `verifier::MerkleOpenings`); the Rust prover ships pruned paths, which the Rust verifier expands into
these (`MerkleOpenings::Pruned`, not formalized; the differential test converts them).

**Two adaptations of mumbai's program, both in how it is run** (`openingWith`): the root is not read
from the stream (leanVM's stacked opening reads it there, `commitStack`) but given, as `opening::verify`
gives it to `verify_whir`, so the run starts with it as commitment `0`; and the sponge is seeded as
`opening::seed` seeds it: Keccak-256 of the label `"pcs-quotient-opening"` and Keccak-256 of the root and
the claims (`seedInput`, the IV's and the public input's words, then one permutation, as leanVM's
`Transcript::new`).
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ### Layouts -/

/-- `LANE_FOLD` (`opening.rs`): the first fold of leanVM's WHIR, `2^6` lanes. -/
def laneFold : ℕ := 6

/-- `LOG_PIECE` (`opening.rs`): a hidden lane's first piece is `2^8` random entries, more than the at most
`225` positions WHIR opens at its first level. -/
def logPiece : ℕ := 8

/-- `LOG_INV_RATE` (`opening.rs`): WHIR's rate is `1/2`. -/
def logInvRate : ℕ := 1

/-- What a lane of the stack holds (`Lane`, `opening.rs`). -/
inductive Lane where
  /-- The table's block (in a hidden layout, all of it but one piece, its pieces in pairs swapped on an
  odd lane). -/
  | block (b : ℕ)
  /-- Pieces of the table, at its pieces `1, 2, …` (`Layout.pieces`). -/
  | overflow
  /-- Randomness, but for the share lane's pieces `1, 2, …`. -/
  | random
  deriving DecidableEq, Inhabited

/-- **Where a table can be nonzero, and how it is stacked** (`Layout`, `opening.rs`). -/
structure Layout where
  /-- The table's variables. -/
  vars : ℕ
  /-- The stack's variables: lanes of `2^(logN − 6)` words. -/
  logN : ℕ
  /-- What each lane holds. -/
  lanes : List Lane
  /-- A hidden layout's piece, `2^s` entries; `none` for a public one. -/
  logPiece : Option ℕ
  /-- The table's pieces at the overflow lane's pieces `1, 2, …`: the piece each block lane gives up, in lane
  order, then the chunks' tails. -/
  pieces : List ℕ
  /-- The random lane holding the share `ρ` of the overflow lane's held pieces. -/
  share : Option ℕ

/-- The lanes' variables, `ℓ = logN − 6`. -/
def Layout.logLane (L : Layout) : ℕ := L.logN - laneFold

/-- What lane `l` holds (random past the last lane). -/
def Layout.laneAt (L : Layout) (l : ℕ) : Lane := L.lanes.getD l .random

/-- The overflow lane (`0` if none). -/
def Layout.overflowLane (L : Layout) : ℕ := (L.lanes.findIdx? (· = .overflow)).getD 0

/-- `Layout::new` (`opening.rs`): a public layout, a lane for each of the leading `len` entries' blocks of
each listed chunk of `2^logChunk` entries, in that order. -/
def Layout.ofChunks (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : Layout :=
  let lane := 2 ^ (logN - laneFold)
  ⟨vars, logN, chunks.flatMap (fun (chunk, len) ↦
    (List.range ((len + lane - 1) / lane)).map fun j ↦
      Lane.block (chunk * 2 ^ (logChunk - (logN - laneFold)) + j)), none, [], none⟩

/-- **`Layout::hidden`** (`opening.rs`) with pieces of `2^s` entries and `random` random lanes, `L` lanes in
all: a lane for each whole block of a chunk, the overflow lane `L − 2`, the share lane `L − 1`, and the other
random lanes on the odd lanes `2⌊k·P/(R−1)⌋ + 1`, `P = ⌊(L − 2)/2⌋`; the block lanes fill the rest in order.
The overflow lane holds the piece `l mod 2` of each block lane `l`'s block, then the chunks' tails, piece by
piece. (The Rust asserts the sizes; at the sizes `supported` admits they hold.) -/
def Layout.hidden (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) (random s : ℕ) : Layout :=
  let logLane := logN - laneFold
  let blocks := chunks.flatMap fun (chunk, len) ↦
    (List.range (len / 2 ^ logLane)).map fun j ↦ chunk * 2 ^ (logChunk - logLane) + j
  let tails := chunks.flatMap fun (chunk, len) ↦
    let first := chunk * 2 ^ (logChunk - logLane)
    let whole := len / 2 ^ logLane
    let tail := len - whole * 2 ^ logLane
    (List.range ((tail + 2 ^ s - 1) / 2 ^ s)).map fun j ↦ (first + whole) * 2 ^ (logLane - s) + j
  let total := blocks.length + 1 + random
  let pairs := (total - 2) / 2
  let randomLanes := (List.range (random - 1)).map fun k ↦ 2 * (k * pairs / (random - 1)) + 1
  let lanes : List Lane := ((List.range total).foldl
    (fun (acc : List Lane × ℕ) l ↦
      if l = total - 1 ∨ randomLanes.contains l then (acc.1 ++ [.random], acc.2)
      else if l = total - 2 then (acc.1 ++ [.overflow], acc.2)
      else (acc.1 ++ [.block (blocks.getD acc.2 0)], acc.2 + 1))
    ([], 0)).1
  let givenUp := (lanes.zipIdx).filterMap fun (lane, l) ↦ match lane with
    | .block b => some (b * 2 ^ (logLane - s) + l % 2)
    | _ => none
  ⟨vars, logN, lanes, some s, givenUp ++ tails, some (total - 1)⟩

/-- `WITNESS_RANDOM_LANES`, `QUOTIENT_RANDOM_LANES` (`protocol.rs`): seven random lanes each, the fewest with
which the openings hide the tables (`HIDING.md`). -/
def randomLanes : ℕ := 7

/-- `wiring_layout` (`protocol.rs`): the wiring table is public, its own stack, `m` variables. -/
def wiringLayout (logRows : ℕ) : Layout :=
  let m := cellVars logRows
  Layout.ofChunks m m m [(0, 2 ^ m)]

/-- `witness_layout` (`protocol.rs`): the cells' polynomial (`2^m` coefficients), then its masks, sixteen
entries of the next chunk; `m + 1` variables. Hidden: `32` block lanes, the overflow lane, `7` random lanes.
-/
def witnessLayout (logRows : ℕ) : Layout :=
  let m := cellVars logRows
  Layout.hidden (m + 1) m (m + 1) [(0, 2 ^ m), (1, 16)] randomLanes logPiece

/-- `Q_SPILL` (`protocol.rs`): where `q` and the gate's quotient spill past whole chunks,
`11 · 2^10 − 2^11 + 64`. -/
def qSpill : ℕ := 9216 + 64

/-- `quotient_chunks` (`protocol.rs`): chunks of `2^m` indexed by two digits, `h` or `q`, that pair or the
gate's quotient, and the extension's two limbs: `h` below `2^m`, `q` below `3 · 2^m` plus its spill, the
gate's quotient below `(2 − 1/4) · 2^m` plus `64`. -/
def quotientChunks (m : ℕ) : List (ℕ × ℕ) :=
  (List.range 3).flatMap (fun e ↦
      [(16 * e, 2 ^ m), (16 * e + 4, 2 ^ m), (16 * e + 5, 2 ^ m), (16 * e + 6, 2 ^ m),
        (16 * e + 7, qSpill)]) ++
    [(8, 2 ^ m), (9, 3 * 2 ^ m / 4 + 64)]

/-- `quotient_layout` (`protocol.rs`): `m + 6` variables, stacked in lanes of a quarter chunk. Hidden:
`55` block lanes, the overflow lane (the pieces the blocks give up and the spills), `7` random lanes. -/
def quotientLayout (logRows : ℕ) : Layout :=
  let m := cellVars logRows
  Layout.hidden (m + 6) m (m + 4) (quotientChunks m) randomLanes logPiece

/-- **The table's entry `i` read back from a stack** (`Table::read`, `opening.rs`): public layout, from the
lane holding its block; hidden layout, a held piece's entry is the sum of the overflow and share lanes' there,
any other from the block lane holding it (its piece pair swapped on an odd lane); zero where the layout holds
nothing. -/
def Layout.readEntry (L : Layout) (stack : ℕ → K) (i : ℕ) : K :=
  let lane := 2 ^ L.logLane
  match L.logPiece with
  | none =>
    match L.lanes.findIdx? (· = .block (i / lane)) with
    | some l => stack (l * lane + i % lane)
    | none => 0
  | some s =>
    let piece := 2 ^ s
    let p := i / piece
    match L.pieces.findIdx? (· = p) with
    | some k =>
      stack (L.overflowLane * lane + (k + 1) * piece + i % piece) +
        stack (L.share.getD 0 * lane + (k + 1) * piece + i % piece)
    | none =>
      match L.lanes.findIdx? (· = .block (p / 2 ^ (L.logLane - s))) with
      | some l => stack (l * lane + ((p % 2 ^ (L.logLane - s)) ^^^ (l % 2)) * piece + i % piece)
      | none => 0

/-! ### A claim's weight on the stack -/

/-- `eq(point, bits of index)`, the first coordinate the lowest bit (`eq_bits`, `opening.rs`). -/
def eqBits (point : List E) (index : ℕ) : E :=
  point.zipIdx.foldl (fun w (p, k) ↦ w * if index.testBit k then p else 1 + p) 1

/-- A claim's scales (`Layout::scales`, `opening.rs`): `eq` of the point's high coordinates at each block
lane's block (zero on the other lanes), and `eq` of the coordinates above a piece at each overflow piece. -/
def Layout.scales (L : Layout) (point : List E) : List E × List E :=
  (L.lanes.map fun
      | .block b => eqBits (point.drop L.logLane) b
      | _ => 0,
    match L.logPiece with
    | some s => L.pieces.map (eqBits (point.drop s))
    | none => [])

/-- **A claim's weight at a stack point** `x` (the closure of `opening::verify`, before the batching): the
lane's coordinates of `x` first, then the six of the lane's index. Public layout: the claim's `eq` on the
lane's coordinates times `Σ_l eq(block_l)·eq(l)`. Hidden layout: below the piece, the claim's `eq`; above,
the block lanes' `eq` with coordinate `s` flipped on odd lanes and the first piece's share taken out, and
the overflow pieces' `eq` on the overflow and share lanes. -/
def stackWeight (L : Layout) (c : Claim) (x : List E) : E :=
  let low := x.take L.logLane
  let high := x.drop L.logLane
  let laneEq (l : ℕ) : E := eqBits high l
  let (lanes, pieces) := L.scales c.point
  let partLow := c.point.take L.logLane
  let on (odd : ℕ) : E := (L.lanes.zipIdx).foldl (fun sum (lane, l) ↦ match lane with
    | .block _ => if l % 2 = odd then sum + lanes.getD l 0 * laneEq l else sum
    | _ => sum) 0
  match L.logPiece with
  | none => eqEval partLow low * (on 0 + on 1)
  | some s =>
    let below := eqEval (partLow.take s) (low.take s)
    let above := eqEval (partLow.drop (s + 1)) (low.drop (s + 1))
    let firstAbove := (partLow.drop (s + 1)).foldl (fun w p ↦ w * (1 + p)) 1
    let firstPiece := (low.drop s).foldl (fun w p ↦ w * (1 + p)) 1
    let block (c : E) : E := above * (1 + c + low.getD s 0) + firstAbove * (1 + c) * firstPiece
    let even := block (partLow.getD s 0)
    let odd := block (1 + partLow.getD s 0)
    let held := (pieces.zipIdx).foldl (fun sum (w, k) ↦ sum + w * eqBits (low.drop s) (k + 1)) 0
    let onOverflow := laneEq L.overflowLane + laneEq (L.share.getD 0)
    below * (even * on 0 + odd * on 1 + held * onOverflow)

/-! ### The opening check -/

/-- `LABEL` (`opening.rs`). -/
def openingLabel : List UInt8 := "pcs-quotient-opening".toUTF8.toList

/-- The eight little-endian bytes of each limb of an element of `E`, limb `0` first. -/
def eBytes (x : E) : List UInt8 := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- What the opening's seed hashes (`seed`, `opening.rs`): the root, then each claim's point and value,
each element as its limbs' little-endian bytes. -/
def openingSeedBytes (root : Digest) (claims : List Claim) : List UInt8 :=
  digestBytes root ++ claims.flatMap fun c ↦ (c.point ++ [c.value]).flatMap eBytes

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The opening check** over the permutation `F` (`opening::verify`): every claim has the table's
variables; the sponge seeded by Keccak-256 of the label and of the root and the claims; then mumbai's
`verifyStackedOpening` (one challenge, its powers batching the claims, then `verifyWhir` at rate `1/2`)
run on the opening proof with the root as commitment `0`, its level-0 rows `64` words at height
`logN − 6 + 1`; and nothing of the proof left unread (`Transcript::finish`). -/
def openingWith (L : Layout) (root : Digest) (claims : List Claim) (proof : Compile.Proof) :
    m Bool := do
  if claims.all (·.point.length = L.vars) then
    let iv ← keccak256With F openingLabel
    let statement ← keccak256With F (openingSeedBytes root claims)
    let seed ← F (seedInput iv statement)
    let program := verifyStackedOpening L.logN logInvRate
      (claims.map fun c ↦ (stackWeight L c, c.value))
    let height := L.logN - laneFold + logInvRate
    match ← run F program ⟨⟨seed, []⟩, proof.stream, proof.openings, [(root, height, 2 ^ laneFold)]⟩
      with
    | some (_, s) => return s.stream.isEmpty && s.openings.isEmpty
    | none => return false
  else return false

end With

end PcsQuotient

end
