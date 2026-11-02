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
  random; the block lanes hold their blocks but for piece `0`, the first `32` in lanes `0 … 31`, the rest
  after the random lanes; lane `32` is the **overflow** lane, holding at its pieces `1, 2, …` the pieces
  the blocks give up and the chunks' tails; the random lanes follow it. The claims weigh the table only.
  The **gadget** (`gadgetWeight`): a fixed weight on nine first-piece entries of lanes `0, 31` / `1, 30` /
  `32`, batched as one more claim of value zero; the prover makes the entries cancel it (`HIDING.md`: it
  makes WHIR's lane rounds uniform).

**The WHIR verifier is mumbai's** `verifyStackedOpening`, a transcription of leanVM's
`python-verifier/verifier.py` (`verify_stacked_opening`, `verify_whir`) at leanVM `c445e3d5`, the commit
`crates/verifier` vendors: it is generic in the weight (`StackClaim`, a weight on the stack and a value),
which is what `opening::verify` gives `verifier::whir::verify_whir`. It runs on mumbai's proof format
(`LeanVM.Protocol.Compile.Proof`): the scalar stream and **one full Merkle path per query** (the raw form
of `verifier::MerkleOpenings`); the Rust prover ships pruned paths, which the Rust verifier expands into
these (`MerkleOpenings::Pruned`, not formalized; the differential test converts them).

**How mumbai's program is run** (`openingWith`): the sponge is seeded as `opening.rs` (version `2`) seeds
it, from an IV that hashes a prefix (label, version, the layout's identifier, sizes) and the claims, with a
zero public digest; the root rides the proof's first two scalars, absorbed and required to be the expected
root (as leanVM's stacked opening reads it, `commitStack`), and the run of `verifyStackedOpening` starts with
it as commitment `0`.
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
  /-- The table's block (in a hidden layout, all of it but its piece `0`). -/
  | block (b : ℕ)
  /-- Pieces of the table, at its pieces `1, 2, …` (`Layout.pieces`). -/
  | overflow
  /-- Randomness. -/
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
  /-- The table's pieces at the overflow lane's pieces `1, 2, …`: piece `0` of each block lane's block, in lane
  order, then the chunks' tails. -/
  pieces : List ℕ

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
      Lane.block (chunk * 2 ^ (logChunk - (logN - laneFold)) + j)), none, []⟩

/-- `OVERFLOW_LANE` (`opening.rs`): a hidden layout's overflow lane. -/
def overflowLaneIndex : ℕ := 32

/-- **`Layout::hidden`** (`opening.rs`) with pieces of `2^s` entries and `random` random lanes: the first `32`
whole blocks of the chunks in lanes `0 … 31` (random lanes where there are fewer), the overflow lane `32`, the
`random` random lanes, then the remaining blocks. The overflow lane holds piece `0` of each block lane's block,
in lane order, then the chunks' tails, piece by piece. (The Rust asserts the sizes; at the sizes `Supported`
admits they hold.) -/
def Layout.hidden (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) (random s : ℕ) : Layout :=
  let logLane := logN - laneFold
  let blocks := chunks.flatMap fun (chunk, len) ↦
    (List.range (len / 2 ^ logLane)).map fun j ↦ chunk * 2 ^ (logChunk - logLane) + j
  let tails := chunks.flatMap fun (chunk, len) ↦
    let first := chunk * 2 ^ (logChunk - logLane)
    let whole := len / 2 ^ logLane
    let tail := len - whole * 2 ^ logLane
    (List.range ((tail + 2 ^ s - 1) / 2 ^ s)).map fun j ↦ (first + whole) * 2 ^ (logLane - s) + j
  let lower := min blocks.length overflowLaneIndex
  let lanes : List Lane := (blocks.take lower).map .block ++
    List.replicate (overflowLaneIndex - lower) .random ++ [.overflow] ++ List.replicate random .random ++
    (blocks.drop lower).map .block
  let givenUp := lanes.filterMap fun
    | .block b => some (b * 2 ^ (logLane - s))
    | _ => none
  ⟨vars, logN, lanes, some s, givenUp ++ tails⟩

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
lane holding its block; hidden layout, a held piece's entry from the overflow lane, any other from the block
lane holding it; zero where the layout holds nothing. -/
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
    | some k => stack (L.overflowLane * lane + (k + 1) * piece + i % piece)
    | none =>
      match L.lanes.findIdx? (· = .block (p / 2 ^ (L.logLane - s))) with
      | some l => stack (l * lane + (p % 2 ^ (L.logLane - s)) * piece + i % piece)
      | none => 0

/-! ### A claim's weight on the stack, and the gadget -/

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
lane's coordinates times `Σ_l eq(block_l)·eq(l)`. Hidden layout: below the piece, the claim's `eq`; above, the
block lanes' `eq` with the first piece's share taken out, and the overflow pieces' `eq` on the overflow lane.
-/
def stackWeight (L : Layout) (c : Claim) (x : List E) : E :=
  let low := x.take L.logLane
  let high := x.drop L.logLane
  let laneEq (l : ℕ) : E := eqBits high l
  let (lanes, pieces) := L.scales c.point
  let partLow := c.point.take L.logLane
  let onBlocks : E := (L.lanes.zipIdx).foldl (fun sum (lane, l) ↦ match lane with
    | .block _ => sum + lanes.getD l 0 * laneEq l
    | _ => sum) 0
  match L.logPiece with
  | none => eqEval partLow low * onBlocks
  | some s =>
    let below := eqEval (partLow.take s) (low.take s)
    let above := eqEval (partLow.drop s) (low.drop s)
    let firstAbove := (partLow.drop s).foldl (fun w p ↦ w * (1 + p)) 1
    let firstPiece := (low.drop s).foldl (fun w p ↦ w * (1 + p)) 1
    let held := (pieces.zipIdx).foldl (fun sum (w, k) ↦ sum + w * eqBits (low.drop s) (k + 1)) 0
    below * ((above + firstAbove * firstPiece) * onBlocks + held * laneEq L.overflowLane)

/-- `GADGET` (`opening.rs`): the gadget's entries, nine. -/
def gadgetSize : ℕ := 9

/-- `gadget_lanes` (`opening.rs`): the lanes of the gadget's pattern `g`. -/
def gadgetLanes : ℕ → List ℕ
  | 0 => [0, 31]
  | 1 => [1, 30]
  | _ => [overflowLaneIndex]

/-- `gadget_beta` (`opening.rs`): the weight of the gadget's entry `i < 3` of a pattern, the unit of limb `i`. -/
def gadgetBeta (i : ℕ) : E :=
  E.ofLimbs (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0)

/-- `gadget_entry` (`opening.rs`): entry `i` of pattern `g`, in the last nine of the first piece. -/
def Layout.gadgetEntry (L : Layout) (g i : ℕ) : ℕ := 2 ^ L.logPiece.getD 0 - gadgetSize + 3 * g + i

/-- **The gadget's weight at a stack point** (`opening::verify`'s closure; `HIDING.md`): for each pattern `g`,
`Σ_{l ∈ lanes g} eq(l)` times `Σ_i β_i · eq(entry g i)` on the lane's coordinates. A hidden layout's opening
batches it as one more claim, of value zero, after the table's. -/
def gadgetWeight (L : Layout) (x : List E) : E :=
  let low := x.take L.logLane
  let high := x.drop L.logLane
  (List.range 3).foldl (fun acc g ↦
    acc + (gadgetLanes g).foldl (fun s l ↦ s + eqBits high l) 0 *
      (List.range 3).foldl (fun s i ↦ s + gadgetBeta i * eqBits low (L.gadgetEntry g i)) 0) 0

/-- **The opening's stack claims**: each claim's weight and value, then, in a hidden layout, the gadget, of value
zero (its scale the challenge's power after the claims', as `opening::verify` batches it). -/
def stackClaims (L : Layout) (claims : List Claim) : List StackClaim :=
  claims.map (fun c ↦ (stackWeight L c, c.value)) ++
    if L.logPiece.isSome then [(gadgetWeight L, 0)] else []
/-! ### The opening check

**The transcript's seed** (version `2`, `opening.rs`'s `prefix`, `iv`, `PUBLIC_DIGEST`): the IV is the
Keccak-256 of a prefix (the label `"pcs-quotient-opening"`, the version, the layout's identifier — the
Keccak-256 of its encoding —, its size and the rate, each number eight little-endian bytes) and of the
claims (each point's coordinates then its value, three limbs of eight little-endian bytes each); the public
digest is zero; the sponge starts at the permutation of the two (`seedInput`, as leanVM's `Transcript::new`).
The root is not hashed: it is the proof's first two scalars, which the verifier reads and requires to be the
root it expects. That is leanVM's transcript shape (`formal/WhirBridge`). -/

/-- `LABEL` (`opening.rs`). -/
def openingLabel : List UInt8 := "pcs-quotient-opening".toUTF8.toList

/-- `VERSION` (`opening.rs`). -/
def openingVersion : ℕ := 2

/-- A number as eight little-endian bytes. -/
def u64Bytes (n : ℕ) : List UInt8 := wordBytes n.toUInt64

/-- `encode_layout` (`opening.rs`): every field of the layout as numbers of eight bytes: the variables, the
stack's size, the lanes (each its kind, `0` a block, `1` the overflow, `2` random, then its block or `0`),
the piece (`0`, or `1` then it), the held pieces (their count, then each), and the gadget (`0` in a public
layout; in a hidden one `9`, then each pattern's lanes, their count then each, and its three entries). -/
def Layout.encoding (L : Layout) : List UInt8 :=
  let option : Option ℕ → List UInt8
    | none => u64Bytes 0
    | some v => u64Bytes 1 ++ u64Bytes v
  u64Bytes L.vars ++ u64Bytes L.logN ++ u64Bytes L.lanes.length ++
    L.lanes.flatMap (fun
      | .block b => u64Bytes 0 ++ u64Bytes b
      | .overflow => u64Bytes 1 ++ u64Bytes 0
      | .random => u64Bytes 2 ++ u64Bytes 0) ++
    option L.logPiece ++ u64Bytes L.pieces.length ++ L.pieces.flatMap u64Bytes ++
    match L.logPiece with
    | none => u64Bytes 0
    | some _ => u64Bytes gadgetSize ++ (List.range 3).flatMap fun g ↦
      u64Bytes (gadgetLanes g).length ++ (gadgetLanes g).flatMap u64Bytes ++
        (List.range 3).flatMap fun i ↦ u64Bytes (L.gadgetEntry g i)

/-- The eight little-endian bytes of each limb of an element of `E`, limb `0` first. -/
def eBytes (x : E) : List UInt8 := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- The claims as the IV hashes them: each point's coordinates then its value. -/
def claimBytes (claims : List Claim) : List UInt8 :=
  claims.flatMap fun c ↦ (c.point ++ [c.value]).flatMap eBytes

/-- The zero digest, the opening transcript's public digest (`PUBLIC_DIGEST`). -/
def zeroDigest : Digest := Vector.replicate 4 0

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The opening's initial sponge** over `F` (`iv`, `prefix`, `layout_id`, `Transcript::new`): the
permutation of the IV, Keccak-256 of the prefix and the claims, and the zero public digest. -/
def openingSpongeWith (L : Layout) (claims : List Claim) : m Sponge := do
  let layoutId ← keccak256With F L.encoding
  let pre := openingLabel ++ u64Bytes openingVersion ++ digestBytes layoutId ++ u64Bytes L.logN ++
    u64Bytes logInvRate
  let iv ← keccak256With F (pre ++ claimBytes claims)
  return ⟨← F (seedInput iv zeroDigest), []⟩

/-- **The opening check** over the permutation `F` (`opening::verify`): every claim has the table's
variables; from the opening's initial sponge, the proof's first two scalars absorbed and required to be the
expected root's halves; then mumbai's `verifyStackedOpening` (one challenge, its powers batching the claims,
then `verifyWhir` at rate `1/2`) run on the rest of the proof with the root as commitment `0`, its level-0 rows
`64` words at height `logN − 6 + 1`; and nothing of the proof left unread (`Transcript::finish`). -/
def openingWith (L : Layout) (root : Digest) (claims : List Claim) (proof : Compile.Proof) :
    m Bool := do
  if claims ≠ [] ∧ claims.all (·.point.length = L.vars) then
    match proof.stream with
    | x0 :: x1 :: rest =>
      let sp ← openingSpongeWith F L claims
      let sp ← absorb F sp x0 dsObserve
      let sp ← absorb F sp x1 dsObserve
      match digestOfScalars (x0, x1) with
      | some r =>
        if r.toList = root.toList then
          let program := verifyStackedOpening L.logN logInvRate
            (stackClaims L claims)
          let height := L.logN - laneFold + logInvRate
          match ← run F program ⟨sp, rest, proof.openings, [(root, height, 2 ^ laneFold)]⟩ with
          | some (_, s) => return s.stream.isEmpty && s.openings.isEmpty
          | none => return false
        else return false
      | none => return false
    | _ => return false
  else return false

end With

end PcsQuotient

end
