-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/opening.rs` (`Layout`, `lane_weights`, `seed`, `verify`) and
-- `crates/quotient/src/protocol.rs` (`witness_layout`, `wiring_layout`, `quotient_layout`). The WHIR
-- verifier is leanerVM's (`Statement/LeanVmVerifier.lean`, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0: `verifyStackedOpening`, `verifyWhir`, the program `Prog` and its run).
module

public import PcsQuotient.Reduction
public import Statement.LeanVmVerifier

/-!
# The openings: leanVM's WHIR, unchanged

A claim is on a **table**, a multilinear in `vars` variables over `K` that vanishes outside some
blocks of `2^(logN − 6)` entries; the table is committed as the **stack** of those blocks, one WHIR
lane each, in the order the `Layout` lists them (`opening.rs:36-97`), `64` lanes of `2^(logN − 6)`
words at most. A claim stays a plain multilinear claim on the whole table: its weight on the stack is
the claim's `eq`, read at each lane's block (`stackWeight`). All the claims on one commitment are
opened together, batched by the powers of one challenge, in one WHIR opening.

**The WHIR verifier is mumbai's** `verifyStackedOpening`, a transcription of leanVM's
`python-verifier/verifier.py` (`verify_stacked_opening`, `verify_whir`) at leanVM `c445e3d5`, the
commit `crates/verifier` vendors: it is generic in the weight (`StackClaim`, a weight on the stack
and a value), which is what `opening::verify` gives `verifier::whir::verify_whir`. It runs on
mumbai's proof format (`LeanVM.Protocol.Compile.Proof`): the scalar stream and **one full Merkle
path per query** (the raw form of `verifier::MerkleOpenings`); the Rust prover ships pruned paths,
which the Rust verifier expands into these (`MerkleOpenings::Pruned`, not formalized; the
differential test converts them).

**Two adaptations of mumbai's program, both in how it is run** (`openingWith`): the root is not
read from the stream (leanVM's stacked opening reads it there, `commitStack`) but given, as
`opening::verify` gives it to `verify_whir`, so the run starts with it as commitment `0`; and the
sponge is seeded as `opening::seed` seeds it: Keccak-256 of the label `"pcs-quotient-opening"` and
Keccak-256 of the root and the claims (`seedInput`, the IV's and the public input's words, then
one permutation, as leanVM's `Transcript::new`).
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ### Layouts -/

/-- `LANE_FOLD` (`opening.rs:27`): the first fold of leanVM's WHIR, `2^6` lanes. -/
def laneFold : ℕ := 6

/-- `LOG_INV_RATE` (`opening.rs:140`): WHIR's rate is `1/2`. -/
def logInvRate : ℕ := 1

/-- **Where a table can be nonzero, and how it is stacked** (`Layout`, `opening.rs:38-45`): lane
`l` holds the table's entries `[blocks[l] · 2^(logN−6), (blocks[l] + 1) · 2^(logN−6))`. -/
structure Layout where
  /-- The table's variables. -/
  vars : ℕ
  /-- The stack's variables: `64` lanes of `2^(logN − 6)` words. -/
  logN : ℕ
  /-- The block each lane holds. -/
  blocks : List ℕ

/-- The lanes' variables, `logN − 6`. -/
def Layout.logLane (L : Layout) : ℕ := L.logN - laneFold

/-- `Layout::new` (`opening.rs:49-65`): lanes for the leading `len` entries of each listed chunk of
`2^logChunk` entries, in that order. -/
def Layout.ofChunks (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : Layout :=
  let lane := 2 ^ (logN - laneFold)
  ⟨vars, logN, chunks.flatMap fun (chunk, len) ↦
    (List.range ((len + lane - 1) / lane)).map fun j ↦ chunk * 2 ^ (logChunk - (logN - laneFold)) + j⟩

/-- `wiring_layout` (`protocol.rs:89-92`): the wiring table is its own stack, `m` variables. -/
def wiringLayout (logRows : ℕ) : Layout :=
  let m := cellVars logRows
  Layout.ofChunks m m m [(0, 2 ^ m)]

/-- `witness_layout` (`protocol.rs:95-98`): the cells' polynomial (`2^m` coefficients), then its
masks, sixteen entries of the next chunk; `m + 1` variables. -/
def witnessLayout (logRows : ℕ) : Layout :=
  let m := cellVars logRows
  Layout.ofChunks (m + 1) m (m + 1) [(0, 2 ^ m), (1, 16)]

/-- `Q_SPILL` (`protocol.rs:34-37`): where `q` and the gate's quotient spill past whole chunks,
`11 · 2^10 − 2^11 + 64`. -/
def qSpill : ℕ := 9216 + 64

/-- `quotient_layout` (`protocol.rs:104-116`): `m + 6` variables, its chunks of `2^m` indexed by two
digits, `h` or `q`, that pair or the gate's quotient, and the extension's two limbs; stacked in lanes
of a quarter chunk. -/
def quotientLayout (logRows : ℕ) : Layout :=
  let m := cellVars logRows
  let n := 2 ^ m
  Layout.ofChunks (m + 6) m (m + 4)
    ((List.range 3).flatMap (fun e ↦
        [(16 * e, n), (16 * e + 4, n), (16 * e + 5, n), (16 * e + 6, n), (16 * e + 7, qSpill)]) ++
      [(8, n), (9, 3 * n / 4 + 64)])

/-! ### A claim's weight on the stack -/

/-- `eq(point, bits of index)`, the first coordinate the lowest bit (`eq_bits`, `opening.rs:100-104`).
-/
def eqBits (point : List E) (index : ℕ) : E :=
  point.zipIdx.foldl (fun w (p, k) ↦ w * if index.testBit k then p else 1 + p) 1

/-- Each lane's weight in a claim at `point`: `eq` of the point's high coordinates at the lane's
block (`lane_weights`, `opening.rs:92-96`). -/
def Layout.laneWeights (L : Layout) (point : List E) : List E :=
  L.blocks.map (eqBits (point.drop L.logLane))

/-- **A claim's weight at a stack point** `x` (the closure of `opening::verify`,
`opening.rs:256-277`, before the batching): the lane's coordinates of `x` first, then the six of the
lane's index; the claim's `eq` on the lane's coordinates times `Σ_l eq(block_l) · eq(l)`. -/
def stackWeight (L : Layout) (c : Claim) (x : List E) : E :=
  let low := x.take L.logLane
  let high := x.drop L.logLane
  eqEval (c.point.take L.logLane) low *
    dot (L.laneWeights c.point) ((List.range L.blocks.length).map (eqBits high))

/-! ### The opening check -/

/-- `LABEL` (`opening.rs:24`). -/
def openingLabel : List UInt8 := "pcs-quotient-opening".toUTF8.toList

/-- The eight little-endian bytes of each limb of an element of `E`, limb `0` first. -/
def eBytes (x : E) : List UInt8 := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- What the opening's seed hashes (`seed`, `opening.rs:151-161`): the root, then each claim's point
and value, each element as its limbs' little-endian bytes. -/
def openingSeedBytes (root : Digest) (claims : List Claim) : List UInt8 :=
  digestBytes root ++ claims.flatMap fun c ↦ (c.point ++ [c.value]).flatMap eBytes

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The opening check** over the permutation `F` (`opening::verify`, `opening.rs:222-288`): every
claim has the table's variables; the sponge seeded by Keccak-256 of the label and of the root and
the claims; then mumbai's `verifyStackedOpening` (one challenge, its powers batching the claims,
then `verifyWhir` at rate `1/2`) run on the opening proof with the root as commitment `0`, its
level-0 rows `64` words at height `logN − 6 + 1`; and nothing of the proof left unread
(`Transcript::finish`). -/
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
