-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The extractor's Merkle inversion, list decoding and transcript replay are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0: `Statement/Extractor.lean`'s `committedLeaves`, `leafAt`,
-- `fastStacks`, `decodeStacks`, and `Statement/LeanVm.lean`'s `keccakEvaluationsOfTranscript`,
-- `permutationQueries`, `lookupEvaluation`), applied here to the witness table; the replay and the
-- inversion with hash maps (`Replay.lean`) and the unique decoder (Gao's, `Decoder.lean`) are this
-- package's, each file crediting its sources.
module

public import PcsQuotient.Circuit
public import PcsQuotient.Verifier
public import PcsQuotient.Decoder
public import PcsQuotient.Replay
public import Statement.LeanVm

/-!
# The knowledge extractor

The fixed straight-line extractor of `KnowledgeSoundness` (`Security.lean`): from the statement, the
proof, the adversary's transcript of queries to the random permutation and **the public setup's tree**
(the circuit commitment's Merkle tree, read as its Keccak-256 evaluations, `Tree.evaluations`), a
secret. It reads nothing else: it neither queries the permutation, nor sees the verifier's queries,
nor runs the adversary again; it is deterministic and computable (every loop a traversal of an explicitly sized
list or array, a `for` over an explicit range, or a recursion on an explicit number), and runs in time
polynomial in the committed size and the transcript's length, not in the proof's.

1. **The witness table's root** (`witnessRootOf`): the first two scalars of the reduction's proof,
   as the verifier reads them (no hash is needed: the root rides the stream as its halves).
2. **The evaluations** (`Replay.transcriptEvaluations`): the transcript replayed as mumbai's
   `keccakEvaluationsOfTranscript` replays it (the byte strings whose whole sponge path the adversary
   queried forward), with hash maps, keeping the inputs of the two lengths the witness tree hashes
   (`merkleLengths`: a node's `64` bytes, a leaf's `512`); then the setup's evaluations and those,
   indexed (`Replay.preimageIndex`: each input's first answer, then for a digest and a length the
   inputs it answers).
3. **The committed word** (`witnessWord`, mumbai's `committedLeaves` and `leafAt` with the index,
   `Replay.leavesUnder`): the Merkle tree under the root inverted top down, a node's children the
   halves of its unique answered 64-byte preimage, a leaf the 64 words of its unique answered 512-byte
   preimage; zero leaves under an unanswered node. The witness table is committed at
   `μ = m + 1 = 25` variables and rate `1/2`: `2^20` leaves of `64` words; each of its `64` lanes is
   a Reed–Solomon word of `n = 2^20` symbols for messages of `k = 2^19` coefficients.
4. **The candidate stacks**, in three stages, each run only if the ones before give no witness:
   * **the fast path** (mumbai's `fastStacks`): each lane interpolated from its first `2^19` columns,
     for a word without errors there;
   * **the unique decoder** (`UniqueDecoding.uniqueStacks`, `Decoder.lean`): each lane decoded by
     Gao's decoder, which recovers its polynomial whenever the lane has at most `⌊(n − k)/2⌋ = 2^18`
     wrong columns, so the stack whenever the word agrees with the stack's encoding on at least
     `(n + k)/2 = 786432` of its `2^20` columns;
   * **the list decoder** (mumbai's `decodeStacks`): every stack whose encoding agrees with the word on
     at least the Johnson threshold of columns (`741549` at this shape, `0.7072·n`), by CompPoly's
     Guruswami–Sudan list decoder over `K` lane by lane with prefix pruning (at most `2^18` candidates
     at every admissible shape, mumbai's `LeanVM.candidates_ncard_le`).
5. **The secret** (`secretOfStack`): the table's first `2^m` entries, read back from a candidate stack
   through the witness table's hidden layout (`Layout.readEntry`: the blocks' pieces, the held pieces from
   the overflow lane), are the cells' polynomial in the Cantor novel basis; its
   values on the cells (`Domain.values`, `m · 2^m` operations) give each input
   row's `V` cell, read as a bit (`1` is true), and the input bits spell `x`, the siblings and the
   directions (`secretOfInputs`). The extractor returns the first candidate's secret that satisfies the
   relation (checked natively: `33` Keccak-256), `none` if no candidate's does.

**Cost** (read off the loops, not proved), in operations of `K` (an addition is an `xor`, a product a
carry-less product reduced), hash-map operations (`O(1)` expected) and byte comparisons; `Q` the
transcript's queries, `N` the evaluations read (the setup's `2^20 − 1`: `2^19` leaves and `2^19 − 1`
nodes, and the transcript's), `n = 2^20` columns, `k = 2^19`:

| Step | Cost |
| --- | --- |
| replay, evaluations (`Replay.lean`) | `Q` steps of `O(1)` hash-map operations on `200`-byte states, at most `680` bytes copied each; at most two paddings of at most `544` bytes compared per chain |
| index, inversion | `N` insertions keyed by inputs (at most `512` bytes) and `N` by digests; `2^20 − 1` node and `2^20` leaf lookups, `20·2^20` leaves copied |
| fast path (`fastStacks`) | `64` inverse transforms of `2^19` and forward of `2^20`: about `2^31.4` |
| unique decoder (`uniqueStacks`), when the fast path gives no witness | about `2^28.3` per lane plus `2^21.5` per wrong column of the lane: about `2^34.3` for a word with few errors, at most `2^45.7` |
| list decoder (`decodeStacks`), when neither gives a witness | multiplicity `m' = 1149`, `Y`-degree `ℓ = 1625`, `n·m'(m'+1)/2 = 2^39.3` interpolation conditions per lane (Lee–O'Sullivan); Mulders–Storjohann's reduction of an `(ℓ+1)×(ℓ+1)` matrix of degree `m'·n`, `(ℓ+1)³(m'n)² ≈ 2^92.3` per lane (`2^98.3` for the `64`), then Roth–Ruckenstein's roots; infeasible, as mumbai says of its own |
| per candidate | the read-back of `2^24` entries, one transform of `2^24`, `33` Keccak-256 |

**The list decoder is the worst case only.** It runs only when neither the fast path nor the unique
decoder gives a witness, so (the unique decoder recovering every stack within its radius) only for a
word whose every witness stack's encoding agrees with it on fewer than `786432` of its `2^20` columns:
beyond the unique-decoding radius (more than `2^18` wrong columns), within the Johnson radius. An honest
proof's word has no errors (the fast path); a word with a few wrong leaves takes the unique decoder.
That the unique decoder recovers every word within its radius is Gao's theorem, tested
(`PcsQuotientTest/Decoder.lean`), not proved here; the soundness proof does not need it (it needs only
that the list decoder, last, lists every candidate: `formal/EndToEnd/Soundness/Extract.lean`).
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Extraction

/-- The witness table's root a proof names: its first two scalars as a digest, if they are two halves.
-/
def witnessRootOf (proof : Proof) : Option Digest := digestOfScalars proof.reduction.witnessRoot

/-- **The input bits a stack spells** for `circuit`: the witness table's first `2^m` entries read back from
the stack through its hidden layout (`Layout.readEntry`), taken from the novel basis to the cells' values;
each input row's `V` cell read as a bit (`1` is true). -/
def inputBitsOfStack (circuit : Circuit) {μ : ℕ} (stack : Vector K (2 ^ μ)) : List Bool :=
  let mv := cellVars circuit.logRows
  let entries := stack.toArray
  let wHat := Array.ofFn (n := 2 ^ mv) fun i ↦
    (witnessLayout circuit.logRows).readEntry (entries.getD · 0) i.val
  let cells := Domain.values mv 0 wHat
  circuit.inputs.toList.map fun r ↦ decide (cells.getD (4 * r + 3) 0 = 1)

/-- **The secret a stack spells**: its input bits read as `x`, the siblings and the directions. -/
def secretOfStack (circuit : Circuit) {μ : ℕ} (stack : Vector K (2 ^ μ)) : Secret :=
  secretOfInputs (inputBitsOfStack circuit stack)

/-- The lengths of the inputs the witness table's Merkle tree hashes: a node's two digests (`64`
bytes) and a leaf's `2^laneFold = 64` words (`512` bytes). -/
def merkleLengths : List ℕ := [64, 8 * 2 ^ laneFold]

/-- **The committed word of the witness table**: under the root the proof names, the leaves the unique
preimages `pre` (a digest and a length to the input) commit to (mumbai's `committedLeaves`,
`Replay.leavesUnder`), `2^(μ−6+1)` leaves of `64` words for `μ = m + 1`; `none` if the proof names no
root. -/
def witnessWord (logRows : ℕ) (pre : Digest → ℕ → Option Bytes) (proof : Proof) :
    Option (ℕ → List K) :=
  (witnessRootOf proof).map fun root ↦
    let height := cellVars logRows + 1 - laneFold + logInvRate
    leafAt (Replay.leavesUnder pre (2 ^ laneFold) height root) height (2 ^ laneFold)

/-- **The extractor on given preimages**: the first candidate whose secret satisfies the relation, the
fast path's candidates (`fastStacks`) first, the unique decoder's (`UniqueDecoding.uniqueStacks`) only if
none of those does, the list decoder's (`decodeStacks`) only if none of those does. -/
def extractFrom (circuit : Circuit) (stmt : Statement) (pre : Digest → ℕ → Option Bytes)
    (proof : Proof) : Option Secret := do
  let word ← witnessWord circuit.logRows pre proof
  let μ := cellVars circuit.logRows + 1
  let witnessOf (stack : Vector K (2 ^ μ)) : Option Secret :=
    let w := secretOfStack circuit stack
    if Relation stmt w then some w else none
  (fastStacks μ logInvRate word).findSome? witnessOf <|>
    (UniqueDecoding.uniqueStacks μ logInvRate word).findSome? witnessOf <|>
    (decodeStacks μ logInvRate word).findSome? witnessOf

/-- **The extractor in the random-permutation model**, for a circuit: `extractFrom` on the unique
preimages of the public setup's Keccak-256 evaluations `setupEvals` (the circuit commitment's tree,
`Tree.evaluations`) then the transcript's (`Replay.transcriptEvaluations`, mumbai's
`keccakEvaluationsOfTranscript` of `permutationQueries`, of the lengths `merkleLengths`), indexed once
(`Replay.preimageIndex`). `Security.lean`'s `extractor` is this at the membership circuit. -/
def transcriptExtractorFor (circuit : Circuit) (stmt : Statement)
    (setupEvals : List (Bytes × Digest)) (T : Common.OracleQueryLog) (proof : Proof) :
    Option Secret :=
  let paths := setupEvals ++
    Replay.transcriptEvaluations merkleLengths (LeanVM.permutationQueries T)
  let index := Replay.preimageIndex paths
  extractFrom circuit stmt (Replay.preimageIn index) proof

end PcsQuotient

end
