-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The replay and the Merkle inversion are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0: `Statement/LeanVm.lean`'s `TranscriptReplay.step`, `keccakEvaluationsOfTranscript`,
-- `keccakPadded`, `lookupEvaluation`, and `Statement/Extractor.lean`'s `answerPairs`, `preimage`,
-- `subtreeLeaves`, `leafAt`), with their list lookups replaced by hash maps; the preimage index
-- (a digest and a length to the unique answered input) follows leanerVM's
-- `mumbai-no-more-extractors-in-statements` (`Extraction/Fast/Transcript.lean`'s `preimageIndex`,
-- `hitsOf`), rewritten on `Std.HashMap`.
module

public import Statement.LeanVm
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# The transcript's evaluations and the Merkle inversion, with hash maps

What the extractor (`Extractor.lean`) reads of the adversary's transcript and of the public setup's
tree, computed as mumbai's `keccakEvaluationsOfTranscript`, `lookupEvaluation`, `answerPairs`,
`preimage` and `subtreeLeaves` compute it (`formal/EndToEnd/Soundness/Replay.lean` proves the results
equal, on the inputs of the lengths the inversion reads), with hash maps where those scan lists:

* **The replay** (`replay`): the transcript's queries in order, oldest first, as mumbai's
  `TranscriptReplay.step`: a forward query `π x` that fixes a new edge extends the chain whose
  capacity (lanes `17 … 24`) is `x`'s, if there is one, by the block of their rates' XOR. The edges'
  inputs and outputs are hash sets (mumbai: a scan of the edges), the newest chain of each capacity
  a hash map (mumbai: a scan of the chains). A chain keeps its absorbed bytes while they are at most
  `maxAbsorbed = 4·136` bytes, the padding of the longest input the inversion reads (`512` bytes).
* **The evaluations** (`transcriptEvaluations lens`): each chain's message of a length in `lens` whose
  padding (`keccakPadded`) is the chain's bytes, with the first four lanes of its state: mumbai's
  evaluations of those lengths (mumbai unpads each chain by trying the `136` prefixes).
* **The preimage index** (`preimageIndex`): each input's first answer (mumbai's `lookupEvaluation`, a
  scan), then for a digest and a length the inputs of that length answered by it, with their first
  answers: one, or several (mumbai's `preimage`, a scan of the pairs per node).
* **The leaves** (`leavesUnder`): the `2^h` leaves under a digest, as mumbai's `subtreeLeaves`, the
  unique preimages read off the index.

**Cost**, `Q` the transcript's queries and `N` the evaluations: `Q` steps of `O(1)` expected hash-map
operations on `200`-byte states, and at most `544 + 136` bytes copied per chain; per chain at most two
paddings of at most `512` bytes compared; `N` insertions keyed by inputs of at most `512` bytes, `N` by
digests; then `2^h − 1` node and `2^h` leaf lookups, and `h·2^h` leaves copied by the concatenations.
-/

@[expose] public section

namespace PcsQuotient.Replay

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Extraction Common

/-! ### The replay -/

/-- The most bytes a chain keeps: four blocks of `136`, the padding of a `512`-byte input. -/
def maxAbsorbed : ℕ := 4 * rate

/-- A chain's bytes, while they are at most `maxAbsorbed` long; `none` past that. -/
def capBytes (bs : Bytes) : Option Bytes := if bs.length ≤ maxAbsorbed then some bs else none

/-- The bytes that take the state `s` to `x`: their rates' XOR, lanes `0 … 16` (as mumbai's
`TranscriptReplay.step`). -/
def blockBytes (s x : KeccakState) : Bytes :=
  (List.range 17).flatMap fun i ↦ wordBytes (Keccak.lane s i ^^^ Keccak.lane x i)

/-- **The replay's state**: the edges' inputs and outputs (hash sets of the states' lanes), the newest
chain of each capacity (a hash map from lanes `17 … 24` to the chain's state and its bytes while
short), and every chain, newest first. -/
structure State where
  /-- The inputs `x` of the edges `(x, π x)` fixed so far. -/
  inputs : Std.HashSet (Array UInt64)
  /-- Their outputs `π x`. -/
  outputs : Std.HashSet (Array UInt64)
  /-- The newest chain whose state has the capacity, with its bytes while at most `maxAbsorbed`. -/
  chains : Std.HashMap (List UInt64) (KeccakState × Option Bytes)
  /-- Every chain, newest first, with its bytes while at most `maxAbsorbed`. -/
  paths : List (KeccakState × Option Bytes)

/-- The zero state, the empty chain. -/
def State.init : State :=
  ⟨∅, ∅, (∅ : Std.HashMap (List UInt64) (KeccakState × Option Bytes)).insert
      ((Vector.replicate 25 0 : KeccakState).toList.drop 17) (Vector.replicate 25 0, some []),
    [(Vector.replicate 25 0, some [])]⟩

/-- **One query and its answer**, as mumbai's `TranscriptReplay.step`: a forward query `π x` that
fixes a new edge extends the newest chain with the capacity of `x`, if there is one, by the block that
takes its state to `x`; an inverse query extends no chain. -/
def State.step (σ : State) : PermutationQuery KeccakState × KeccakState → State
  | (.forward x, y) =>
    if σ.inputs.contains x.toArray then σ else
      match σ.chains[x.toList.drop 17]? with
      | some (s, bs) =>
        let bs' := bs.bind fun b ↦ capBytes (b ++ blockBytes s x)
        ⟨σ.inputs.insert x.toArray, σ.outputs.insert y.toArray,
          σ.chains.insert (y.toList.drop 17) (y, bs'), (y, bs') :: σ.paths⟩
      | none => ⟨σ.inputs.insert x.toArray, σ.outputs.insert y.toArray, σ.chains, σ.paths⟩
  | (.inverse y, x) =>
    if σ.outputs.contains y.toArray then σ else
      ⟨σ.inputs.insert x.toArray, σ.outputs.insert y.toArray, σ.chains, σ.paths⟩

/-- The replay of a transcript of permutation queries, oldest first. -/
def replay (T : List (PermutationQuery KeccakState × KeccakState)) : State :=
  T.foldl State.step State.init

/-- A chain's message of a length in `lens` (its padding the chain's bytes), with its digest. -/
def evaluationOf (lens : List ℕ) (p : KeccakState × Option Bytes) : Option (Bytes × Digest) :=
  p.2.bind fun bs ↦
    (lens.findSome? fun ℓ ↦ if keccakPadded (bs.take ℓ) = bs then some (bs.take ℓ) else none).map
      fun m ↦ (m, #v[p.1[0], p.1[1], p.1[2], p.1[3]])

/-- **The Keccak-256 evaluations a transcript holds, of the lengths `lens`**: mumbai's
`keccakEvaluationsOfTranscript`, newest first, its evaluations of the lengths in `lens` (each of
padding at most `maxAbsorbed`). -/
def transcriptEvaluations (lens : List ℕ) (T : List (PermutationQuery KeccakState × KeccakState)) :
    List (Bytes × Digest) :=
  (replay T).paths.filterMap (evaluationOf lens)

/-! ### The preimage index -/

/-- Each input's first answer among the evaluations (mumbai's `lookupEvaluation`). -/
def firstAnswers (P : List (Bytes × Digest)) : Std.HashMap Bytes Digest :=
  P.foldl (fun m e ↦ m.insertIfNew e.1 e.2) ∅

/-- The answered pairs: each input of the evaluations, in order, with its first answer (mumbai's
`answerPairs` of `lookupEvaluation`). -/
def answeredPairs (P : List (Bytes × Digest)) : List (Bytes × Digest) :=
  let first := firstAnswers P
  P.filterMap fun e ↦ first[e.1]?.map (e.1, ·)

/-- The inputs a digest and a length index: one input (perhaps several times), or several. -/
inductive Hits where
  /-- One input. -/
  | one (x : Bytes)
  /-- Two different inputs or more. -/
  | many

/-- An input added to the inputs of a key. -/
def Hits.add : Option Hits → Bytes → Hits
  | none, x => .one x
  | some (.one y), x => if y = x then .one y else .many
  | some .many, _ => .many

/-- One answered pair `(x, d)` added to the index, at the key of `d`'s lanes and `x`'s length. -/
def indexStep (idx : Std.HashMap (List UInt64 × ℕ) Hits) (p : Bytes × Digest) :
    Std.HashMap (List UInt64 × ℕ) Hits :=
  idx.insert (p.2.toList, p.1.length) (Hits.add idx[(p.2.toList, p.1.length)]? p.1)

/-- The index of answered pairs: a digest's lanes and a length to the inputs of that length it
answers. -/
def indexOf (pairs : List (Bytes × Digest)) : Std.HashMap (List UInt64 × ℕ) Hits :=
  pairs.foldl indexStep ∅

/-- **The preimage index** of evaluations. -/
def preimageIndex (P : List (Bytes × Digest)) : Std.HashMap (List UInt64 × ℕ) Hits :=
  indexOf (answeredPairs P)

/-- **The unique preimage** of length `len` of `d` the index holds (mumbai's `preimage`). -/
def preimageIn (idx : Std.HashMap (List UInt64 × ℕ) Hits) (d : Digest) (len : ℕ) : Option Bytes :=
  match idx[(d.toList, len)]? with
  | some (.one x) => some x
  | _ => none

/-! ### The leaves -/

/-- **The `2^h` leaves of `w` words under the digest `d`** through the unique preimages `pre` (mumbai's
`subtreeLeaves`): a node's children the halves of its 64-byte preimage, a leaf the words of its
preimage of `8w` bytes; zero leaves under a digest without one. -/
def leavesUnder (pre : Digest → ℕ → Option Bytes) (w : ℕ) : ℕ → Digest → Array (List K)
  | 0, d =>
    #[match pre d (8 * w) with
      | some x => bytesWords w x
      | none => List.replicate w 0]
  | h + 1, d =>
    match pre d 64 with
    | some x => leavesUnder pre w h (splitNode x).1 ++ leavesUnder pre w h (splitNode x).2
    | none => Array.replicate (2 ^ (h + 1)) (List.replicate w 0)

end PcsQuotient.Replay

end
