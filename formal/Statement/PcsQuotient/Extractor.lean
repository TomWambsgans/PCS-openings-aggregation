-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The extractor's Merkle inversion, list decoding and transcript replay are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0: `Statement/Extractor.lean`'s `committedLeaves`, `leafAt`,
-- `fastStacks`, `decodeStacks`, and `Statement/LeanVm.lean`'s `keccakEvaluationsOfTranscript`,
-- `permutationQueries`, `lookupEvaluation`), applied here to the witness table.
module

public import PcsQuotient.Circuit
public import PcsQuotient.Verifier
public import Statement.LeanVm

/-!
# The knowledge extractor

The fixed straight-line extractor of `KnowledgeSoundness` (`Security.lean`): from the statement, the
proof and the adversary's transcript of queries to the random permutation, a secret. It reads nothing
else: it neither queries the permutation, nor sees the verifier's or the setup's queries, nor runs the
adversary again; it is deterministic and computable (every loop a traversal of an explicitly sized
list or array, or a recursion on an explicit number), and runs in time polynomial in the committed size
and the transcript's length, not in the proof's.

1. **The witness table's root** (`witnessRootOf`): the first two scalars of the reduction's proof,
   as the verifier reads them (no hash is needed: the root rides the stream as its halves).
2. **The committed word** (mumbai's `committedLeaves`, `leafAt`): the Merkle tree under the root
   inverted through the Keccak-256 evaluations the transcript holds (`keccakEvaluationsOfTranscript`,
   the byte strings whose whole sponge path the adversary queried forward), top down, a node's
   children the halves of its unique answered 64-byte preimage, a leaf the 64 words of its unique
   answered 512-byte preimage; zero leaves under an unanswered node. The witness table is committed
   at `μ = m + 1 = 25` variables and rate `1/2`: `2^20` leaves of `64` words.
3. **The candidate stacks** (mumbai's `fastStacks`, then `decodeStacks` if no fast candidate works): the stacks whose WHIR
   encoding agrees with the word on at least the Johnson threshold of columns at this shape, listed by
   interpolation for a word without errors, then by CompPoly's Guruswami–Sudan list decoder over `K`
   lane by lane with prefix pruning (at most `2^18` candidates at every admissible shape, mumbai's
   `LeanVM.candidates_ncard_le`; infeasible at deployed sizes except on the fast path, as mumbai says
   of its own extractor).
4. **The secret** (`secretOfStack`): the table's first `2^m` entries, read back from a candidate stack
   through the witness table's hidden layout (`Layout.readEntry`: the blocks' pieces, the held pieces as
   the sum of the overflow and share lanes), are the cells' polynomial in the Cantor novel basis; its
   values on the cells (`Domain.values`, `m · 2^m` operations) give each input
   row's `V` cell, read as a bit (`1` is true), and the input bits spell `x`, the siblings and the
   directions (`secretOfInputs`). The extractor returns the first candidate's secret that satisfies the
   relation (checked natively: `33` Keccak-256), `none` if no candidate's does.

**Cost**, `N` the transcript's evaluations, `μ = 25`, `n = 2^20` columns, `L ≤ 2^18` the list size:
the Merkle inversion `N` evaluations then `2^21` scans of `N` pairs; the fast path `64` inverse and
forward additive transforms of `2^20`; the list decoder as mumbai's cost table (Lee–O'Sullivan on
`n·m'(m'+1)/2` conditions, `m'` its multiplicity); per candidate one transform of `2^24` and `33` hashes.
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

/-- **The committed word of the witness table**: under the root the proof names, the leaves the
answers `answers` (on the byte strings `keys`) commit to (mumbai's `committedLeaves`), `2^(μ−6+1)`
leaves of `64` words for `μ = m + 1`; `none` if the proof names no root. -/
def witnessWord (logRows : ℕ) (answers : Bytes → Option Digest) (keys : List Bytes) (proof : Proof) :
    Option (ℕ → List K) :=
  (witnessRootOf proof).map fun root ↦
    let height := cellVars logRows + 1 - laneFold + logInvRate
    leafAt (committedLeaves answers keys root height (2 ^ laneFold)) height (2 ^ laneFold)

/-- **The extractor on given evaluations**: the first candidate whose secret satisfies the relation,
the fast path's candidates (`fastStacks`) first, the list decoder's (`decodeStacks`) only if none of
those does. -/
def extractFrom (circuit : Circuit) (stmt : Statement) (answers : Bytes → Option Digest)
    (keys : List Bytes) (proof : Proof) : Option Secret := do
  let word ← witnessWord circuit.logRows answers keys proof
  let μ := cellVars circuit.logRows + 1
  let witnessOf (stack : Vector K (2 ^ μ)) : Option Secret :=
    let w := secretOfStack circuit stack
    if Relation stmt w then some w else none
  (fastStacks μ logInvRate word).findSome? witnessOf <|>
    (decodeStacks μ logInvRate word).findSome? witnessOf

/-- **The extractor in the random-permutation model**, for a circuit: `extractFrom` on the Keccak-256
evaluations of the transcript's permutation queries (mumbai's `keccakEvaluationsOfTranscript`,
`permutationQueries`, `lookupEvaluation`), computed once. `Security.lean`'s `extractor` is this at the
membership circuit. -/
def transcriptExtractorFor (circuit : Circuit) (stmt : Statement) (T : Common.OracleQueryLog)
    (proof : Proof) : Option Secret :=
  let paths := LeanVM.keccakEvaluationsOfTranscript (LeanVM.permutationQueries T)
  extractFrom circuit stmt (LeanVM.lookupEvaluation paths) (paths.map (·.1)) proof

end PcsQuotient

end
