-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient

/-!
# The extractor's unique decoder and its hash-map inversion, tested

Compiled evaluation (`#guard`), at small sizes, of what `PcsQuotient/Decoder.lean` and
`PcsQuotient/Replay.lean` claim and the soundness proof does not need:

* the subspace polynomial `W_m` (`vanishing`) vanishes on the `2^m` points and only there among the
  next ones; the basis change `toMono` is the novel basis of mumbai's transforms (its monomial form,
  evaluated by Horner, is `novelFwd`'s encoding), and `fromMono` inverts it;
* **Gao's decoder recovers a lane within the unique-decoding radius**: at `κ = 4`, `R = 1`
  (`n = 32`, `k = 16`, radius `8`) for every number of wrong columns `0 … 8`, three words and error
  patterns each, and at `κ = 6`, `R = 1` (`n = 128`, `k = 64`, radius `32`) at `0`, `1`, `17` and `32`
  wrong columns;
* **the unique-decoding stage recovers a stack** with errors in the first columns, where the fast path
  (mumbai's `fastStacks`) finds none, on all `64` lanes: of a small stack (`μ = 9`, `16` columns, radius
  `4`), and of the smallest stack the extractor takes (`μ = 15`, `2^10` columns, radius `256`, at its
  Johnson threshold `724`), with a lane at the radius at that size (`256` wrong columns of `2^10`).

`#guard` runs in Lean's interpreter, where a product in `K` (`BF64`'s carry-less product, about `200`
big-number operations) takes about `35` microseconds: the file takes about five minutes, the `μ = 15`
checks nearly all of it.
* the replay with hash maps gives mumbai's evaluations of the lengths it keeps, and the inversion through
  the index reads back every leaf of a small tree committed through a transcript.

Not part of the statement; `lake env lean PcsQuotientTest/Decoder.lean` (from `formal/EndToEnd`, with
the statement built there) or `lake build PcsQuotientTest` here.
-/

open LeanVM.Parameters LeanVM.Extraction PcsQuotient.UniqueDecoding

namespace PcsQuotientTest.Decoder

/-- A pseudorandom element of `K`. -/
def kOf (seed i : ℕ) : K :=
  K.ofLane (UInt64.ofNat ((seed * 6364136223846793005 + i * 1442695040888963407 + 12345) % 2 ^ 64))

/-- A polynomial's value by Horner (coefficients lowest first). -/
def evalMono (p : Array K) (a : K) : K := p.foldr (fun c acc ↦ acc * a + c) 0

/-- `W_m` vanishes on `x_v`, `v < 2^m`, and nowhere on the next `2^m` points. -/
def vanishingTest (m : ℕ) : Bool :=
  (List.range (2 ^ m)).all (fun v ↦ evalMono (vanishing m) (K.ofBits v) == 0) &&
    (List.range (2 ^ m)).all (fun v ↦ evalMono (vanishing m) (K.ofBits (2 ^ m + v)) != 0)

/-- `toMono` is the novel basis: the monomial form of `Σ c_j X_j`, at `x_v`, is `novelFwd`'s entry. -/
def toMonoTest (κ R seed : ℕ) : Bool :=
  let c := Array.ofFn fun i : Fin (2 ^ κ) ↦ kOf seed i.val
  let p := toMono κ c
  let e := novelFwd κ R c
  (List.range (2 ^ (κ + R))).all fun v ↦ evalMono p (K.ofBits v) == e.getD v 0

/-- `fromMono` inverts `toMono`. -/
def roundTripTest (m seed : ℕ) : Bool :=
  let c := Array.ofFn fun i : Fin (2 ^ m) ↦ kOf seed i.val
  fromMono m (toMono m c) == c

/-- The message of lane `u` of the test words: pseudorandom novel coefficients. -/
def message (κ seed u : ℕ) : Array K := Array.ofFn fun i : Fin (2 ^ κ) ↦ kOf (seed + 7919 * u) i.val

/-- The columns of a word of `64` lanes, lane `u < lanes` the encoding of `message κ seed u` (the others
zero), its symbols changed (by `+ 1 + v`) at the columns `bad`. -/
def columns (κ R seed lanes : ℕ) (bad : List ℕ) : Array (List K) :=
  let enc := (List.range lanes).toArray.map fun u ↦ novelFwd κ R (message κ seed u)
  Array.ofFn fun v : Fin (2 ^ (κ + R)) ↦
    let wrong := decide (v.val ∈ bad)
    (List.range 64).reverse.map fun u ↦
      let s := (enc.getD u #[]).getD v.val 0
      if wrong then s + 1 + K.ofBits v.val else s

/-- A word read off its columns. (The columns are computed once, outside: a definition returning a
function may be eta-expanded by the compiler and recompute them at every column.) -/
def colAt (cols : Array (List K)) (v : ℕ) : List K := cols.getD v []

/-- `e` pseudorandom distinct columns of `2^m`. -/
def badColumns (m e seed : ℕ) : List ℕ :=
  ((List.range (2 ^ m)).map fun v ↦ ((v * 2654435761 + seed * 40503) % 2 ^ m)).dedup.take e

/-- Lane `0` decoded with `e` wrong columns. -/
def laneTest (κ R seed e : ℕ) : Bool :=
  let cols := columns κ R seed 1 (badColumns (κ + R) e seed)
  laneDecode κ R (colAt cols) 0 == some (message κ seed 0)

end PcsQuotientTest.Decoder

open PcsQuotientTest.Decoder

#guard vanishingTest 1 && vanishingTest 3 && vanishingTest 5
#guard toMonoTest 3 1 5 && toMonoTest 4 2 11 && toMonoTest 5 1 3
#guard roundTripTest 1 2 && roundTripTest 4 17 && roundTripTest 7 23

-- every number of errors within the radius `(32 − 16)/2 = 8`, three words each
#guard (List.range 9).all fun e ↦ (List.range 3).all fun s ↦ laneTest 4 1 (100 * s + e) e
-- `n = 128`, `k = 64`: radius `32`
#guard laneTest 6 1 1 0 && laneTest 6 1 2 1 && laneTest 6 1 3 17
#guard laneTest 6 1 4 32

/-- info: (1, 0, 1, true) -/
#guard_msgs in
-- `μ = 9` (`κ = 3`, `16` columns, radius `4`), all `64` lanes, two wrong columns among the first `8`:
-- the fast path finds no stack, the unique decoder one, the fast path's stack of the clean word
#eval
  let w := columns 3 1 77 64 [0, 5]
  let clean := columns 3 1 77 64 []
  ((fastStacks 9 1 (colAt clean)).length, (fastStacks 9 1 (colAt w)).length,
    (uniqueStacks 9 1 (colAt w)).length, uniqueStacks 9 1 (colAt w) == fastStacks 9 1 (colAt clean))

/-! ## The replay and the inversion with hash maps -/

namespace PcsQuotientTest.Decoder

/-- Keccak-f[1600], each call recorded as a forward query of the permutation with its answer. -/
abbrev LogM := StateM (Array (Common.PermutationQuery LeanVM.Semantics.KeccakState ×
  LeanVM.Semantics.KeccakState))

/-- One logged call. -/
def loggedKeccak (s : LeanVM.Semantics.KeccakState) : LogM LeanVM.Semantics.KeccakState := do
  let y := LeanVM.Semantics.keccakF1600 s
  modify (·.push (.forward s, y))
  return y

/-- **The inversion through a transcript**: a tree of `8` leaves of `64` words committed by logged
Keccak-f calls; the replay with hash maps gives mumbai's evaluations of `64` and `512` bytes, and the
leaves under the root, read through the preimage index, are the tree's. -/
def inversionTest : Bool :=
  let leaf : LeanVM.Protocol.Compile.Word := fun p ↦
    (List.range 64).map fun j ↦ K.ofLane (UInt64.ofNat (1000003 * (64 * p + j) + 7))
  let (tree, log) := (LeanVM.Prover.buildTreeM (m := LogM) loggedKeccak 3 leaf).run #[]
  let T := log.toList
  let fast := PcsQuotient.Replay.transcriptEvaluations [64, 512] T
  let slow := (LeanVM.keccakEvaluationsOfTranscript T).filter fun e ↦ e.1.length ∈ [64, 512]
  let index := PcsQuotient.Replay.preimageIndex fast
  let leaves := PcsQuotient.Replay.leavesUnder (PcsQuotient.Replay.preimageIn index) 64 3 tree.root
  decide (fast = slow) && fast.length == 15 &&
    (List.range 8).all fun p ↦ decide (leaves.getD p [] = leaf p)

end PcsQuotientTest.Decoder

#guard inversionTest

/-! ## The smallest stack the extractor takes -/

-- a lane at the radius at `n = 1024`, `k = 512`: `256` wrong columns
#guard laneTest 9 1 4 256

-- `μ = 15` (`κ = 9`, `2^10` columns, the Johnson threshold `724`), all `64` lanes, three wrong columns
-- among the first `2^9`: no fast candidate, and the unique decoder's one stack is the word's
#guard
  let w := columns 9 1 77 64 [0, 5, 300]
  (fastStacks 15 1 (colAt w)).isEmpty &&
    uniqueStacks 15 1 (colAt w) == [stackOf 15 ((List.range 64).map fun u ↦ message 9 77 u)]
