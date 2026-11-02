-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribes, at the level of the oracle calls, `crates/quotient/src/transcript.rs` (the reduction's
-- Keccak-256 chain, with `QuotientRpm`'s bytes), `crates/fiat_shamir/src/{lib,merkle}.rs` (the overwrite
-- duplex, grinding, `PrunedMerklePaths`; vendored from leanVM c445e3d5), `crates/pcs/src/whir.rs`
-- (`recursive_prover`'s order of absorbs, draws, commitments and grinds) and
-- `crates/quotient/src/opening.rs` (the opening's IV and seed).
import QuotientZk.Rom.Main
import QuotientRpm.Bytes

/-!
# The deployed prover as a skeleton

The skeleton (`skel`) is the honest prover of `crates/quotient` with its secret taken out: every
hash it computes is an operation of `Rom/Defs.lean` and every message it sends comes from a `msg`
operation. One oracle `G : Inp → Out` stands for both of Keccak's uses (`Inp = bytes ⊕ duplex
state`, `Out = digest × duplex state`): Keccak-256 of `m` is `(G (inl m)).1`, the permutation of a
duplex state `x` is `(G (inr x)).2`; for a random `G` these are independent random functions, the
two-oracle model of leanerVM `mumbai` (`KeccakCalls`) that F2 and F4 use.

* **The reduction** (`transcript.rs`, F4a's bytes): the seed `H(label)`; `α` from
  `H(state ‖ rootWords(witness root))`, `β`, `γ` from `H(state)`, `t` from
  `H(state ‖ rootWords(quotient root))`, `ρ` from `H(state ‖ the five values' words)`: five `chal`.
* **Merkle trees** (`pcs::merkle`, `fiat_shamir::merkle`): a leaf is `H(image)`, a node
  `H(left ‖ right)` (64 bytes); the secret tables' level-0 leaves are `leaf` operations (their rows
  are secret), every other leaf and every node a `pub` query. `prune` is `PrunedMerklePaths::prune`:
  the sorted distinct positions, then the siblings level by level, bottom up, left to right, a
  sibling sent only when it is not itself on a path.
* **The openings' duplex** (`fiat_shamir`): 25 lanes, rate 16; up to four scalars wait, scalar `i`
  in lanes `4i .. 4i + 4` as `(c0, c1, c2, tag)`; a permutation takes them, the rest of the rate
  zero, the capacity carried; a fifth scalar first permutes (a `pub` query: its output is not a
  challenge); a draw is a permutation of its own (`chal`), its challenge lanes `0 .. 2`. The seed
  is one permutation from the zero state with the IV in lanes `0 .. 4`. **Grinding**: the smallest
  nonce `n` (from `0`) such that absorbing `(n, 0, 0)` with tag `4` and permuting gives a lane 0
  with its low 17 bits zero, each try a `pub` query; the state after it is the successful try's
  (the Rust prover then absorbs the nonce and draws again: the same query).
* **An opening** (`whir.rs`, `recursive_prover`): the events of `Ev`, from the shape of the opening
  (`OpenShape`): send the root, draw `λ`; the lane rounds; per level the fold rounds, the next
  commitment and its out-of-domain sample, grinding, the query positions, the batching challenge,
  the multiproof and the intro message; at the last level the residual instead of a commitment and
  the tail rounds.

What the skeleton does not fix is what the prover sends: the `msg` answers (`Item`s, the scalars,
the codewords' rows of the deeper commitments, the opened rows), which `Proto.msgFn` gives.
-/

open OracleComp OracleSpec QuotientRpm

namespace QuotientZk.Deployed

/-! ## The oracle and the operations -/

/-- A Keccak-f[1600] state, 25 lanes. -/
abbrev KSt := Vector UInt64 25

/-- The oracle's inputs: Keccak-256's byte strings and the permutation's states. -/
abbrev Inp := List UInt8 ⊕ KSt

/-- The oracle's answers: a digest and a state (`H` reads the first, the permutation the second). -/
abbrev Out := Bytes32 × KSt

/-- What the prover sends between two challenges, in the order the skeleton reads it. -/
inductive Item where
  /-- Scalars sent and absorbed (tag 1); also the values the claims and IVs read. -/
  | scalars (l : List Limbs)
  /-- The rows of a codeword the prover commits to (each row a leaf's bytes). -/
  | rows (l : List (List UInt8))
  /-- The rows sent for a multiproof (each row as its words). -/
  | opened (l : List (List UInt64))
  /-- Bytes hashed but not sent (an opening's claims, for its IV). -/
  | bytes (l : List UInt8)

/-- A message: the items sent between two challenges. -/
abbrev Msg := List Item

/-- The secret tables: `0` the witness table `R1`, `1` the quotient table `R2`. -/
abbrev Tbl := Fin 2

/-- A leaf position: at most `2^23` leaves (the quotient table's level 0, `2^(28 - 6 + 1)`). -/
abbrev Pos := Fin (2 ^ 23)

/-- The operations of the deployed prover. -/
abbrev DSpec := OpSpec Inp Out Msg Tbl Pos

/-- Keccak-256. -/
def hashH (m : List UInt8) : OracleComp DSpec Bytes32 := do
  let a ← liftM (DSpec.query (.pub (.inl m)))
  return a.1

/-- The permutation. -/
def perm (x : KSt) : OracleComp DSpec KSt := do
  let a ← liftM (DSpec.query (.pub (.inr x)))
  return a.2

/-- A Fiat–Shamir Keccak-256 query (a chain state). -/
def chalH (m : List UInt8) : OracleComp DSpec Bytes32 := do
  let a ← liftM (DSpec.query (.chal (.inl m)))
  return a.1

/-- A Fiat–Shamir permutation (a draw). -/
def chalF (x : KSt) : OracleComp DSpec KSt := do
  let a ← liftM (DSpec.query (.chal (.inr x)))
  return a.2

/-- The digest of a secret table's level-0 leaf. -/
def leafH (k : Tbl) (x : ℕ) : OracleComp DSpec Bytes32 := do
  let a ← liftM (DSpec.query (.leaf k ⟨x % 2 ^ 23, Nat.mod_lt _ (by positivity)⟩))
  return a.1

/-- The next message. -/
def getMsg : OracleComp DSpec Msg := liftM (DSpec.query .msg)

/-! ## Merkle trees -/

/-- One level up: `H(left ‖ right)` for each pair. -/
def levelUp : List Bytes32 → OracleComp DSpec (List Bytes32)
  | a :: b :: rest => do
    let h ← hashH (a.toList ++ b.toList)
    let t ← levelUp rest
    return h :: t
  | _ => pure []

/-- The tree's levels, leaves first, after `depth` levels up (the root's level last). -/
def levels : ℕ → List Bytes32 → OracleComp DSpec (List (List Bytes32))
  | 0, leaves => pure [leaves]
  | d + 1, leaves => do
    let up ← levelUp leaves
    let rest ← levels d up
    return leaves :: rest

/-- The root: the last level's first digest. -/
def rootOf (lv : List (List Bytes32)) : Bytes32 := (lv.getLastD []).headD default

/-- Sorted distinct positions. -/
def sortedUnique (ps : List ℕ) : List ℕ := (ps.mergeSort (· ≤ ·)).dedup

/-- One level of `PrunedMerklePaths::prune`: the siblings sent and the next active positions. -/
def pruneLevel (lv : List Bytes32) : List ℕ → List Bytes32 × List ℕ
  | p :: q :: rest =>
    if q = p ^^^ 1 then
      let r := pruneLevel lv rest
      (r.1, (p / 2) :: r.2)
    else
      let r := pruneLevel lv (q :: rest)
      (lv.getD (p ^^^ 1) default :: r.1, (p / 2) :: r.2)
  | [p] => ([lv.getD (p ^^^ 1) default], [p / 2])
  | [] => ([], [])

/-- **`PrunedMerklePaths::prune`**: the sorted distinct positions and the siblings, level by level
(every level but the root's), bottom up. -/
def prune : List (List Bytes32) → List ℕ → List Bytes32
  | lv :: rest@(_ :: _), active =>
    let r := pruneLevel lv active
    r.1 ++ prune rest r.2.dedup
  | _, _ => []

/-! ## The reduction's chain (`transcript.rs`) -/

/-- The label's tag, `b"pcs-quotient-kc1"` (`QuotientRpm.tag`). -/
def kcTag : List UInt8 :=
  [0x70, 0x63, 0x73, 0x2d, 0x71, 0x75, 0x6f, 0x74, 0x69, 0x65, 0x6e, 0x74, 0x2d, 0x6b, 0x63, 0x31]

/-- The chain's public input: the circuit's commitment and the statement's 64 bytes. -/
structure Statement where
  indexRoot : Bytes32
  stmt : Vector UInt8 64

/-! ## The duplex (`fiat_shamir`) -/

/-- A duplex: the last permutation's output (only its capacity is kept) and the waiting scalars
with their tags. -/
structure Dx where
  st : KSt
  pend : List (Limbs × UInt64)

/-- The tag of a sent scalar and of a grinding nonce. -/
def tagObserve : UInt64 := 1
def tagNonce : UInt64 := 4

/-- The permutation's input: the waiting scalars in the rate, zeros, the capacity. -/
def Dx.input (d : Dx) : KSt :=
  Vector.ofFn fun i : Fin 25 =>
    if (i : ℕ) < 16 then
      match d.pend[(i : ℕ) / 4]? with
      | some (x, tag) =>
        match (i : ℕ) % 4 with
        | 0 => x.1
        | 1 => x.2.1
        | 2 => x.2.2
        | _ => tag
      | none => 0
    else d.st[i]

/-- Absorb a scalar: a fifth one first permutes what waits (a public query). -/
def Dx.absorb (d : Dx) (x : Limbs) (tag : UInt64) : OracleComp DSpec Dx :=
  if d.pend.length = 4 then do
    let s ← perm d.input
    return ⟨s, [(x, tag)]⟩
  else pure ⟨d.st, d.pend ++ [(x, tag)]⟩

/-- Absorb scalars with tag 1. -/
def Dx.absorbAll : Dx → List Limbs → OracleComp DSpec Dx
  | d, [] => pure d
  | d, x :: xs => do
    let d' ← d.absorb x tagObserve
    d'.absorbAll xs

/-- **A draw**: a Fiat–Shamir permutation; the challenge is its lanes `0 .. 2`. -/
def Dx.draw (d : Dx) : OracleComp DSpec (Limbs × Dx) := do
  let s ← chalF d.input
  return ((s[0], s[1], s[2]), ⟨s, []⟩)

/-- The seed: one permutation from the zero state, the IV's four words in lanes `0 .. 4`. -/
def seedInput (iv : Bytes32) : KSt :=
  Vector.ofFn fun i : Fin 25 =>
    if (i : ℕ) < 4 then LeanVM.Rpm.bytesLane ((iv.toList.drop (8 * (i : ℕ))).take 8) else 0

def seed (iv : Bytes32) : OracleComp DSpec Dx := do
  let s ← perm (seedInput iv)
  return ⟨s, []⟩

/-- The grinding bits of every level (`QUERY_GRINDING_BITS`). -/
def grindBits : ℕ := 17

/-- One grinding try: absorb the nonce with tag 4, permute (public queries). -/
def tryNonce (d : Dx) (n : UInt64) : OracleComp DSpec (Bool × Dx) := do
  let d' ← d.absorb (n, 0, 0) tagNonce
  let s ← perm d'.input
  return (s[0] % (2 ^ grindBits : UInt64) == 0, ⟨s, []⟩)

/-- **Grinding**: the smallest nonce from `n` on, within `fuel` tries. -/
def grind (d : Dx) : ℕ → UInt64 → OracleComp DSpec (UInt64 × Dx)
  | 0, n => pure (n, d)
  | fuel + 1, n => do
    let (ok, d') ← tryNonce d n
    if ok then pure (n, d') else grind d fuel (n + 1)

/-- The query positions of a draw: consecutive `b`-bit windows of `c0 + 2^64 c1 + 2^128 c2`. -/
def positionsOf (b : ℕ) (x : Limbs) : List ℕ :=
  let v : ℕ := x.1.toNat + 2 ^ 64 * x.2.1.toNat + 2 ^ 128 * x.2.2.toNat
  (List.range (192 / b)).map fun j => (v / 2 ^ (j * b)) % 2 ^ b

/-- A root as the two scalars it is sent as (`hash_to_scalars`). -/
def rootLimbs (r : Bytes32) : List Limbs := [(rootScalars r).1, (rootScalars r).2]

/-! ## An opening (`whir.rs`, `recursive_prover`) -/

/-- The shape of one opening, at the deployed parameters. -/
structure OpenShape where
  /-- The prefix the IV hashes: `"pcs-quotient-opening" ‖ LE64(2) ‖ layout_id ‖ LE64(log_n) ‖ LE64(1)`. -/
  ivPrefix : List UInt8
  /-- The secret table at level 0, or `none` (the public wiring table, its rows in `pubRows`). -/
  secret : Option Tbl
  pubRows : List (List UInt8)
  /-- Level 0's codeword length (`2^depth₀` leaves). -/
  depth₀ : ℕ
  /-- Out-of-domain coordinates of the first commitment. -/
  ood₀ : ℕ
  /-- Every later level: fold rounds, the commitment's depth and its out-of-domain coordinates. -/
  levels : List (ℕ × ℕ × ℕ)
  /-- The queries of every level, level 0 first (one more entry than `levels` + the last). -/
  queries : List ℕ
  /-- The last level's fold rounds and residual variables. -/
  lastFolds : ℕ
  residualVars : ℕ

/-- The prover's state through an opening: the duplex, the current message's items, the levels of
the commitments so far, the stream sent, the multiproofs. -/
structure OSt where
  dx : Dx
  items : Msg
  trees : List (List (List Bytes32))
  stream : List Limbs
  merkle : List (List ℕ × List (List UInt64) × List Bytes32)

/-- The next scalars of the message (`k` of them, default zeros). -/
def takeScalars (items : Msg) (k : ℕ) : List Limbs × Msg :=
  match items with
  | .scalars l :: rest => ((l ++ List.replicate k (0, 0, 0)).take k, rest)
  | rest => (List.replicate k (0, 0, 0), rest)

/-- The next rows. -/
def takeRows (items : Msg) : List (List UInt8) × Msg :=
  match items with
  | .rows l :: rest => (l, rest)
  | rest => ([], rest)

/-- The next opened rows. -/
def takeOpened (items : Msg) : List (List UInt64) × Msg :=
  match items with
  | .opened l :: rest => (l, rest)
  | rest => ([], rest)

/-- Send `k` scalars: from the message, into the stream, absorbed. -/
def sendK (o : OSt) (k : ℕ) : OracleComp DSpec OSt := do
  let (xs, items) := takeScalars o.items k
  let dx ← o.dx.absorbAll xs
  return { o with dx := dx, items := items, stream := o.stream ++ xs }

/-- Draw a challenge; the next message is read after it. -/
def drawO (o : OSt) : OracleComp DSpec (Limbs × OSt) := do
  let (c, dx) ← o.dx.draw
  let m ← getMsg
  return (c, { o with dx := dx, items := m })

/-- `k` rounds: draw, then send two scalars. -/
def rounds (o : OSt) : ℕ → OracleComp DSpec OSt
  | 0 => pure o
  | k + 1 => do
    let (_, o) ← drawO o
    let o ← sendK o 2
    rounds o k

/-- Draw `m` challenges and keep them. -/
def drawMany (o : OSt) : ℕ → OracleComp DSpec (List Limbs × OSt)
  | 0 => pure ([], o)
  | m + 1 => do
    let (c, o) ← drawO o
    let (cs, o) ← drawMany o m
    return (c :: cs, o)

/-- Commit to the next codeword (rows from the message): its tree, its root sent. -/
def commitNext (o : OSt) (depth : ℕ) : OracleComp DSpec OSt := do
  let (rows, items) := takeRows o.items
  let leaves ← rows.mapM hashH
  let lv ← levels depth leaves
  let o' : OSt := { o with items := items, trees := o.trees ++ [lv] }
  let dx ← o'.dx.absorbAll (rootLimbs (rootOf lv))
  return { o' with dx := dx, stream := o'.stream ++ rootLimbs (rootOf lv) }

/-- The out-of-domain sample: `m` coordinates drawn, the value and the intro message sent. -/
def ood (o : OSt) (m : ℕ) : OracleComp DSpec OSt := do
  let (_, o) ← drawMany o m
  sendK o 3

/-- The query phase of a level: grind, draw the positions, draw `λ`, the multiproof of the
commitment `lvl` (rows from the message), the intro message. -/
def queryPhase (o : OSt) (lvl q : ℕ) : OracleComp DSpec OSt := do
  let (nonce, dx) ← grind o.dx (2 ^ 64) 0
  let o := { o with dx := dx, stream := o.stream ++ [(nonce, 0, 0)] }
  let lv := o.trees.getD lvl []
  let b := lv.length - 1
  let per := 192 / max b 1
  let (cs, o) ← drawMany o ((q + per - 1) / per)
  let pos := ((cs.flatMap (positionsOf (max b 1))).take q)
  let (_, o) ← drawO o
  let (opened, items) := takeOpened o.items
  let o := { o with
    items := items
    merkle := o.merkle ++ [(sortedUnique pos, opened, prune lv (sortedUnique pos))] }
  sendK o 2

/-- Every later level but the last: fold rounds, commitment, OOD, query phase. -/
def middle (o : OSt) : ℕ → List (ℕ × ℕ × ℕ) → List ℕ → OracleComp DSpec OSt
  | _, [], _ => pure o
  | lvl, (folds, depth, oodN) :: rest, q :: qs => do
    let o ← rounds o folds
    let o ← commitNext o depth
    let o ← ood o oodN
    let o ← queryPhase o lvl q
    middle o (lvl + 1) rest qs
  | _, _ :: _, [] => pure o

/-- The level-0 tree of an opening: leaf operations for a secret table, hashes of public rows. -/
def tree₀ (sh : OpenShape) : OracleComp DSpec (List (List Bytes32)) := do
  let leaves ← match sh.secret with
    | some k => (List.range (2 ^ sh.depth₀)).mapM (leafH k)
    | none => sh.pubRows.mapM hashH
  levels sh.depth₀ leaves

/-- **One opening**, from its level-0 tree: the IV and seed, the root, `λ`, the lane rounds, the
first commitment and its OOD, level 0's query phase, the later levels, the last level. Returns the
stream and the multiproofs. -/
def opening (sh : OpenShape) (lv₀ : List (List Bytes32)) :
    OracleComp DSpec (List Limbs × List (List ℕ × List (List UInt64) × List Bytes32)) := do
  let m ← getMsg
  let (claims, m) := match m with
    | .bytes b :: rest => (b, rest)
    | rest => ([], rest)
  let iv ← hashH (sh.ivPrefix ++ claims)
  let dx ← seed iv
  let o : OSt := ⟨dx, m, [lv₀], [], []⟩
  -- the root, then the batching challenge `λ`
  let dx ← o.dx.absorbAll (rootLimbs (rootOf lv₀))
  let o := { o with dx := dx, stream := rootLimbs (rootOf lv₀) }
  let (_, o) ← drawO o
  -- the lane rounds: the first message, then six rounds
  let o ← sendK o 2
  let o ← rounds o 6
  -- the first commitment (after the lane fold) and its OOD sample
  let firstDepth := (sh.levels.headD (0, sh.depth₀ - 1, 0)).2.1
  let o ← commitNext o firstDepth
  let o ← ood o sh.ood₀
  let o ← queryPhase o 0 (sh.queries.headD 0)
  let o ← middle o 1 sh.levels (sh.queries.drop 1)
  -- the last level
  let o ← rounds o sh.lastFolds
  let o ← sendK o (2 ^ sh.residualVars)
  let o ← queryPhase o (sh.levels.length + 1) (sh.queries.getLastD 0)
  let o ← rounds o (sh.residualVars - 1)
  let (_, o) ← drawO o
  return (o.stream, o.merkle)

/-! ## The whole proof -/

/-- **The proof**: the calldata (the witness root, the quotient root, the five values) and the three
openings (stream and multiproofs). -/
structure Proof where
  wRoot : Bytes32
  qRoot : Bytes32
  values : List Limbs
  openings : List (List Limbs × List (List ℕ × List (List UInt64) × List Bytes32))

/-- The public parameters of the skeleton: the statement, the three openings' shapes (witness,
wiring, quotient), and the two secret tables' level-0 depths. -/
structure Shape where
  st : Statement
  witness : OpenShape
  wiring : OpenShape
  quotient : OpenShape

/-- **The deployed prover's skeleton.** The reduction: the witness table's tree (leaf operations),
the seed, `α, β, γ`, the quotient table's tree, `t`, the five values (from the message), `ρ`; then
the three openings. -/
def skel (sh : Shape) : OracleComp DSpec Proof := do
  let lvW ← tree₀ sh.witness
  let st₀ ← hashH (kcTag ++ sh.st.indexRoot.toList ++ sh.st.stmt.toList)
  let st₁ ← chalH (st₀.toList ++ rootWords (rootOf lvW))
  let st₂ ← chalH st₁.toList
  let st₃ ← chalH st₂.toList
  let lvQ ← tree₀ sh.quotient
  let st₄ ← chalH (st₃.toList ++ rootWords (rootOf lvQ))
  let m ← getMsg
  let (vals, _) := takeScalars m 5
  let _ ← chalH (st₄.toList ++ vals.flatMap scalarWord)
  let lvσ ← tree₀ sh.wiring
  let oW ← opening sh.witness lvW
  let oσ ← opening sh.wiring lvσ
  let oQ ← opening sh.quotient lvQ
  return ⟨rootOf lvW, rootOf lvQ, vals, [oW, oσ, oQ]⟩

end QuotientZk.Deployed
