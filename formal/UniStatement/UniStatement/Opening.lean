-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `PCS_OPEN`'s ABI is `crates/evm/src/machine.rs`'s
-- (as `crates/leanvm_flock_gas/src/evm/machine.rs` mocks it), its layout words and the contract's IV
-- `crates/leanvm_univariate/src/contract.rs`'s (`layout_word`, `layout_words`, `shape_bytes`, `contract_iv`,
-- `SetupRoots`); its semantics is this repository's `formal/Statement` opening (`PcsQuotient.openingWith`:
-- leanerVM `mumbai` 6175f1a0's WHIR verifier, MIT OR Apache-2.0).
module

public import UniStatement.Run
public import PcsQuotient.Opening

/-!
# `PCS_OPEN`, the contract's IV, and the whole verifier (the main line)

**`PCS_OPEN`** (`machine.rs`'s ABI: a root, a layout word, `k` point claims, each `v` coordinates and a
value): "the block's openings hold exactly these claims on that commitment under that layout". As in
`formal/Statement` (`formal/EndToEnd/Evm`'s `pcsOpen`), its meaning here is **the Statement's opening**,
`PcsQuotient.openingWith` (leanVM's WHIR verifier, mumbai's `verifyStackedOpening`, seeded as
`opening.rs` seeds it), on the call's opening proof, for the **plain layout** of a stack of `2^vars`
words (`plainLayout`: lane `l` holds block `l`, so a claim's weight on the stack is `eq(point, ·)`: a point
claim on the stack's multilinear extension), `vars` read from the call's **layout word** (iteration 2, F2:
`layoutWord`, byte 24). The Rust has only a mock (`PcsOpen::attesting_all`): which WHIR instance the
precompile runs is not specified there; this is the choice the statements are made under.

**The layout words** (iteration 2, F2; `contract::layout_word`): 32 bytes, the shape's 8 (`shapeBytes`: `log_memory`,
`log_bytecode`, the six heights), the opening's code (bytes 22..24: `0x5501` `C1`, `0x5502` `C2`, `0x5503` the
setup, `0x5504` `A0`, `0x5505` `B0`), the stack's `vars` (byte 24) and `placed` (bytes 25..32, the words its
blocks fill, `StackLayout.words`; `2^28` for `A0`, `B0`). **The contract's IV** (`contract_iv`,
`contractIvWith`): the Keccak-256 of the tag `"leanVM-univar-iv"`, the program's IV, the three setup roots, the
shape's bytes and the five layout words. The seed is then `keccak(name ‖ IV ‖ public input)` (`runWith`).

**The whole verifier** (`verifyWith`, the main line: Flock (a′) in tower order, `PCS_OPEN`'s point-claim ABI):
the run on the stream (`runWith`; the row counts its first 24 bytes, range-checked by the run), its verdict, then
**five calls**, in the contract's order: `C1`, `C2`, the setup (each its one point claim, on its root: `C1`'s
and `C2`'s the stream's, the setup's a constant), then Flock's `A0` and `B0` (one point claim each, `2^28`
words). The extensions (weighted claims, the bit-slice claim type) are precompile changes with no opening
defined here; `verifyWith` rejects them.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **The plain layout** of a stack of `2^vars` words: one chunk, lane `l` its block `l`
(`PcsQuotient.Layout.ofChunks`); a claim's weight is `eq(point, ·)` on the stack. -/
def plainLayout (vars : ℕ) : PcsQuotient.Layout := PcsQuotient.Layout.ofChunks vars vars vars [(0, 2 ^ vars)]

/-- A commitment's root from the two halves the stream carries it as (`next_root`; never malformed: a
half has no top limb). -/
def rootOf (halves : E × E) : Digest := (digestOfScalars halves).getD (Vector.replicate 4 0)

/-- **The setup's roots**, constants of the verifier: the bytecode's tuples and the memory's addresses
(`F`), and Flock's matrices `A0`, `B0`. -/
structure SetupRoots where
  bytecode : Digest
  a0 : Digest
  b0 : Digest

/-- The digest whose bytes (`digestBytes`, its words little-endian) are the 32 bytes `b`. -/
def digestOfBytes32 (b : List UInt8) : Digest :=
  Vector.ofFn fun j : Fin 4 ↦
    (List.range 8).foldl (fun acc k ↦ acc ||| ((b.getD (8 * j.val + k) 0).toUInt64 <<< (8 * k).toUInt64)) 0

/-- The bytes of a lowercase hex string (a constant's spelling). -/
def bytesOfHex (s : String) : List UInt8 :=
  let digit (c : Char) : ℕ := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i ↦ (16 * digit (cs.getD (2 * i) '0') + digit (cs.getD (2 * i + 1) '0')).toUInt8

/-- **`SetupRoots::REFERENCE`** (iteration 2, F2): the reference shape's real setup roots (memory `2^21`, bytecode
`2^19`; `prover::setup::roots`, PROVER.md), as the contract's code holds them, each 32-byte word read as the
digest of those bytes. The gas reports and the differential test use them for every shape. -/
def referenceRoots : SetupRoots :=
  ⟨digestOfBytes32 (bytesOfHex "9b5a0f9bd796c09b8bc328113956464acf865c99b7dfc088c0c0a3208eab5fb7"),
    digestOfBytes32 (bytesOfHex "93cd9a0352a85dcc663f7068e1f3afa3a00f5220bd2b03d67244f0eb133fd2f7"),
    digestOfBytes32 (bytesOfHex "c07556508c416240dafd47665831fd51d2eb1104a52c63231101479c7f6cd467")⟩

/-- **`shape_bytes(shape)`** (iteration 2, F2): `log_memory`, `log_bytecode`, then the six heights, a byte each. -/
def shapeBytes (s : Shape) : List UInt8 :=
  [s.logMemory.toUInt8, s.logBytecode.toUInt8] ++ (List.range 6).map fun k ↦ (s.heights.getD k 0).toUInt8

/-- `layout_code(commitment)`: the opening's code in its layout word. -/
def layoutCode : Commitment → ℕ
  | .c1 => 0x5501
  | .c2 => 0x5502
  | .setup => 0x5503

/-- `A0_CODE`, `B0_CODE`. -/
def a0Code : ℕ := 0x5504
def b0Code : ℕ := 0x5505

/-- **`layout_word(shape, code, vars, placed)`**: the shape's bytes (bytes `0..8`), zeros, the opening's code
(bytes `22..24`, big-endian), the stack's variables (byte `24`) and the words its blocks fill (bytes `25..32`,
big-endian). -/
def layoutWord (s : Shape) (code vars placed : ℕ) : List UInt8 :=
  shapeBytes s ++ List.replicate 14 (0 : UInt8) ++ [(code >>> 8).toUInt8, code.toUInt8, vars.toUInt8] ++
    (List.range 7).map fun k ↦ (placed >>> (8 * (6 - k))).toUInt8

/-- `A0`'s and `B0`'s stacks: `2^28` words, the R1CS of `2^14` positions. -/
def matrixVars : ℕ := 2 * blake2sR1csLogSize

/-- **`layout_words(shape)`**: the five openings' layout words, in call order: `C1`, `C2`, the setup (each its
stack's `vars` and `placed`, `layoutsOf`), `A0`, `B0` (`28` variables, `2^28` words). -/
def layoutWords (s : Shape) : List (List UInt8) :=
  let stackLayouts := layoutsOf s
  let wordOf (c : Commitment) : List UInt8 :=
    let l := (stackLayouts.lookup c).getD default
    layoutWord s (layoutCode c) l.vars l.words
  [wordOf .c1, wordOf .c2, wordOf .setup, layoutWord s a0Code matrixVars (2 ^ matrixVars),
    layoutWord s b0Code matrixVars (2 ^ matrixVars)]

/-- The stack's variables a layout word names (byte `24`): what the opening reads it for. -/
def layoutWordVars (word : List UInt8) : ℕ := (word.getD 24 0).toNat

/-! ### `PCS_OPEN`'s inputs, word for word (`contract::calls`, `opening_words`, `combined_words`) -/

/-- The eight big-endian bytes of a 64-bit word. -/
def be64 (w : UInt64) : List UInt8 := (List.range 8).map fun k ↦ (w >>> (8 * (7 - k)).toUInt64).toUInt8

/-- `number(n)`: a 32-byte word, `n` big-endian in its last eight bytes. -/
def numberWord (n : ℕ) : List UInt8 := List.replicate 24 0 ++ be64 n.toUInt64

/-- `element_word(x)`: `x`'s limbs `c2, c1, c0` big-endian in the low 24 bytes of a 32-byte word. -/
def elementWord (x : E) : List UInt8 :=
  List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane ++ be64 (x.limb 0).lane

/-- A commitment's root word, as the stream carries it (`next_root`'s two halves, each big-endian limbs `1, 0`). -/
def rootWord (halves : E × E) : List UInt8 :=
  be64 (halves.1.limb 1).lane ++ be64 (halves.1.limb 0).lane ++ be64 (halves.2.limb 1).lane ++
    be64 (halves.2.limb 0).lane

/-- `combined_words(claim)`: its points (a count, then each its length and coordinates), its terms (a count, then
each `column | point << 32 | twist << 48` and its coefficient), its value. -/
def combinedWords (claim : Combined) : List UInt8 :=
  numberWord claim.points.length ++ claim.points.flatMap (fun p ↦ numberWord p.length ++ p.flatMap elementWord) ++
    numberWord claim.terms.length ++
    claim.terms.flatMap (fun (c, p, twist, k) ↦ numberWord (c.id ||| p <<< 32 ||| twist <<< 48) ++ elementWord k) ++
    elementWord claim.value

/-- `opening_words(root, layout, opening)`: a call's header (the root, the layout word, the number of claims),
then its claims: a weighted claim; or a point claim (its coordinates, its value), and the bit-slice claim. -/
def openingWords (root layout : List UInt8) : Opening → List UInt8
  | .weighted claim => root ++ layout ++ numberWord 1 ++ combinedWords claim
  | .point pt v bitSlice => root ++ layout ++ numberWord (if bitSlice.isSome then 2 else 1) ++
      pt.flatMap elementWord ++ elementWord v ++ (bitSlice.map combinedWords).getD []

/-- **`calls`**: the contract's `PCS_OPEN` inputs, in call order: one per commitment (`C1`'s and `C2`'s roots the
stream's, the setup's a constant), then `A0`'s and `B0`'s (one point claim each), each with its layout word. -/
def pcsCalls (shape : Shape) (roots : SetupRoots) (r : Reduced) : List (List UInt8) :=
  let words := layoutWords shape
  let header : Commitment → List UInt8 × List UInt8
    | .c1 => (rootWord r.roots.1, words.getD 0 [])
    | .c2 => (rootWord r.roots.2, words.getD 1 [])
    | .setup => (digestBytes roots.bytecode, words.getD 2 [])
  let matrices : List (List UInt8) := match r.matrices with
    | some mc =>
      [digestBytes roots.a0 ++ words.getD 3 [] ++ numberWord 1 ++ mc.point.flatMap elementWord ++ elementWord mc.a,
        digestBytes roots.b0 ++ words.getD 4 [] ++ numberWord 1 ++ mc.point.flatMap elementWord ++ elementWord mc.b]
    | none => []
  r.openings.map (fun (c, o) ↦ openingWords (header c).1 (header c).2 o) ++ matrices

/-- The contract IV's tag. -/
def ivTag : List UInt8 := "leanVM-univar-iv".toUTF8.toList

/-- **A proof**: the stream (calldata after the selector and the public input: the row counts, then the rest),
and the opening proof the block holds for each of the five `PCS_OPEN` calls (mumbai's format,
`Compile.Proof`). -/
structure UniProof where
  stream : Array UInt8
  c1 : Compile.Proof
  c2 : Compile.Proof
  setup : Compile.Proof
  a0 : Compile.Proof
  b0 : Compile.Proof

/-- **A proof's row counts** (iteration 2, F1): the six its stream announces (`rowsOf`). -/
def UniProof.rows (p : UniProof) : List ℕ := rowsOf p.stream

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`contract_iv(shape, program_iv, roots)`** over `F` (iteration 2, F2): the Keccak-256 of the tag, the
program's IV, the setup's three roots (`digestBytes`), the shape's bytes and the five layout words. -/
def contractIvWith (s : Shape) (programIv : List UInt8) (roots : SetupRoots) : m (List UInt8) := do
  let d ← keccak256With F (ivTag ++ programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes s ++ (layoutWords s).flatten)
  return digestBytes d

end With

/-- The contract's IV over Keccak-f[1600]: the deployed contract's constant (`contract::contract_iv`). -/
def contractIv (s : Shape) (programIv : List UInt8) (roots : SetupRoots) : List UInt8 :=
  Id.run (contractIvWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s programIv roots)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`PCS_OPEN`** over `F`: the claims on the stack of `2^vars` words committed as `root`, against the
call's opening proof. -/
def pcsOpenWith (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    m Bool :=
  PcsQuotient.openingWith F (plainLayout vars) root claims proof

/-- **The verifier** over `F` (the main line): the run on the stream (its row counts read and range-checked
there), its verdict, the five `PCS_OPEN` calls with their layout words. -/
def verifyWith (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) : m Bool := do
  let o ← runWith F shape iv publicInput.toList proof.stream (.flock flockMain) .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := layoutWords shape
    let callOf : Commitment → Digest × List UInt8 × Compile.Proof
      | .c1 => (rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    -- C1, C2, the setup: one point claim each.
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← pcsOpenWith F (layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    -- Flock's matrices.
    match r.matrices with
    | some mc =>
      ok := ok && (← pcsOpenWith F (layoutWordVars (words.getD 3 [])) roots.a0 [⟨mc.point, mc.a⟩] proof.a0)
      ok := ok && (← pcsOpenWith F (layoutWordVars (words.getD 4 [])) roots.b0 [⟨mc.point, mc.b⟩] proof.b0)
    | none => ok := false
    return ok

end With

end UniStatement

end
