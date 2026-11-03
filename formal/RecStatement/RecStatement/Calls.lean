-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/pi2/contract.rs`
-- (`read_indices`, `number`, `root_word`, `call_words`, `expected_calls`) and `crates/leanvm_univariate/src/contract.rs`
-- (`variant_bytes`, `contract_iv_for`), branch `leanvm-rec` @ 2b22581. `PCS_OPEN`'s ABI is
-- `crates/evm/src/machine.rs`'s (`crates/leanvm_flock_gas/src/evm/machine.rs`: `element_word`, `root_word`).
import RecStatement.Verifier

/-!
# The six `PCS_OPEN` calls, word for word

The contract calls `PCS_OPEN` six times, each with `machine.rs`'s ABI (`root word, layout word, k, k × (point,
value)`, 32-byte words), in this order (`contract::call_words`):

1. **π1's three** (`C1`, `C2`, π1's setup `F`), their words as the circuit names them (`CallWord`): constants (π1's
   layout words, the claim counts, `F`'s root word), π1's roots `C1`, `C2` (the stream's 32 bytes at their reads),
   π1's claims' elements (public scalars, `element_word`), and the coordinates `y_0(z_j), y_1(z_j)` of π1-rec3's pair
   challenges `z_j` (`pair_point`), which the contract derives;
2. **`W`'s** (one claim; its root the stream's 32 bytes), **the setup's** (one claim; its root a constant,
   `root_word` of the setup's root: each 16-byte half reversed), **`Q`'s** (two claims in one call: one opening).

**π1's contract IV** (`contract_iv_for`, REVIEW-REC.md N2): the main line's IV preimage (`UniStatement.contractIvWith`'s:
the tag, the program IV, π1's three setup roots, the shape's bytes, the five layout words) with the variant's bytes
appended, for π1-rec3 `"fs-rec3"`, the skip `3` and the slices' code `4` (`Slices::TowerWalk`).
-/

namespace RecStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- The stream offsets of the roots: π1's (at each `Read.root`), then `W`'s and `Q`'s, after the public data. -/
def rootsAt (reads : List Read) : List ℕ :=
  let (roots, next) := reads.foldl (fun (acc : List ℕ × ℕ) rd ↦
    (if rd = .root then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.bytes)) ([], 0)
  roots ++ [next, next + 32]

/-- **`read_indices`**: the public scalars' indices of π1's claims' elements (each `Read.scalar`), after the public
input's four words. -/
def elementIndices (reads : List Read) : List ℕ :=
  (reads.foldl (fun (acc : List ℕ × ℕ) rd ↦
    (if rd = .scalar then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.scalars)) ([], 4)).1

/-- The number of π1's roots the stream carries. -/
def rootReads (reads : List Read) : ℕ := (reads.filter (· = .root)).length

/-- The stream's 32 bytes from `at`. -/
def streamWord (stream : Array UInt8) (at' : ℕ) : List UInt8 := (stream.extract at' (at' + 32)).toList

/-- **`root_word(root)`**: `PCS_OPEN`'s root word of a root's 32 bytes, each 16-byte half reversed (an involution). -/
def rootWordOfBytes (h : List UInt8) : List UInt8 := (h.take 16).reverse ++ ((h.drop 16).take 16).reverse

/-- A claim's words: its coordinates, then its value. -/
def claimWords (c : List E × E) : List (List UInt8) := (c.1 ++ [c.2]).map UniStatement.elementWord

/-- **A word of π1's calls** from the stream and the reduction. -/
def callWord (reads : List Read) (stream : Array UInt8) (r : Reduced) : CallWord → List UInt8
  | .const w => w
  | .root i => streamWord stream ((rootsAt reads).getD i 0)
  | .element i => UniStatement.elementWord (r.scalars.getD ((elementIndices reads).getD i 0) 0)
  | .pair e c =>
    let pp := r.pairPoints.getD ((elementIndices reads).getD e 0) (0, 0)
    UniStatement.elementWord (if c = 0 then pp.1 else pp.2)

/-- **`expected_calls`**: the six calls' words, in order: π1's, then `W`'s, the setup's, `Q`'s. -/
def pcsCalls (c : Circuit) (pi1 : List (List CallWord)) (setupRoot : List UInt8) (stream : Array UInt8)
    (r : Reduced) : List (List (List UInt8)) :=
  let at' := rootsAt c.reads
  let n := rootReads c.reads
  let (lw, lq, ls) := layoutWords c.logN
  let head (root lid : List UInt8) (k : ℕ) : List (List UInt8) := [root, lid, UniStatement.numberWord k]
  pi1.map (·.map (callWord c.reads stream r)) ++
    [head (streamWord stream (at'.getD n 0)) lw 1 ++ claimWords r.witness,
     head (rootWordOfBytes setupRoot) ls 1 ++ claimWords r.setup,
     head (streamWord stream (at'.getD (n + 1) 0)) lq 2 ++ claimWords r.quotient ++ claimWords r.sum]

/-- The stream's length: the public data, `W`'s and `Q`'s roots, the `2^r + 1` values. -/
def streamLen (c : Circuit) : ℕ := (c.reads.map (·.bytes)).sum + 64 + 24 * (2 ^ c.logRow + 1)

/-! ## π1's contract IV -/

/-- **`variant_bytes(Flock(FLOCK_REC3))`**: `"fs-rec3"`, the skip (`3`), the slices' code (`4`, `TowerWalk`)
(`UniStatement.variantBytes`). -/
def rec3VariantBytes : List UInt8 := UniStatement.variantBytes (.flock UniStatement.flockMain) .rec3 true

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`contract_iv_for(shape, Flock(FLOCK_REC3), program_iv, roots)`** over `F`: π1-rec3's contract IV
(`UniStatement.contractIvForWith` at π1-rec3's Fiat–Shamir shape and walked terminal). -/
def pi1IvWith (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniStatement.SetupRoots) :
    m (List UInt8) :=
  UniStatement.contractIvForWith F s (.flock UniStatement.flockMain) .rec3 true programIv roots

end With

/-- π1-rec3's contract IV over Keccak-f[1600]. -/
def pi1Iv (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniStatement.SetupRoots) : List UInt8 :=
  Id.run (pi1IvWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s programIv roots)

end RecStatement
