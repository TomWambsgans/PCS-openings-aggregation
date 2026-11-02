-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- ChaCha is D. J. Bernstein's (https://cr.yp.to/chacha.html); the stream is `rand_chacha`'s `ChaCha12Rng`
-- (`rand`'s `StdRng`, the one `crates/quotient/src/opening.rs` pads with), not formalized, for the test only.
import PcsQuotient

/-!
# The Rust prover's padding

The deployed prover draws a hidden table's padding from a 32-byte seed (`Table::hidden`, `opening.rs`): the
table's seed is Keccak-256 of `"pcs-quotient-pad-" ‖ table ‖ seed` (`table_seed`, `protocol.rs`), lane `l`'s
generator is `StdRng` (ChaCha12, a 64-bit block counter from `0`, stream `0`) keyed by Keccak-256 of the table's
seed and `l` as eight little-endian bytes, and its words are the generator's 64-bit outputs, two 32-bit words of
the keystream each, low first. The statement's prover takes the padding uniform (`Security.lean`); this module
gives the test the Rust's, so that the Lean prover can be compared with the Rust's on the same seed.
-/

namespace PcsQuotientTest.ChaCha

/-- `x` rotated left by `n`. -/
def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- The quarter round on words `a, b, c, d` of the state. -/
def quarter (s : Array UInt32) (a b c d : ℕ) : Array UInt32 :=
  let va := s[a]! + s[b]!
  let vd := rotl (s[d]! ^^^ va) 16
  let vc := s[c]! + vd
  let vb := rotl (s[b]! ^^^ vc) 12
  let va := va + vb
  let vd := rotl (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotl (vb ^^^ vc) 7
  ((s.set! a va).set! b vb |>.set! c vc).set! d vd

/-- One ChaCha12 block: the key's eight words, the 64-bit counter, stream `0`; six double rounds, then the
input added back. -/
def block (key : Array UInt32) (counter : UInt64) : Array UInt32 :=
  let init : Array UInt32 := (#[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] : Array UInt32) ++ key ++
    #[counter.toUInt32, (counter >>> 32).toUInt32, 0, 0]
  let s := (List.range 6).foldl (fun s _ ↦
    let s := quarter s 0 4 8 12
    let s := quarter s 1 5 9 13
    let s := quarter s 2 6 10 14
    let s := quarter s 3 7 11 15
    let s := quarter s 0 5 10 15
    let s := quarter s 1 6 11 12
    let s := quarter s 2 7 8 13
    quarter s 3 4 9 14) init
  Array.zipWith (· + ·) s init

/-- The first `count` 64-bit outputs of `StdRng::from_seed(seed)`. -/
def stdRngWords (seed : List UInt8) (count : ℕ) : Array UInt64 :=
  let key : Array UInt32 := Array.ofFn (n := 8) fun i ↦
    (List.range 4).foldl (fun acc k ↦ acc ||| ((seed.getD (4 * i.val + k) 0).toUInt32 <<< (8 * k).toUInt32)) 0
  let blocks := (2 * count + 15) / 16
  let words : Array UInt32 := (List.range blocks).foldl (fun acc b ↦ acc ++ block key b.toUInt64) #[]
  Array.ofFn (n := count) fun i ↦
    (words.getD (2 * i.val) 0).toUInt64 ||| ((words.getD (2 * i.val + 1) 0).toUInt64 <<< 32)

open LeanVM.Parameters LeanVM.Protocol PcsQuotient

/-- The deployed Keccak-256 of bytes, as bytes. -/
def keccakBytes (data : List UInt8) : List UInt8 := (KeccakHash.keccak256 data).toBytes.toList

/-- **The Rust prover's padding words** of table `table` (`"witness"` or `"quotient"`) of layout `L`, from the
proof's seed: each lane's `2^ℓ` first words. -/
def paddingLanes (seed : List UInt8) (table : String) (L : Layout) : Array (Array UInt64) :=
  let tableSeed := keccakBytes ("pcs-quotient-pad-".toUTF8.toList ++ table.toUTF8.toList ++ seed)
  Array.ofFn (n := L.lanes.length) fun l ↦
    let laneBytes := (List.range 8).map fun k ↦ (l.val.toUInt64 >>> (8 * k).toUInt64).toUInt8
    stdRngWords (keccakBytes (tableSeed ++ laneBytes)) (2 ^ L.logLane)

/-- The padding the words are. The words are an argument, computed once by the caller: a definition
`let words := …; fun l i ↦ …` is compiled at its full arity, which would expand the seed again at every
word. -/
def padOf (lanes : Array (Array UInt64)) : Padding :=
  fun l i ↦ K.ofLane ((lanes.getD l #[]).getD i 0)

end PcsQuotientTest.ChaCha
