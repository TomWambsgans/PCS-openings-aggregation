-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/transcript.rs` (adapted from leanVM, branch
-- PCS-openings-aggregation, commit 651453c6, `FiatShamirState::keccak`). Keccak-256 over a
-- permutation is leanerVM's (`Statement/Keccak.lean`, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0).
module

public import Statement.Field

/-!
# The reduction's transcript: a Keccak-256 chain

The reduction's Fiat–Shamir transcript (`transcript.rs`), over a permutation `F` of the Keccak state
in any monad, Keccak-256 the sponge over `F` (`keccak256With F`): in the model `F` is the random
permutation `π`, deployed it is Keccak-f[1600] (and the EVM's `KECCAK256`).

The state is a 256-bit word, a Keccak-256 digest. A challenge is one Keccak-256 of the state and of
every scalar sent since the last challenge, each as a 256-bit big-endian word (limb `0` lowest, eight
zero bytes on top); the digest is the new state, and its low 192 bits, read big-endian, the
challenge. The seed is the Keccak-256 of a label (`Reduction.lean`'s `label`, which holds the
circuit's commitment and the statement). The protocol fixes how many scalars precede each
challenge, so no length or tag is hashed.
-/

@[expose] public section

namespace PcsQuotient.Transcript

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- The eight big-endian bytes of a 64-bit word. -/
def beBytes (w : UInt64) : List UInt8 := (wordBytes w).reverse

/-- **A scalar as the chain hashes it** (`Chain::sample`, `transcript.rs:69-73`): a 256-bit
big-endian word, eight zero bytes, then limbs `2`, `1`, `0`, each big-endian. -/
def scalarBytes (x : E) : List UInt8 :=
  List.replicate 8 0 ++ beBytes (x.limb 2).lane ++ beBytes (x.limb 1).lane ++ beBytes (x.limb 0).lane

/-- The big-endian 64-bit word of bytes `start … start + 7`. -/
def beWord (bytes : List UInt8) (start : ℕ) : UInt64 :=
  (List.range 8).foldl (fun acc k ↦ (acc <<< 8) ||| (bytes.getD (start + k) 0).toUInt64) 0

/-- **The challenge of a state** (`transcript.rs:74-75`): its low 192 bits, the digest's bytes
read as a big-endian number, limb `i` the bytes `24 − 8i … 31 − 8i`. -/
def challengeOf (state : Digest) : E :=
  let b := digestBytes state
  E.ofLimbs (K.ofLane (beWord b 24)) (K.ofLane (beWord b 16)) (K.ofLane (beWord b 8))

/-- **The chain** (`Chain`, `transcript.rs:51-56`): the state, and the scalars sent since the last
challenge. -/
structure Chain where
  state : Digest
  pending : List E

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- The chain seeded by `label`: its Keccak-256 (`Chain::new`, `transcript.rs:58-63`). -/
def Chain.startWith (label : List UInt8) : m Chain := do
  return ⟨← keccak256With F label, []⟩

/-- **A challenge** (`Chain::sample`, `transcript.rs:65-76`): the Keccak-256 of the state's bytes
and the pending scalars' words is the new state, its low 192 bits the challenge. -/
def Chain.squeezeWith (c : Chain) : m (E × Chain) := do
  let state ← keccak256With F (digestBytes c.state ++ c.pending.flatMap scalarBytes)
  return (challengeOf state, ⟨state, []⟩)

end With

/-- Send (or read) a scalar: it waits for the next challenge (`ProverChain::send`,
`VerifierChain::next`). -/
def Chain.absorb (c : Chain) (x : E) : Chain := { c with pending := c.pending ++ [x] }

end PcsQuotient.Transcript

end
