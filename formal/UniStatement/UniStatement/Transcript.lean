-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/leanvm_flock_gas/src/transcript.rs` (`KeccakChannel`, `keccak_seed`, `challenge_of`,
-- `sumcheck`, `sumcheck_round_poly`; the last two adapted there from leanVM (https://github.com/leanEthereum/leanVM),
-- commit 42422001, `crates/verifier/src/transcript.rs`). Keccak-256 over a permutation is leanerVM's
-- (`Statement/Keccak.lean`, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0); `challengeOf` is this
-- repository's `formal/Statement` (`PcsQuotient.Transcript`).
module

public import UniStatement.Basic
public import PcsQuotient.Transcript

/-!
# The transcript: the contract's Keccak-256 chain over calldata

`KeccakChannel` (`transcript.rs`), over a permutation `F` of the Keccak state in any monad (`F` is the
random permutation `π` in the model, Keccak-f[1600] deployed):

* the proof is the **stream**, calldata bytes after the selector and the public input;
* a **scalar** is 24 bytes, big-endian, limbs `2, 1, 0` (`next_scalar`); a commitment's **root** is two
  16-byte halves, each big-endian limbs `1, 0` (`next_root`), so a root has one encoding (no top limb);
* a **challenge** is one Keccak-256 of the state and of the stream bytes read since the last challenge,
  exactly as they are in calldata (`sample`); the digest is the new state, its low 192 bits the
  challenge (`challengeOf`, read big-endian, limb `i` the bytes `24 − 8i … 31 − 8i`);
* the **seed** is the Keccak-256 of the 16-byte name, the program's 32-byte IV and the 32-byte public input
  (`keccak_seed`);
* the identities the verifier requires are **collected**, not enforced (`Checks::Collect`): the verdict is
  that every collected value is zero, and nothing of the stream is left unread (`finish`).

The channel's state also keeps every challenge drawn (`challenges`): the differential test compares them;
nothing in the verifier reads them back.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- The errors the stream can end the run with (`VerifierError`'s `StreamExhausted`,
`StreamNotConsumed`); every other check of the verifier is collected (`Chan.zeros`). -/
inductive UniError where
  | streamExhausted
  | streamNotConsumed
  deriving DecidableEq, Repr, Inhabited

/-- `UniError` as the Rust prints it (`Debug`). -/
def UniError.name : UniError → String
  | .streamExhausted => "StreamExhausted"
  | .streamNotConsumed => "StreamNotConsumed"

/-- **The channel** (`KeccakChannel`): the stream, the cursor, how much of it the state has absorbed, the
state, and what the verifier stated: every challenge drawn, every value it requires to be zero. -/
structure Chan where
  data : Array UInt8
  cursor : ℕ
  absorbed : ℕ
  state : Digest
  challenges : Array E
  zeros : Array E

/-- The channel's monad over `m`: the state survives an error (the test reads the challenges drawn
before it). -/
abbrev ChanM (m : Type → Type) := ExceptT UniError (StateT Chan m)

/-- The big-endian 64-bit word of bytes `start … start + 7`. -/
def beWordAt (a : Array UInt8) (start : ℕ) : UInt64 :=
  (List.range 8).foldl (fun acc k ↦ (acc <<< 8) ||| (a.getD (start + k) 0).toUInt64) 0

/-- `NAME` (`contract.rs`): the transcript's 16-byte name. -/
def name : List UInt8 := "leanVM-univar-v1".toUTF8.toList

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- `keccak_seed(name, iv, public_input)` over `F`. -/
def seedWith (iv publicInput : List UInt8) : m Digest := keccak256With F (name ++ iv ++ publicInput)

/-- `KeccakChannel::new`: the stream, read from its start, the state the seed. -/
def Chan.start (seed : Digest) (stream : Array UInt8) : Chan := ⟨stream, 0, 0, seed, #[], #[]⟩

/-- `take::<N>`: the next `n` bytes, or `StreamExhausted` (the cursor stays). -/
def takeBytes (n : ℕ) : ChanM m (Array UInt8) := do
  let c ← get
  if c.cursor + n ≤ c.data.size then
    set { c with cursor := c.cursor + n }
    return c.data.extract c.cursor (c.cursor + n)
  else throw .streamExhausted

/-- `next_scalar`: 24 bytes, big-endian, limbs `2, 1, 0`. -/
def nextScalar : ChanM m E := do
  let b ← takeBytes (m := m) 24
  return eNew (beWordAt b 16) (beWordAt b 8) (beWordAt b 0)

/-- `next_scalars(count)`. -/
def nextScalars (count : ℕ) : ChanM m (List E) := do
  let mut out : Array E := #[]
  for _ in [0:count] do
    out := out.push (← nextScalar (m := m))
  return out.toList

/-- `next_root`: two halves of 16 bytes, each big-endian limbs `1, 0`, low half first. -/
def nextRoot : ChanM m (E × E) := do
  let lo ← takeBytes (m := m) 16
  let hi ← takeBytes (m := m) 16
  return (eNew (beWordAt lo 8) (beWordAt lo 0) 0, eNew (beWordAt hi 8) (beWordAt hi 0) 0)

/-- **`sample`**: the Keccak-256 over `F` of the state's 32 bytes and the bytes read since the last
challenge is the new state; its low 192 bits are the challenge. -/
def sample : ChanM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList
  let state ← (keccak256With F input : m Digest)
  let x := PcsQuotient.Transcript.challengeOf state
  set { c with absorbed := c.cursor, state := state, challenges := c.challenges.push x }
  return x

/-- `samples(count)`. -/
def samples (count : ℕ) : ChanM m (List E) := do
  let mut out : Array E := #[]
  for _ in [0:count] do
    out := out.push (← sample F)
  return out.toList

/-- `require_zero(value, _)` (`Checks::Collect`): the value is recorded; the verdict requires it zero. -/
def requireZero (value : E) : ChanM m Unit :=
  modify fun c ↦ { c with zeros := c.zeros.push value }

/-- `finish`: nothing of the stream is left unread. -/
def finish : ChanM m Unit := do
  let c ← get
  if c.cursor = c.data.size then return () else throw .streamNotConsumed

/-! ### Sumcheck (`transcript.rs`, leanVM's) -/

/-- `sumcheck_round_poly(count, claim, eq_factor)`: a round's message, `count` coefficients. Without
`eq_factor` the stream holds `c0, c2, …` and `q(0) + q(1) = claim` gives `c1`; with it the stream holds
`c1, c2, …` and `(1 + r) q(0) + r q(1) = claim` gives `c0`. -/
def roundPoly (count : ℕ) (claim : E) (eqFactor : Option E) : ChanM m (List E) := do
  match eqFactor with
  | none =>
    let constant ← nextScalar (m := m)
    let tail ← nextScalars (m := m) (count - 2)
    return [constant, claim + esum tail] ++ tail
  | some r =>
    let tail ← nextScalars (m := m) (count - 1)
    return [claim + r * esum tail] ++ tail

/-- **`sumcheck(claim, count, equalities)`**: one round per entry, each its message then a challenge; the
point and the final claim. -/
def sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) : ChanM m (List E × E) := do
  let mut point : Array E := #[]
  let mut claim := claim
  for equality in equalities do
    let message ← roundPoly (m := m) count claim equality
    let challenge ← sample F
    point := point.push challenge
    claim := polyEval message challenge
  return (point.toList, claim)

end With

end UniStatement

end
