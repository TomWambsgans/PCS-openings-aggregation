-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/protocol.rs` (`verify`, `verify_openings`, `Openings`). The
-- opening proofs are leanerVM's format (`Statement/LeanVmVerifier.lean`, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0).
module

public import PcsQuotient.Opening

/-!
# The verifier

**The proof** (`Proof`): the reduction's proof (two commitments and five elements of `E`,
`Reduction.lean`) and three WHIR opening proofs, one per commitment, the quotient table's two claims
together (`Openings`, `protocol.rs:631-635`), each in mumbai's format (`Opening.lean`).

**The verifier** (`verifyWith`), over a permutation `F` in any monad, Keccak-256 the sponge over
`F`: the reduction down to the two roots and the four claims, then each opening against its root:
the witness claim against the witness table's root, the wiring claim against the circuit's
commitment `indexRoot`, the quotient table's two claims against its root (`verify_openings`,
`protocol.rs:661-687`). It accepts when all three openings hold. In the model `F` is the random
permutation; deployed, Keccak-f[1600] (`verify`), at `logRows = 22` and the membership circuit's
commitment (`Circuit.lean`, `Security.lean`).

The EVM contract (`crates/evm`) is the reduction, recorded from the same Rust code
(`crates/evm/src/record.rs`); it leaves the claims to the PCS_OPEN aggregation layer, which this
verifier checks with WHIR directly.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **A proof**: the reduction's proof, and the openings of the witness table's claim, of the wiring
table's claim, and of the quotient table's two claims. -/
structure Proof where
  reduction : ReductionProof
  witness : Compile.Proof
  wiring : Compile.Proof
  quotient : Compile.Proof

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The verifier** over the permutation `F`, on a circuit of `2^logRows` rows committed as
`indexRoot`: the claims of the reduction (`reduceWith`), then the three openings, in the Rust's
order, stopping at the first that fails. -/
def verifyWith (logRows : ℕ) (indexRoot : Digest) (stmt : Statement) (proof : Proof) : m Bool := do
  match ← reduceWith F logRows indexRoot stmt proof.reduction with
  | none => return false
  | some r =>
    if !(← openingWith F (witnessLayout logRows) r.witnessRoot [r.claims.witness] proof.witness)
    then return false
    if !(← openingWith F (wiringLayout logRows) indexRoot [r.claims.wiring] proof.wiring)
    then return false
    openingWith F (quotientLayout logRows) r.quotientRoot [r.claims.quotient, r.claims.sum]
      proof.quotient

end With

/-- The reduction over Keccak-f[1600] (`protocol::verify`): the roots and claims, or `none`. -/
def reduce (logRows : ℕ) (indexRoot : Digest) (stmt : Statement) (p : ReductionProof) :
    Option Reduced :=
  Id.run (reduceWith (m := Id) (fun s ↦ pure (keccakF1600 s)) logRows indexRoot stmt p)

/-- An opening check over Keccak-f[1600] (`opening::verify`). -/
def opening (L : Layout) (root : Digest) (claims : List Claim) (proof : Compile.Proof) : Bool :=
  Id.run (openingWith (m := Id) (fun s ↦ pure (keccakF1600 s)) L root claims proof)

/-- **The deployed verifier**, over Keccak-f[1600], on a circuit of `2^logRows` rows committed as
`indexRoot`. -/
def verify (logRows : ℕ) (indexRoot : Digest) (stmt : Statement) (proof : Proof) : Bool :=
  Id.run (verifyWith (m := Id) (fun s ↦ pure (keccakF1600 s)) logRows indexRoot stmt proof)

end PcsQuotient

end
