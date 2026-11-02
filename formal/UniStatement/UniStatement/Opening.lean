-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `PCS_OPEN`'s ABI is `crates/evm/src/machine.rs`'s
-- (as `crates/leanvm_flock_gas/src/evm/machine.rs` mocks it); its semantics is this repository's `formal/Statement`
-- opening (`PcsQuotient.openingWith`: leanerVM `mumbai` 6175f1a0's WHIR verifier, MIT OR Apache-2.0).
module

public import UniStatement.Run
public import PcsQuotient.Opening

/-!
# `PCS_OPEN` and the whole verifier (the main line)

**`PCS_OPEN`** (`machine.rs`'s ABI: a root, a layout id, `k` point claims, each `v` coordinates and a
value): "the block's openings hold exactly these claims on that commitment under that layout". As in
`formal/Statement` (`formal/EndToEnd/Evm`'s `pcsOpen`), its meaning here is **the Statement's opening**,
`PcsQuotient.openingWith` (leanVM's WHIR verifier, mumbai's `verifyStackedOpening`, seeded as
`opening.rs` seeds it), on the call's opening proof, for the **plain layout** of a stack of `2^vars`
words (`plainLayout`: lane `l` holds block `l`, so a claim's weight on the stack is `eq(point, ·)`: a point
claim on the stack's multilinear extension). The Rust has only a mock (`PcsOpen::attesting_all`): which
WHIR instance the precompile runs is not specified there; this is the choice the statements are made under.

**The whole verifier** (`verifyWith`, the main line: Flock (a′), `PCS_OPEN`'s point-claim ABI): the proof's
row counts (REVIEW-M1 F1: announced, absorbed in the seed; the encoding `rowsBytes` is provisional until the
Rust fixes it), the run on the stream (`runWith`), its verdict, then **five calls**, in the contract's order: `C1`, `C2`, the setup
(each its one point claim, on its root: `C1`'s and `C2`'s the stream's, the setup's a constant), then
Flock's `A0` and `B0` (one point claim each, `2^28` words). The extensions (weighted claims, the bit-slice
claim type) are precompile changes with no opening defined here; `verifyWith` rejects them.
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

/-- **A proof**: its row counts (REVIEW-M1 F1: announced, absorbed in the seed), the stream (calldata after
the selector and the public input), and the opening proof the block holds for each of the five `PCS_OPEN`
calls (mumbai's format, `Compile.Proof`). -/
structure UniProof where
  rows : List ℕ
  stream : Array UInt8
  c1 : Compile.Proof
  c2 : Compile.Proof
  setup : Compile.Proof
  a0 : Compile.Proof
  b0 : Compile.Proof

/-- `A0`'s and `B0`'s stacks: `2^28` words, the R1CS of `2^14` positions. -/
def matrixVars : ℕ := 2 * blake2sR1csLogSize

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`PCS_OPEN`** over `F`: the claims on the stack of `2^vars` words committed as `root`, against the
call's opening proof. -/
def pcsOpenWith (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    m Bool :=
  PcsQuotient.openingWith F (plainLayout vars) root claims proof

/-- **The verifier** over `F` (the main line): the proof's row counts fit the shape, the run at them (the seed
absorbing them after the public input, `rowsBytes`), its verdict, the five `PCS_OPEN` calls. -/
def verifyWith (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) : m Bool := do
  if !decide (shape.RowsFit proof.rows) then return false
  let o ← runWith F shape proof.rows iv publicInput.toList (rowsBytes proof.rows) proof.stream
    (.flock flockMain) .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let varsOf (c : Commitment) : ℕ := (r.stackVars.lookup c).getD 0
    let callOf : Commitment → Digest × Compile.Proof
      | .c1 => (rootOf r.roots.1, proof.c1)
      | .c2 => (rootOf r.roots.2, proof.c2)
      | .setup => (roots.bytecode, proof.setup)
    -- C1, C2, the setup: one point claim each.
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, p) := callOf c
        ok := ok && (← pcsOpenWith F (varsOf c) root [⟨pt, value⟩] p)
      | _ => ok := false
    -- Flock's matrices.
    match r.matrices with
    | some mc =>
      ok := ok && (← pcsOpenWith F matrixVars roots.a0 [⟨mc.point, mc.a⟩] proof.a0)
      ok := ok && (← pcsOpenWith F matrixVars roots.b0 [⟨mc.point, mc.b⟩] proof.b0)
    | none => ok := false
    return ok

end With

end UniStatement

end
