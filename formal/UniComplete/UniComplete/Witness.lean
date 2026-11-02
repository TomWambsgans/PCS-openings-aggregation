-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `crates/leanvm_univariate/src/prover/trace.rs`
-- (`Trace::place`) and `tests/prove_tiny.rs` (the padding rows' counters `1`); the stack is `formal/Lv42`'s
-- (leanerVM `mumbai` f0393df4's `LeanIsa.layout`, MIT OR Apache-2.0).
import UniComplete.Prover

/-!
# The placed trace of a witness, and the honest prover

**`honestTrace D input rows q`**: the trace the honest prover proves, read off Lv42's stack `q` (the relation's
witness, `D.Stack rows`) through Lv42's own reading (`LeanIsa.cell`: `M3Instance.column` of `leanIsaInstance`):

* each opcode table's column `i` (`⟨opIdx t, i⟩`; BLAKE2S's limbs `9 … 26` are read, as Lv42 reads them, off
  `QFLOCK`'s slots) at Lv42's row `x`, placed at the univariate PIOP's row `rowPosition count h x` (the executed
  rows at the fixed cosets of the count's set bits, `activePositions`, iteration 2's F1b), the shape's height `h`;
* the padding rows' counters set to `1` (Lv42's padding row `padRow` has zero counters; the PIOP requires
  `z_T Π c = 1` on every row, SPEC.md §13 entry 6, as the Rust's `prove_tiny` and `Trace::place` do);
* the memory's four columns (`memCol`), the bytecode's final counts (`bfcntCol`), at their heights;
* `q_flock` (`flockCol`): Lv42's instance `x` at the PIOP's instance `rowPosition count₅ h₅ x`;
* the bytecode's 16 tuple slots from the program (`tupleSlot`, the setup's), the public input's bytes.

**The honest prover** (`uniProverWith`): `proveWith` on that trace, Flock's prover a parameter, at the main line
(`flockMain`, point claims), `nonceFuel` nonces a proof of work, over `H = keccak256With F` and `F`.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Lv42.Protocol.LeanIsa (Col opIdx kappa width memCol bfcntCol flockCol cell)

/-- Cell `x` of Lv42's column `c` of the stack `q` (`0` past its height). -/
def lv42Cell (D : Deployment) (rows : List ℕ) (q : D.Stack rows) (c : Col) (x : ℕ) : K :=
  if h : x < 2 ^ kappa D.prog (D.sizes rows) c then
    cell Lv42.Protocol.Blake2sFlock.blake2sFlockSpec D.prog (D.sizes rows) q c ⟨x, h⟩
  else 0

/-- Lv42's column `i` of opcode table `t` (`0` past its width). -/
def lv42TableCell (D : Deployment) (rows : List ℕ) (q : D.Stack rows) (t : Fin 6) (i x : ℕ) : K :=
  if h : i < width (opIdx t) then lv42Cell D rows q ⟨opIdx t, ⟨i, h⟩⟩ x else 0

/-- Scatter `2^r` values to their positions: value `x` at `pos x`. -/
def scatter (r : ℕ) (pos : ℕ → ℕ) (value : ℕ → K) : Array K :=
  (List.range (2 ^ r)).foldl (fun a x ↦ a.set! (pos x) (value x)) (Array.replicate (2 ^ r) 0)

/-- **The placed trace of a witness**. -/
def honestTrace (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : Trace :=
  let shape := D.shape
  let table (t : Fin 6) : List (Array K) :=
    let r := shape.heights.getD t.val 0
    let count := rows.getD t.val 0
    let counters := (tables.getD t.val default).countColumns
    (List.range (tables.getD t.val default).width).map fun i ↦
      let placed := scatter r (rowPosition count r) (lv42TableCell D rows q t i)
      if i ∈ counters then
        Array.ofFn (n := 2 ^ r) fun p ↦ if isActive p.val count r then placed.getD p.val 0 else 1
      else placed
  let hB := shape.heights.getD 5 0
  let countB := rows.getD 5 0
  let qflock : Array K := (List.range (2 ^ (hB + 8))).foldl (fun a word ↦
      a.set! (word % 256 + 256 * rowPosition countB hB (word / 256)) (lv42Cell D rows q flockCol word))
    (Array.replicate (2 ^ (hB + 8)) 0)
  let lb := shape.logBytecode
  ⟨shape, rows, (List.finRange 6).map table,
    (List.range 4).map fun k ↦ Array.ofFn (n := 2 ^ shape.logMemory) fun x ↦
      if h : k < 4 then lv42Cell D rows q (memCol ⟨k, h⟩) x.val else 0,
    Array.ofFn (n := 2 ^ lb) fun x ↦ lv42Cell D rows q bfcntCol x.val,
    qflock,
    (List.range 16).map fun s ↦ Array.ofFn (n := 2 ^ lb) fun i ↦
      if h : i.val < 2 ^ D.prog.logSize then tupleSlot D.prog ⟨i.val, h⟩ s else 0,
    input.toList⟩

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The honest prover** over `H`, `F`, Flock's prover given: `proveWith` on the placed trace of the witness, at
the main line, `nonceFuel` nonces a proof of work. -/
def uniProverWith (flock : FlockProver m) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : m (Option UniProof) :=
  proveWith H F PcsQuotient.nonceFuel flock (.flock flockMain) D.programIv (honestTrace D input rows q)

end With

end UniComplete
