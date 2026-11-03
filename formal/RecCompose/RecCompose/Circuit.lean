-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Part1
import RecCircuit.Pi1Rec3

/-!
# `Pi2Layers.circuit` from RecCircuit's end theorem

RecCircuit's `pi1rec3_end` (branch `lean-rec-circuit`, merged at `leanvm-rec` d93c375; no hypothesis but the compiler's
run `hc`): on π2's circuit for π1-rec3's emitted graph, every witness satisfying π2's PIOP has ports and rebuilt
`PCS_OPEN` inputs equal to the graph's outputs over Keccak-f[1600] (`EndStatement`: the statement's words, the roots'
words, the zero checks' values, the constant ones `0`, π1's three calls word for word, word 0 as `PCS_OPEN`'s root
word `pcsWord`). What is left to the field `Pi2Layers.circuit` is the bridge from that statement, read at π2's
public limbs, to RecStatement's `Pi1GraphAccepts` with the contract's π1 openings (`CircuitBridge`), and that the
Lean recording of π1-rec3's verifier is the emitted graph (`GraphsAgree`).

* `GraphsAgree`: `RecGraph.Pi1.pi1Graph = RecGraph.Emitted.graph` (the Lean recorder's graph, which RecStatement's
  statements name, is the Rust's, which RecCircuit's instance compiles). **A run, not a proof**:
  `RecGraph/RecGraphTest/Pi1Check.lean` compares them node for node (compiled evaluation; no kernel evaluation of the
  `166K`-node graph).
* `CircuitBridge` (**open, `lean-rec-compose`**): at π2's public limbs `pub` of the calldata, `EndStatement` gives
  `Pi1GraphAccepts`: the statement port and `Satisfies` make the witness's public input the calldata's; the zero ports'
  public limbs are zero, so every zero check of the graph is (the constant ones are by `EndStatement`), and the graph has
  no nonzero check; the stream decoded has the graph's length; the circuit's `callInputs` read at `pub` are the
  contract's π1 call words (RecStatement's `callWord`: the stream's root words, the claims' elements, their pair
  points), so `decodePi1Call` of the graph's calls (word 0 raw, the contract's `pcsWord` of it) gives the contract's
  openings' layouts, claims, and `C1`'s and `C2`'s roots. (To check there: that `Pi1GraphAccepts` compares `C1`'s and
  `C2`'s roots in one encoding, `decodePi1Call` reading the graph's raw word 0 with `rootOfWord` and `decodeWith` the
  contract's word 0, `pcsWord` of it, with `rootOfWord` too.)
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol
open scoped ENNReal

/-- **π1's roots' words in π2's calls name π1-rec3's WHIR roots** (the composition's finding; the fix, option (a),
branch `fix-pi1-root`, merged): the word 0 of π1's `C1`, `C2` calls the circuit rebuilds from a root's 32 stream bytes
`raw` (`RecCircuit.pcsWord 0 (.stream at) raw`), decoded as the contract's `PCS_OPEN` decodes it (`rootOfWord`), is the
digest π1-rec3's verifier opens (`UniStatement.rootOf` of the halves `nextRoot` reads, which is `rootOfWord raw`). At
`leanvm-rec` d93c375 it was false: `pcsWord` reversed each 16-byte half and π2's stream carried the reversed word (the
real vectors: π2's stream started `b25c056f…`, π1's `C1` root `f30c504d…`), so the contract decoded `digestOfBytes32 raw`;
`Pi1GraphAccepts`'s roots then disagreed on honest proofs and the contract opened π1's commitments at other digests than
π1-rec3's. With the fix `pcsWord` keeps a stream root's word as it is: `pi1RootWordOk`. -/
def Pi1RootWordOk : Prop :=
  ∀ (at' : ℕ) (raw : List UInt8), rootOfWord (RecCircuit.pcsWord 0 (.stream at') raw) = rootOfWord raw

/-- **The corrected root word** (`fix-pi1-root`): a stream root's word is kept as it is. -/
theorem pi1RootWordOk : Pi1RootWordOk := fun _ _ ↦ rfl

/-- **The Lean recording of π1-rec3's verifier is the emitted graph** (a run: `RecGraphTest/Pi1Check.lean`). -/
def GraphsAgree : Prop := RecGraph.Pi1.pi1Graph = RecGraph.Emitted.graph

/-- **The bridge from RecCircuit's end statement to `Pi1GraphAccepts`**: a witness satisfying π2's circuit at π2's
public limbs `pub` of the calldata, whose ports and rebuilt calls are the emitted graph's outputs (`EndStatement`),
holds a π1 stream (`D.pi1Stream`) on which π1-rec3's graph accepts with the contract's π1 openings. -/
def CircuitBridge (D : RecDeployment) (compiled : List UInt8 → RecCircuit.Compiled)
    (pub : RecSetupRoots → Vector UInt8 32 → Array UInt8 → ℕ → List Primitives.F192) : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) (w : ℕ → K) (ops : List Pi1Opening),
    ((compiled (D.pi1IvAt roots.pi1)).circuit.toPiop).Satisfies (pub roots input stream) (RecCircuit.emb w) →
      RecCircuit.Compiled.EndStatement RecGraph.Emitted.graph RecGraph.Emitted.rootsAt (D.pi1IvAt roots.pi1)
        (compiled (D.pi1IvAt roots.pi1)) w →
      pi1OpsOf D roots input stream = some ops →
        Pi1GraphAccepts (D.pi1IvAt roots.pi1) input (D.pi1Stream w) ops

/-- **`Pi2Layers.circuit`, from RecCircuit's end theorem**: given the compiler's run on the emitted graph (`hc`, at
π1's roots' offsets `RecGraph.Emitted.rootsAt`), the bridge gives the field's statement. -/
theorem circuit_of_bridge {D : RecDeployment} {compiled : List UInt8 → RecCircuit.Compiled}
    {pub : RecSetupRoots → Vector UInt8 32 → Array UInt8 → ℕ → List Primitives.F192}
    (hc : ∀ iv, RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) =
      .ok (compiled iv))
    (hb : CircuitBridge D compiled pub) :
    ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) (w : ℕ → K) (ops : List Pi1Opening),
      ((compiled (D.pi1IvAt roots.pi1)).circuit.toPiop).Satisfies (pub roots input stream) (RecCircuit.emb w) →
        pi1OpsOf D roots input stream = some ops →
          Pi1GraphAccepts (D.pi1IvAt roots.pi1) input (D.pi1Stream w) ops :=
  fun roots input stream w ops hw hops ↦
    hb roots input stream w ops hw (RecCircuit.pi1rec3_end (hc _) hw) hops

/-- **`Pi2Layers.compile_ok` from the compiler's run on the emitted graph**, the graphs agreeing. -/
theorem compile_ok_of_emitted {compiled : List UInt8 → RecCircuit.Compiled} (hg : GraphsAgree)
    (hc : ∀ iv, RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) =
      .ok (compiled iv)) :
    ∀ iv, RecCircuit.compile (RecCircuit.ofRG RecGraph.Pi1.pi1Graph RecGraph.Emitted.rootsAt iv) =
      .ok (compiled iv) := by
  intro iv
  unfold GraphsAgree at hg
  rw [hg]
  exact hc iv

end RecCompose

/-- info: 'RecCompose.circuit_of_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.circuit_of_bridge
