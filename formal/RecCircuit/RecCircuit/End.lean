-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Calls

/-!
# The end theorems: π2's ports and π1's `PCS_OPEN` inputs are π1's graph's

For every recorded graph `g` (`RecGraph.Graph`) the compiler accepts (`compile (ofRG g rootsAt iv) = .ok c`: the
transcription of `compile.rs` ran, and every check of `Check.lean` passed), on every witness satisfying π2's PIOP
(`RecPiop`'s `Satisfies`): the ports and the `PCS_OPEN` inputs π2's verifier rebuilds from them are what `g` outputs
in `RecGraph`'s semantics (`RecGraph.evalNodes` over Keccak-f[1600]) on the public input and the stream the witness
encodes (`pubW`, `streamW`). No hypothesis is left (`ExpandSound` is `expandSound`):

* `compile_sound_statement`, `compile_sound_root` (`SoundRG.lean`): the statement's and the roots' ports;
* `compile_sound_element_end`: an element port, `RecGraph`'s value of any original node mapped to its node;
* `compile_sound_zero_end`, `compile_sound_zero_const`: the `m`-th zero port carries the `m`-th zero check whose image
  is not a constant; every other zero check is `0`;
* `compile_sound_calls`, `compile_sound_callInputs` (`Calls.lean`): π1's `PCS_OPEN` inputs.

`compile_sound_end` bundles them.
-/

namespace RecCircuit

open Primitives LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

namespace Compiled

variable {c : Compiled} {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8}

/-- π1's zero checks name nodes of its graph (`Graph.outputsIn`). -/
theorem zero_lt (hc : compile (ofRG g rootsAt iv) = .ok c) : ∀ id ∈ g.zero, id < g.nodes.size := by
  obtain ⟨ht, -⟩ := compileRaw_ok (compileRaw_of_compile hc)
  simp only [Graph.typed, Graph.outputsIn, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  intro id hid
  have := ht.2.1 id (List.mem_append_left _ hid)
  simpa [ofRG] using this

/-- **Element `e`'s port carries `RecGraph`'s value of any original node mapped to the `e`-th element node.** -/
theorem compile_sound_element_end (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) {J e : ℕ} (hJ : J < c.circuit.ports.size)
    (hs : (c.circuit.ports.getD J default).source = .element e) {id : ℕ} (hid : id < g.nodes.size)
    (hmap : c.map.getD id 0 = c.elementNodes.getD e 0) :
    c.circuit.portLimbs w J =
      limbsL (RecGraph.valE (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) id) :=
  compile_sound_element hc hw (expandSound hc) hJ hs hid hmap

/-- **The zero ports carry `RecGraph`'s values of π1's zero checks**: the `m`-th zero port the `m`-th whose image is
not a constant. -/
theorem compile_sound_zero_end (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    ∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs w J = limbsL (RecGraph.valE
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) (zeroOrig c (ofRG g rootsAt iv) (c.zeroIndex J))) :=
  compile_sound_zero_rg hc hw (zero_lt hc) (expandSound hc)

/-- **The other zero checks are zero**: a zero check whose image is a constant is `0`, on every IV, public input and
stream. -/
theorem compile_sound_zero_const (hc : compile (ofRG g rootsAt iv) = .ok c) (iv' pub stream : List UInt8) :
    ∀ id ∈ g.zero, notConst (c.nodes.getD (c.map.getD id 0) default) = false →
      RecGraph.valE (rgVals g iv' pub stream) id = 0 := by
  intro id hid hnc
  have hz := (checked_of_compile hc).zeroConst
  unfold zeroConstOk at hz
  rw [List.all_eq_true] at hz
  have h := hz id hid
  rw [← expandSound hc iv' pub stream id (zero_lt hc id hid)]
  generalize hn : c.nodes.getD (c.map.getD id 0) default = n at h hnc
  cases n <;> simp only [notConst, Bool.true_eq_false] at hnc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, hq⟩ := h
  have hx := rgX_node c iv' pub stream hq (by rw [hn]; intro k m e; cases e) (by rw [hn]; intro o ho; cases ho)
  rw [hn] at hx
  rw [valE_elem (hx.trans (congrArg some (stepP_const _ _ _ _ _))), h0]

/-- **What the end theorem states** of a compiled circuit `c` for `g` and a witness `w`: π2's ports and the
`PCS_OPEN` inputs its verifier rebuilds from them are π1's graph's outputs in `RecGraph`'s semantics over
Keccak-f[1600], on the public input and the stream the witness encodes: the statement's words, the roots' words, the
zero checks' values (the constant ones `0`), the calls' bytes (word 0 as `PCS_OPEN`'s root word). -/
def EndStatement (g : RecGraph.Graph) (rootsAt : List ℕ) (iv : List UInt8) (c : Compiled) (w : ℕ → K) : Prop :=
    (∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .statement →
      c.circuit.portLimbs w J = (List.range 4).map fun k => K.ofLane (beWordAt (c.pubW w).toArray (8 * k))) ∧
    (∀ J < c.circuit.ports.size, ∀ i, (c.circuit.ports.getD J default).source = .root i →
      c.circuit.portLimbs w J = (List.range 4).map fun l =>
        F64.ofNat (leNat (slice ((c.streamW (ofRG g rootsAt iv) w).toArray.extract (rootsAt.getD i 0)
          (rootsAt.getD i 0 + 32)).toList ([16, 24, 0, 8].getD l 0) 8))) ∧
    (∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs w J = limbsL (RecGraph.valE
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) (zeroOrig c (ofRG g rootsAt iv) (c.zeroIndex J)))) ∧
    (∀ id ∈ g.zero, notConst (c.nodes.getD (c.map.getD id 0) default) = false →
      RecGraph.valE (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) id = 0) ∧
    c.circuit.callInputs w = g.calls.map fun ws => (List.range ws.length).flatMap fun k =>
      pcsWord k (RecGraph.wordBytes (c.streamW (ofRG g rootsAt iv) w).toArray
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) (ws.getD k default))

/-- **The end theorem**: on a satisfied circuit the compiler accepted, `EndStatement`. -/
theorem compile_sound_end (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) : EndStatement g rootsAt iv c w :=
  ⟨fun _ hJ hs => compile_sound_statement hc hw hJ hs, fun _ hJ _ hs => compile_sound_root hc hw hJ hs,
    compile_sound_zero_end hc hw, compile_sound_zero_const hc _ _ _, compile_sound_callInputs hc hw⟩

end Compiled

end RecCircuit
