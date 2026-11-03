-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Piop
import RecGraph.Semantics

/-!
# π2's circuit computes π1's recorded verifier

**`compile_sound`**: if the compiler accepts π1's recorded verifier `r` (`compile r = .ok c`: the transcription of
`compile.rs` ran, and the checker accepted its circuit) and a witness of `K` words satisfies π2's PIOP's relation for
that circuit (`RecPiop.Circuit.Satisfies`, through `Circuit.toPiop`), then every port carries what its source means
(`portMeaning`): the public input's words, the roots' words, the calls' elements' and the zero checks' values in the
expanded graph, zero pads, on the public input and the stream the witness's free bits encode.

**Against `RecGraph`'s semantics** (`compile_sound_zero`): with the compiler's input `ofRG g` for a `RecGraph.Graph`
`g` (π1-rec3's is `RecGraph.Emitted.graph`), the zero ports carry `RecGraph.evalNodes`'s values of `g`'s non-constant
zero checks, over Keccak-f[1600], given **`ExpandFaithful`**: that the expanded graph (`Expand.lean`, `compile.rs`'s
`expand`), evaluated by this library's transcription of `eval.rs` (`Graph.eval`), agrees at every node's image with
`RecGraph.evalNodes` on the original graph. This is the earlier form; the end theorems need no such hypothesis
(`End.lean`: `agree` and `expandSound` prove the narrower `ExpandSound` they use).
-/

namespace RecCircuit

open Primitives LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **π2's circuit computes the expanded graph's outputs.** -/
theorem compile_sound {r : Recorded} {c : Compiled} (hc : compile r = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    ∀ J < c.circuit.ports.size, c.circuit.portLimbs w J = c.portMeaning r w J :=
  Compiled.ports_carry (Compiled.checked_of_compile hc) (satisfied_of_piop _ hw)

/-- The same, from a fixed point of the circuit's dataflow (`RecPiop.Circuit.copy_iff_flow`). -/
theorem compile_sound_flow {r : Recorded} {c : Compiled} (hc : compile r = .ok c) (hV : c.circuit.toPiop.Valid)
    {w : ℕ → K} (hw : c.circuit.toPiop.flow (emb w) = emb w) :
    ∀ J < c.circuit.ports.size, c.circuit.portLimbs w J = c.portMeaning r w J :=
  Compiled.ports_carry (Compiled.checked_of_compile hc) (satisfied_of_flow _ hV hw)

/-! ## `RecGraph`'s graphs and semantics -/

def ofRGWord : RecGraph.Word → Word
  | .node id => .node id
  | .const w => .const w
  | .stream a => .stream a

/-- **The compiler's input for a `RecGraph` graph**, its roots' offsets and π1's contract IV. -/
def ofRG (g : RecGraph.Graph) (rootsAt : List ℕ) (iv : List UInt8) : Recorded :=
  ⟨⟨g.nodes.map ofRGNode, g.zero, g.nonzero, g.kernels, g.calls.map (·.map ofRGWord), g.streamLen⟩, rootsAt, iv⟩

/-- A value of this library's semantics and `RecGraph`'s agree: the same element, or a state and its digest's
bytes. -/
def Corr : Value → RecGraph.Value → Prop
  | .e x, .elem y => x = y
  | .state s, .state d => s = digestBytes d
  | _, _ => False

/-- `RecGraph`'s node values over Keccak-f[1600] (the deployed contract's). -/
def rgVals (g : RecGraph.Graph) (iv pub stream : List UInt8) : Array RecGraph.Value :=
  RecGraph.evalNodes (m := Id) (fun s => pure (keccakF1600 s)) g iv pub stream.toArray

/-- **The named obligation: the expansion keeps `RecGraph`'s meaning.** At every node of the original graph, the
expanded graph's value (this library's `Graph.eval`) at the node's image is `RecGraph`'s value of the node. -/
def ExpandFaithful (g : RecGraph.Graph) (c : Compiled) (r : Recorded) : Prop :=
  ∀ (pub stream : List UInt8), ∀ id < g.nodes.size, ∃ b, (rgVals g r.iv pub stream)[id]? = some b ∧
    Corr (((c.egraph r).eval r.iv pub stream).getD (c.map.getD id 0) default) b

theorem Corr.toE {a : Value} {b : RecGraph.Value} (h : Corr a b) {vals : Array RecGraph.Value} {i : ℕ}
    (hb : vals[i]? = some b) : a.toE = RecGraph.valE vals i := by
  unfold RecGraph.valE
  rw [hb]
  cases a <;> cases b <;> simp_all [Corr, Value.toE]

/-- The original zero check the `m`-th zero port carries: the `m`-th whose image is not a constant. -/
def zeroOrig (c : Compiled) (r : Recorded) (m : ℕ) : ℕ :=
  (r.graph.zero.filter fun id => Compiled.notConst (c.nodes.getD (c.map.getD id 0) default)).getD m 0

/-- **The zero ports carry `RecGraph`'s values of π1's zero checks** (over Keccak-f[1600]), given the named
obligation `ExpandFaithful`. -/
theorem compile_sound_zero {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8} {c : Compiled}
    (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) (hz : ∀ id ∈ g.zero, id < g.nodes.size)
    (hE : ExpandFaithful g c (ofRG g rootsAt iv)) :
    ∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs w J = Compiled.limbsL (RecGraph.valE
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) (zeroOrig c (ofRG g rootsAt iv) (c.zeroIndex J))) := by
  intro J hJ hsrc
  have hchk := Compiled.checked_of_compile hc
  rw [compile_sound hc hw J hJ, Compiled.portMeaning, hsrc]
  simp only
  set r := ofRG g rootsAt iv
  have hzero : c.zero = r.graph.zero.map (fun id => c.map.getD id 0) := (Compiled.graphOk_parts hchk.graph).2.1
  have hso := allBelow_spec hchk.sources J hJ
  simp only [hsrc, decide_eq_true_eq] at hso
  set P := fun id => Compiled.notConst (c.nodes.getD id default)
  have hP : (P ∘ fun id => c.map.getD id 0) =
      (fun id => Compiled.notConst (c.nodes.getD (c.map.getD id 0) default)) := rfl
  have hzn : c.zeroNodes = (r.graph.zero.filter (P ∘ fun id => c.map.getD id 0)).map (fun id => c.map.getD id 0) := by
    unfold Compiled.zeroNodes; rw [hzero, List.filter_map]
  rw [hP] at hzn
  have hlen : c.zeroIndex J < (r.graph.zero.filter
      (fun id => Compiled.notConst (c.nodes.getD (c.map.getD id 0) default))).length := by
    rw [hzn, List.length_map] at hso; exact hso
  have hget : c.zeroNodes.getD (c.zeroIndex J) 0 = c.map.getD (zeroOrig c r (c.zeroIndex J)) 0 := by
    rw [hzn]
    simp only [zeroOrig, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen,
      Option.map_some, Option.getD_some]
  rw [hget]
  have hmem : zeroOrig c r (c.zeroIndex J) ∈ g.zero := by
    have : zeroOrig c r (c.zeroIndex J) ∈ r.graph.zero.filter
        (fun id => Compiled.notConst (c.nodes.getD (c.map.getD id 0) default)) := by
      simp only [zeroOrig, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
      exact List.getElem_mem hlen
    exact (List.mem_filter.mp this).1
  obtain ⟨b, hb, hcorr⟩ := hE (c.pubW w) (c.streamW r w) _ (hz _ hmem)
  show Compiled.limbsL (((c.egraph r).eval r.iv (c.pubW w) (c.streamW r w)).getD _ default).toE = _
  rw [Corr.toE hcorr hb]
  rfl

end RecCircuit
