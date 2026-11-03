-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Agree

/-!
# The ports carry π1's graph's outputs, in `RecGraph`'s semantics

With `agree` (this library's semantics is `RecGraph`'s on every live node of the expanded graph), the end theorem's
ports read against `RecGraph.evalNodes` of the original graph (`rgVals`, over Keccak-f[1600]), given one named
obligation in `RecGraph`'s semantics only, **`ExpandSound`**: the expansion (`compile.rs`'s `expand`) keeps every live
node's value, the expanded graph's `RecGraph` value at a node's image being the original graph's value of the node.

* `compile_sound_statement`: the statement port carries the public input's four words as `RecGraph` reads them
  (`beWordAt`, the `statement` nodes' values);
* `compile_sound_root`: root `i`'s port carries the little-endian words of the 32 bytes `RecGraph`'s call word
  `Word.stream at` outputs, bytes `16, 24, 0, 8` (the `PCS_OPEN` root word's limbs);
* `compile_sound_element`: element `e`'s port carries `RecGraph`'s value of any original node the expansion maps to the
  calls' `e`-th element node;
* `compile_sound_zero_rg`: the `m`-th zero port carries `RecGraph`'s value of the `m`-th non-constant zero check.
-/

namespace RecCircuit

open Primitives LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

/-- **The named obligation, in `RecGraph`'s semantics only**: at every original node whose image is live, the
expanded graph's value (`RecGraph`'s, `Compiled.rgX`) is the original graph's (`rgVals`). -/
def ExpandSound (g : RecGraph.Graph) (c : Compiled) : Prop :=
  ∀ (iv pub stream : List UInt8), ∀ id < g.nodes.size, c.live.getD (c.map.getD id 0) false = true →
    (c.rgX iv pub stream)[c.map.getD id 0]? = (rgVals g iv pub stream)[id]?

namespace Compiled

variable {c : Compiled} {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8}

/-- A live expanded node's element, in `RecGraph`'s semantics of the original graph. -/
theorem elem_rg (hc : c.Checked (ofRG g rootsAt iv)) (hE : ExpandSound g c) (w : ℕ → K) {k id : ℕ}
    (hk : k < c.nodes.size) (hlk : c.live.getD k false = true) (hid : id < g.nodes.size) (hmap : c.map.getD id 0 = k) :
    ((c.valsW (ofRG g rootsAt iv) w).getD k default).toE =
      RecGraph.valE (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) id := by
  obtain ⟨b, hb, hcorr⟩ := agree hc (c.pubW w) (c.streamW (ofRG g rootsAt iv) w) (decodePublic_length _)
    streamW_length k hk hlk
  have hiv : (ofRG g rootsAt iv).iv = iv := rfl
  rw [hiv] at hb hcorr
  have hs := hE iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w) id hid (by rw [hmap]; exact hlk)
  rw [hmap, hb] at hs
  exact Corr.toE hcorr hs.symm

/-- **The statement port carries the public input's words as `RecGraph` reads them.** -/
theorem compile_sound_statement (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) {J : ℕ} (hJ : J < c.circuit.ports.size)
    (hs : (c.circuit.ports.getD J default).source = .statement) :
    c.circuit.portLimbs w J = (List.range 4).map fun k => K.ofLane (beWordAt (c.pubW w).toArray (8 * k)) := by
  rw [compile_sound hc hw J hJ, portMeaning, hs]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [beWordAt_eq _ _ (by simp [pubW, decodePublic_length]; omega)]

/-- **Root `i`'s port carries the root word's limbs of `RecGraph`'s stream word** at `rootsAt[i]`. -/
theorem compile_sound_root (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) {J i : ℕ} (hJ : J < c.circuit.ports.size)
    (hs : (c.circuit.ports.getD J default).source = .root i) :
    c.circuit.portLimbs w J = (List.range 4).map fun l =>
      F64.ofNat (leNat (slice ((c.streamW (ofRG g rootsAt iv) w).toArray.extract (rootsAt.getD i 0)
        (rootsAt.getD i 0 + 32)).toList ([16, 24, 0, 8].getD l 0) 8)) := by
  rw [compile_sound hc hw J hJ, portMeaning, hs]
  apply List.map_congr_left
  intro l hl
  rw [List.mem_range] at hl
  rw [extract_toList, show rootsAt.getD i 0 + 32 - rootsAt.getD i 0 = 32 by omega,
    slice_slice _ _ _ _ _ (by interval_cases l <;> decide)]
  rfl

/-- **Element `e`'s port carries `RecGraph`'s value of the call's node**, for any original node the expansion maps to
the calls' `e`-th element node. -/
theorem compile_sound_element (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) (hE : ExpandSound g c) {J e : ℕ} (hJ : J < c.circuit.ports.size)
    (hs : (c.circuit.ports.getD J default).source = .element e) {id : ℕ} (hid : id < g.nodes.size)
    (hmap : c.map.getD id 0 = c.elementNodes.getD e 0) :
    c.circuit.portLimbs w J =
      limbsL (RecGraph.valE (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) id) := by
  have hchk := checked_of_compile hc
  rw [compile_sound hc hw J hJ, portMeaning, hs]
  simp only
  have hso := allBelow_spec hchk.sources J hJ
  simp only [hs, decide_eq_true_eq] at hso
  have hmem := (graphOk_parts hchk.graph).2.2.1 (c.elementNodes.getD e 0) (by
    apply List.mem_append_right
    simpa [Array.getD_eq_getD_getElem?, hso] using Array.getElem_mem_toList hso)
  rw [elem_rg hchk hE w hmem.1 hmem.2 hid hmap]

/-- **The zero ports carry `RecGraph`'s values of π1's zero checks**, given `ExpandSound`. -/
theorem compile_sound_zero_rg (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) (hz : ∀ id ∈ g.zero, id < g.nodes.size) (hE : ExpandSound g c) :
    ∀ J < c.circuit.ports.size, (c.circuit.ports.getD J default).source = .zero →
      c.circuit.portLimbs w J = limbsL (RecGraph.valE
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) (zeroOrig c (ofRG g rootsAt iv) (c.zeroIndex J))) := by
  intro J hJ hsrc
  have hchk := checked_of_compile hc
  rw [compile_sound hc hw J hJ, portMeaning, hsrc]
  simp only
  set r := ofRG g rootsAt iv
  have hzero : c.zero = r.graph.zero.map (fun id => c.map.getD id 0) := (graphOk_parts hchk.graph).2.1
  have hso := allBelow_spec hchk.sources J hJ
  simp only [hsrc, decide_eq_true_eq] at hso
  set P := fun id => notConst (c.nodes.getD id default)
  have hP : (P ∘ fun id => c.map.getD id 0) = (fun id => notConst (c.nodes.getD (c.map.getD id 0) default)) := rfl
  have hzn : c.zeroNodes = (r.graph.zero.filter (P ∘ fun id => c.map.getD id 0)).map (fun id => c.map.getD id 0) := by
    unfold zeroNodes; rw [hzero, List.filter_map]
  rw [hP] at hzn
  have hlen : c.zeroIndex J < (r.graph.zero.filter
      (fun id => notConst (c.nodes.getD (c.map.getD id 0) default))).length := by
    rw [hzn, List.length_map] at hso; exact hso
  have hget : c.zeroNodes.getD (c.zeroIndex J) 0 = c.map.getD (zeroOrig c r (c.zeroIndex J)) 0 := by
    rw [hzn]
    simp only [zeroOrig, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen,
      Option.map_some, Option.getD_some]
  have hmemz : zeroOrig c r (c.zeroIndex J) ∈ g.zero := by
    have : zeroOrig c r (c.zeroIndex J) ∈ r.graph.zero.filter
        (fun id => notConst (c.nodes.getD (c.map.getD id 0) default)) := by
      simp only [zeroOrig, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
      exact List.getElem_mem hlen
    exact (List.mem_filter.mp this).1
  have hmem := (graphOk_parts hchk.graph).2.2.1 (c.zeroNodes.getD (c.zeroIndex J) 0) (by
    apply List.mem_append_left
    simp [List.getD_eq_getElem?_getD, hso])
  rw [elem_rg hchk hE w hmem.1 hmem.2 (hz _ hmemz) hget.symm]

end Compiled

end RecCircuit
