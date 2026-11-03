-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Nodes

/-!
# The ports carry the graph's outputs

`ports_carry`: on a satisfied accepted circuit, every port's limbs (as the witness carries them, `portLimbs`) are what
its source means (`portMeaning`), on the public input and the stream the witness's free bits encode:

* the statement port: the public input's four big-endian words;
* root `i`'s port: the big-endian words of the stream's bytes `at + 24, at + 16, at + 8, at` (root `i` at `at`),
  that is `PCS_OPEN`'s root word's four big-endian limbs, the word being the stream's 32 bytes (REVIEW-REC.md R1);
* element `e`'s port: the limbs of the value of the calls' `e`-th element node (a pair's challenge for a pair's
  coordinates), in the expanded graph;
* the `m`-th zero port: the limbs of the value of the graph's `m`-th non-constant zero check;
* a padding port: zero.
-/

namespace RecCircuit

open Primitives PcsCircuit

namespace Compiled

variable {c : Compiled} {r : Recorded} {w : ℕ → K}

/-- An element's three limbs. -/
def limbsL (x : F192) : List K := [x.limb 0, x.limb 1, x.limb 2]

/-- **What port `J` means**, on the witness's public input and stream. -/
def portMeaning (c : Compiled) (r : Recorded) (w : ℕ → K) (J : ℕ) : List K :=
  match (c.circuit.ports.getD J default).source with
  | .statement => (List.range 4).map fun k => F64.ofNat (beNat (slice (c.pubW w) (8 * k) 8))
  | .root i => (List.range 4).map fun l =>
      F64.ofNat (beNat (slice (c.streamW r w) (r.rootsAt.getD i 0 + [24, 16, 8, 0].getD l 0) 8))
  | .element e => limbsL ((c.valsW r w).getD (c.elementNodes.getD e 0) default).toE
  | .zero => limbsL ((c.valsW r w).getD (c.zeroNodes.getD (c.zeroIndex J) 0) default).toE
  | .pad => [0, 0, 0]

theorem portsOk_parts (h : c.portsOk c.ctx = true) :
    ∀ J < c.circuit.ports.size,
      let p := c.circuit.ports.getD J default
      p.position < c.ctx.n ∧ c.circuit.formulaAt p.position = .port (List.range p.source.limbs) ∧
      (c.portValues c.ctx J).size = p.source.limbs ∧
      (∀ l < p.source.limbs, (c.portValues c.ctx J).getD l NONE ≠ NONE ∧
        c.ctx.cellAt (c.ctx.rowStart p.position + l) = (c.portValues c.ctx J).getD l NONE) ∧
      (p.source = .pad → ∀ l < 3, c.ctx.constOk ((c.portValues c.ctx J).getD l NONE) 0 = true) := by
  intro J hJ
  unfold portsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have := allBelow_spec h.2 J hJ
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨⟨hpos, hf⟩, hs⟩, hl⟩, hpad⟩ := this
  refine ⟨hpos, hf, hs, fun l hl' => ?_, fun hp => ?_⟩
  · have := allBelow_spec hl l hl'
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    exact this
  · rcases hpad with h | h
    · exact absurd hp h
    · exact fun l hl => allBelow_spec h l hl

/-- A port's limbs as the witness carries them are its values' words. -/
theorem portLimbs_eq (hc : c.Checked r) (hw : c.circuit.Satisfied w) {J : ℕ} (hJ : J < c.circuit.ports.size) :
    c.circuit.portLimbs w J =
      (List.range (c.circuit.ports.getD J default).source.limbs).map fun l =>
        c.ctx.val w ((c.portValues c.ctx J).getD l NONE) := by
  have G := hc.good hw
  obtain ⟨hpos, hf, _, hl, _⟩ := portsOk_parts hc.ports J hJ
  unfold Circuit.portLimbs
  simp only [hf]
  apply List.map_congr_left
  intro l hlm
  rw [List.mem_range] at hlm
  obtain ⟨hne, hcell⟩ := hl l hlm
  have hW : c.ctx.W = c.circuit.width := rfl
  rw [Circuit.cells]
  have hq := c.ctx.cellAt_lt G.view (q := c.ctx.rowStart (c.circuit.ports.getD J default).position + l)
    (by rw [hcell]; exact hne)
  exact c.ctx.val_holds G.view G.kd G.sat hq hcell hne

/-- An element node's limbs, as a port's values. -/
theorem elem_port (hc : c.Checked r) (hw : c.circuit.Satisfied w) {id : ℕ} (hid : id < c.nodes.size)
    (hl : c.live.getD id false = true) (h3 : (c.limbsOf id).size = 3) :
    (List.range 3).map (fun l => c.ctx.val w ((c.limbsOf id).getD l NONE)) =
      limbsL ((c.valsW r w).getD id default).toE := by
  have hinv := node_inv hc hw id hid hl
  unfold NodeInv at hinv
  rw [elem_of_limbs3 hc hid hl h3, if_neg (by simp)] at hinv
  rw [← hinv.2]
  simp [limbsL, List.range_succ]

/-- **Every port carries what its source means.** -/
theorem ports_carry (hc : c.Checked r) (hw : c.circuit.Satisfied w) :
    ∀ J < c.circuit.ports.size, c.circuit.portLimbs w J = c.portMeaning r w J := by
  intro J hJ
  have G := hc.good hw
  rw [portLimbs_eq hc hw hJ]
  obtain ⟨_, _, hsize, hl, hpad⟩ := portsOk_parts hc.ports J hJ
  unfold portMeaning
  cases hsrc : (c.circuit.ports.getD J default).source with
  | statement =>
    rw [hsrc] at hsize hl
    simp only [Source.limbs] at hsize hl ⊢
    have hpv : c.portValues c.ctx J = c.statementLimb := by simp only [portValues, hsrc]
    rw [hpv]
    have hst := hc.statement
    unfold statementOk at hst
    simp only [Bool.and_eq_true, beq_iff_eq] at hst
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    exact packBE_word hc G (fun i => c.publicSelf.getD i NONE) (c.pubW w) (8 * k) 8
      (by rw [pubW, decodePublic_length]; omega)
      (fun i hi j hj => public_bit hc hw (by omega) hj) (allBelow_spec hst.2 k hk)
  | root i =>
    rw [hsrc] at hsize hl
    simp only [Source.limbs] at hsize hl ⊢
    have hpv : c.portValues c.ctx J = c.rootLimbs.getD i #[] := by simp only [portValues, hsrc]
    rw [hpv]
    have hro := hc.roots
    unfold rootsOk at hro
    simp only [Bool.and_eq_true, beq_iff_eq] at hro
    have hi : i < r.rootsAt.length := by
      by_contra hcon
      have : c.rootLimbs.getD i #[] = #[] := by
        simp [Array.getD_eq_getD_getElem?, show c.rootLimbs.size ≤ i by omega]
      rw [hpv, this] at hsize; simp at hsize
    have hr := allBelow_spec hro.2 i hi
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hr
    obtain ⟨⟨_, hall⟩, hpk⟩ := hr
    apply List.map_congr_left
    intro l hlm
    rw [List.mem_range] at hlm
    set at_ := r.rootsAt.getD i 0
    have hfirst : [24, 16, 8, 0].getD l 0 + 8 ≤ 32 := by interval_cases l <;> decide
    have hall' : ∀ k < 8 * 32, (c.bitSelf.getD (8 * at_ + k) none).isSome := fun k hk => hall k hk
    obtain ⟨hb, hbits⟩ := read_bits hc hw (by norm_num) hall'
    apply packBE_word hc G c.streamBit (c.streamW r w) (at_ + [24, 16, 8, 0].getD l 0) 8
      (by rw [streamW_length]; omega) _ (allBelow_spec hpk l hlm)
    intro i' hi' j hj
    have := hbits ([24, 16, 8, 0].getD l 0 + i') (by omega) j hj
    rwa [show at_ + ([24, 16, 8, 0].getD l 0 + i') = at_ + [24, 16, 8, 0].getD l 0 + i' by ring] at this
  | element e =>
    rw [hsrc] at hsize hl
    simp only [Source.limbs] at hsize hl ⊢
    have hpv : c.portValues c.ctx J = c.limbsOf (c.elementNodes.getD e 0) := by simp only [portValues, hsrc]
    rw [hpv] at hsize ⊢
    have hso := allBelow_spec hc.sources J hJ
    simp only [hsrc, decide_eq_true_eq] at hso
    have hmem := (graphOk_parts hc.graph).2.2.1 (c.elementNodes.getD e 0) (by
      apply List.mem_append_right
      simpa [Array.getD_eq_getD_getElem?, hso] using Array.getElem_mem_toList hso)
    exact elem_port hc hw hmem.1 hmem.2 hsize
  | zero =>
    rw [hsrc] at hsize hl
    simp only [Source.limbs] at hsize hl ⊢
    have hpv : c.portValues c.ctx J = c.limbsOf (c.zeroNodes.getD (c.zeroIndex J) 0) := by simp only [portValues, hsrc]
    rw [hpv] at hsize ⊢
    have hso := allBelow_spec hc.sources J hJ
    simp only [hsrc, decide_eq_true_eq] at hso
    have hmem := (graphOk_parts hc.graph).2.2.1 (c.zeroNodes.getD (c.zeroIndex J) 0) (by
      apply List.mem_append_left
      simp [List.getD_eq_getElem?_getD, hso])
    exact elem_port hc hw hmem.1 hmem.2 hsize
  | pad =>
    rw [hsrc] at hsize hl
    simp only [Source.limbs] at hsize hl ⊢
    apply List.ext_getElem (by simp)
    intro l h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [Ctx.const_val G (hpad hsrc l h1)]
    interval_cases l <;> rfl

end Compiled

end RecCircuit
