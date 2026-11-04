-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The honest witness is the circuit compiler's
-- (`crates/leanvm_rec/src/circuit/layout.rs`'s `finish`, `RecCircuit.Compiled.witness`), the public values π2's prover
-- sends `prover.rs`'s (`public_values`: π1's roots' 32 bytes, the calls' elements).
import RecCompose.Pi2CompleteEnd
import RecCompose.Meanings
import RecCircuit.Complete

/-!
# The compiled circuit's completeness (`Pi2WitnessComplete`)

**`pi2WitnessComplete hD C hchk : Pi2WitnessComplete D C (pi2Facts hD C hchk)`**: on every stream π1-rec3's graph
accepts (its checks at Keccak-f[1600]), an honest witness and public values exist (`Pi2Good`):

* the witness `RecCircuit.Compiled.witness` (the honest words at their pulls, `RecCircuit/Complete.lean`): it satisfies
  the copy constraints (`witness_copy`) and holds the stream (`streamW_witness`, so `D.pi1Stream w = s`);
* the public values `valuesOf`: each root's 32 bytes of the stream, each element port's value (the circuit's own:
  `valsW` of the calls' element node), as the reads (`Data.reads`: two roots, then the scalars) take them;
* the ports' limbs are the public limbs (`pubOfC`): the statement's the public input's words (`pubW_witness`), a root's
  the stream's words, an element's its value's, a zero port's `0` (π1's zero checks, in `RecGraph`'s semantics on the
  stream, are zero: the graph's checks, `zero_port_sat`), a padding port's `0`.

Generic in the graph: only `compile_ok`, the checker's completeness checks and the view (`viewOf_reads`) are used.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2W

open RecStatement LeanVM.Parameters Primitives
open Pi2E

/-! ## `public_counts` bounds the ports' sources -/

theorem sourceCounts_mono (l : List RecCircuit.Port) (acc : ℕ × ℕ) :
    acc.1 ≤ (l.foldl (fun a p ↦ sourceCounts a p.source) acc).1 ∧
      acc.2 ≤ (l.foldl (fun a p ↦ sourceCounts a p.source) acc).2 := by
  induction l generalizing acc with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih (sourceCounts acc p.source)
    simp only [List.foldl_cons]
    cases hs : p.source <;> simp only [sourceCounts, hs] at h1 h2 ⊢ <;> omega

theorem wordCounts_mono (l : List RecCircuit.CallWord) (acc : ℕ × ℕ) :
    acc.1 ≤ (l.foldl wordCounts acc).1 ∧ acc.2 ≤ (l.foldl wordCounts acc).2 := by
  induction l generalizing acc with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih (wordCounts acc p)
    simp only [List.foldl_cons]
    cases p <;> simp only [wordCounts] at h1 h2 ⊢ <;> omega

theorem sourceCounts_mem (l : List RecCircuit.Port) (acc : ℕ × ℕ) (p : RecCircuit.Port) (hp : p ∈ l) :
    (∀ i, p.source = .root i → i < (l.foldl (fun a p ↦ sourceCounts a p.source) acc).1) ∧
      (∀ e, p.source = .element e → e < (l.foldl (fun a p ↦ sourceCounts a p.source) acc).2) := by
  induction l generalizing acc with
  | nil => cases hp
  | cons q l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · obtain ⟨h1, h2⟩ := sourceCounts_mono l (sourceCounts acc p.source)
      refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
      · rw [hi] at h1 ⊢; simp only [sourceCounts] at h1 ⊢
        exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right _ _)) h1
      · rw [he] at h2 ⊢; simp only [sourceCounts] at h2 ⊢
        exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self e) (le_max_right _ _)) h2
    · exact ih _ hp'

theorem publicCounts_port (c : RecCircuit.Circuit) {J : ℕ} (hJ : J < c.ports.size) :
    (∀ i, (c.ports.getD J default).source = .root i → i < (publicCounts c).1) ∧
      (∀ e, (c.ports.getD J default).source = .element e → e < (publicCounts c).2) := by
  have hmem : c.ports.getD J default ∈ c.ports.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hJ, Option.getD_some]
    exact Array.getElem_mem_toList hJ
  obtain ⟨h1, h2⟩ := sourceCounts_mem c.ports.toList (0, 0) _ hmem
  obtain ⟨m1, m2⟩ := wordCounts_mono c.calls.flatten (c.ports.toList.foldl (fun a p ↦ sourceCounts a p.source) (0, 0))
  exact ⟨fun i hi ↦ lt_of_lt_of_le (h1 i hi) m1, fun e he ↦ lt_of_lt_of_le (h2 e he) m2⟩

/-! ## The public values -/

/-- Root `i`'s 32 bytes of the stream. -/
def rootBytes (rootsAt : List ℕ) (s : Array UInt8) (i : ℕ) : List UInt8 :=
  (List.range 32).map fun k ↦ s.toList.getD (rootsAt.getD i 0 + k) 0

/-- **The public values π2's prover sends**: the roots' bytes, then the elements' values. -/
def valuesOf (nR nE : ℕ) (rootsAt : List ℕ) (s : Array UInt8) (elt : ℕ → E) : List PublicValue :=
  (List.range nR).map (fun i ↦ .root (rootBytes rootsAt s i)) ++ (List.range nE).map (fun e ↦ .scalar (elt e))

theorem length_pairs {α : Type} (n : ℕ) (f g : ℕ → α) :
    ((List.range n).flatMap fun i ↦ [f i, g i]).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring

theorem flatMap_pair_getD {α : Type} (f g : ℕ → α) (d : α) :
    ∀ n i, i < n → ((List.range n).flatMap fun k ↦ [f k, g k]).getD (2 * i) d = f i ∧
      ((List.range n).flatMap fun k ↦ [f k, g k]).getD (2 * i + 1) d = g i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    have hlen := length_pairs n f g
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge i n with h | h
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ih i h
    · have : i = n := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]
      simp

theorem scalars_valuesOf (nR nE : ℕ) (rootsAt : List ℕ) (s : Array UInt8) (elt : ℕ → E) :
    (valuesOf nR nE rootsAt s elt).flatMap PublicValue.scalars =
      ((List.range nR).flatMap fun i ↦ [(halvesOf (rootBytes rootsAt s i)).1, (halvesOf (rootBytes rootsAt s i)).2]) ++
        (List.range nE).map elt := by
  unfold valuesOf
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]
  congr 1
  induction nE with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.map_append]; rfl

theorem getD_pubs (input : List UInt8) (values : List PublicValue) (n : ℕ) :
    (publicScalarsOf input values).getD (4 + n) 0 = (values.flatMap PublicValue.scalars).getD n 0 := by
  unfold publicScalarsOf
  have h4 : (UniStatement.publicWordsOf input).length = 4 := by simp [UniStatement.publicWordsOf]
  rw [List.getD_append_right _ _ _ _ (by omega), h4, show 4 + n - 4 = n by omega]

theorem pubs_root (input : List UInt8) (nR nE : ℕ) (rootsAt : List ℕ) (s : Array UInt8) (elt : ℕ → E) {i : ℕ}
    (hi : i < nR) :
    (publicScalarsOf input (valuesOf nR nE rootsAt s elt)).getD (4 + 2 * i) 0 = (halvesOf (rootBytes rootsAt s i)).1 ∧
      (publicScalarsOf input (valuesOf nR nE rootsAt s elt)).getD (4 + 2 * i + 1) 0 =
        (halvesOf (rootBytes rootsAt s i)).2 := by
  have hl := length_pairs nR (fun i ↦ (halvesOf (rootBytes rootsAt s i)).1) (fun i ↦ (halvesOf (rootBytes rootsAt s i)).2)
  rw [show 4 + 2 * i + 1 = 4 + (2 * i + 1) by ring, getD_pubs, getD_pubs, scalars_valuesOf,
    List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  exact flatMap_pair_getD _ _ 0 nR i hi

theorem pubs_elem (input : List UInt8) (nR nE : ℕ) (rootsAt : List ℕ) (s : Array UInt8) (elt : ℕ → E) {e : ℕ}
    (he : e < nE) : (publicScalarsOf input (valuesOf nR nE rootsAt s elt)).getD (4 + 2 * nR + e) 0 = elt e := by
  have hl := length_pairs nR (fun i ↦ (halvesOf (rootBytes rootsAt s i)).1) (fun i ↦ (halvesOf (rootBytes rootsAt s i)).2)
  rw [show 4 + 2 * nR + e = 4 + (2 * nR + e) by ring, getD_pubs, scalars_valuesOf,
    List.getD_append_right _ _ _ _ (by omega), hl, show 2 * nR + e - 2 * nR = e by omega,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]
  rfl

theorem pubs_statement (input : List UInt8) (values : List PublicValue) {k : ℕ} (hk : k < 4) :
    (publicScalarsOf input values).getD k 0 = UniStatement.eK (UniStatement.beWordAt input.toArray (8 * k)) := by
  unfold publicScalarsOf
  have h4 : (UniStatement.publicWordsOf input).length = 4 := by simp [UniStatement.publicWordsOf]
  rw [List.getD_append _ _ _ _ (by omega)]
  simp [UniStatement.publicWordsOf, List.getD_eq_getElem?_getD, hk]

theorem forall₂_replicate_map {α β : Type} (R : α → β → Prop) (a : α) (f : ℕ → β) (h : ∀ i, R a (f i)) :
    ∀ n, List.Forall₂ R (List.replicate n a) ((List.range n).map f) := by
  intro n
  induction n with
  | zero => exact List.Forall₂.nil
  | succ n ih =>
    rw [List.replicate_succ', List.range_succ, List.map_append]
    exact List.rel_append ih (List.Forall₂.cons (h n) List.Forall₂.nil)

/-! ## The words of 32 bytes -/

theorem getD_rootBytes (rootsAt : List ℕ) (s : Array UInt8) (i j : ℕ) (hj : j < 32) :
    (rootBytes rootsAt s i).toArray.getD j 0 = s.getD (rootsAt.getD i 0 + j) 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  simp only [rootBytes, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some,
    List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem beWordAt_rootBytes (rootsAt : List ℕ) (s : Array UInt8) (i off : ℕ) (hoff : off + 8 ≤ 32) :
    UniStatement.beWordAt (rootBytes rootsAt s i).toArray off =
      UniStatement.beWordAt s (rootsAt.getD i 0 + off) := by
  unfold UniStatement.beWordAt
  apply List.foldl_ext
  intro acc k hk
  rw [List.mem_range] at hk
  rw [getD_rootBytes _ _ _ _ (by omega), add_assoc]


/-! ## The witness's completeness -/

theorem ofRG_streamLen (g : RecGraph.Graph) (rootsAt : List ℕ) (iv : List UInt8) :
    (RecCircuit.ofRG g rootsAt iv).graph.streamLen = g.streamLen := rfl

/-- **π1's zero checks are zero on a stream the graph accepts** (in `RecGraph`'s semantics over Keccak-f[1600]). -/
theorem zeros_of_checks {g : RecGraph.Graph} {iv : List UInt8} {input : Vector UInt8 32} {s : Array UInt8}
    {out : RecGraph.Outputs} (hev : RecGraph.evalGraphDeployed g iv input.toList s = some out)
    (h : out.zeros.all (· == 0) = true) :
    s.size = g.streamLen ∧ ∀ id ∈ g.zero, RecGraph.valE (RecCircuit.rgVals g iv input.toList s.toList) id = 0 := by
  unfold RecGraph.evalGraphDeployed RecGraph.evalGraph at hev
  by_cases hsz : s.size = g.streamLen
  · simp only [hsz, ↓reduceIte] at hev
    refine ⟨hsz, fun id hid ↦ ?_⟩
    have e : RecCircuit.rgVals g iv input.toList s.toList =
        Id.run (RecGraph.evalNodes (m := Id) (fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) g iv input.toList s) := by
      unfold RecCircuit.rgVals; rw [Array.toArray_toList]; rfl
    have hev' : some (RecGraph.outputsOf g s (RecCircuit.rgVals g iv input.toList s.toList)) = some out := by
      rw [e]; exact hev
    cases Option.some.inj hev'
    unfold RecGraph.outputsOf at h
    simp only [List.all_eq_true, List.mem_map, beq_iff_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h
    exact h id hid
  · simp only [hsz, ↓reduceIte] at hev
    cases hev

/-- **The compiled circuit is complete**: on every stream π1-rec3's graph accepts, the honest witness and π2's public
values are an honest witness (`Pi2Good`). -/
theorem pi2WitnessComplete {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C) :
    Pi2WitnessComplete D C (pi2Facts hD C hchk) := by
  intro roots input s hgc
  have hc := C.compile_ok (D.pi1IvAt roots.pi1)
  have hck := RecCircuit.Compiled.checked_of_compile hc
  obtain ⟨hview, -, -⟩ := viewChecked_at C hchk roots
  set c := C.compiled (D.pi1IvAt roots.pi1) with hcdef
  set r := RecCircuit.ofRG RecGraph.Pi1.pi1Graph C.rootsAt (D.pi1IvAt roots.pi1) with hrdef
  unfold pi1GraphChecks at hgc
  split at hgc
  case h_2 => cases hgc
  rename_i out hev
  obtain ⟨hsz, hzero⟩ := zeros_of_checks hev ((Bool.and_eq_true _ _).mp hgc).1
  set w := c.witness input.toList s.toList with hw
  have hsat : c.circuit.Satisfied w := RecCircuit.Compiled.witness_satisfied hck
  have hpub : c.pubW w = input.toList := RecCircuit.Compiled.pubW_witness hck (by simp)
  have hstr : c.streamW r w = s.toList := RecCircuit.Compiled.streamW_witness hck
    (by rw [hrdef, ofRG_streamLen, Array.length_toList]; exact hsz)
  set nR := (publicCounts c.circuit).1
  set nE := (publicCounts c.circuit).2
  set elt : ℕ → E := fun e ↦ ((c.valsW r w).getD (c.elementNodes.getD e 0) default).toE
  refine ⟨(valuesOf nR nE C.rootsAt s elt, w), ?_, ⟨?_, ?_⟩, ?_⟩
  · -- the reads
    show List.Forall₂ Pi2S.ReadMatch (D.circuitAt roots.pi1).circuit.reads (valuesOf nR nE C.rootsAt s elt)
    rw [show (D.circuitAt roots.pi1).circuit = Data.circuit from hD.1 _, show Data.circuit.reads = Data.reads from rfl,
      ← viewOf_reads hview]
    exact List.rel_append (forall₂_replicate_map _ _ _ (fun i ↦ by simp [Pi2S.ReadMatch, rootBytes]) _)
      (forall₂_replicate_map _ _ _ (fun e ↦ by simp [Pi2S.ReadMatch]) _)
  · exact RecCircuit.Compiled.witness_copy hck
  · -- the ports
    intro J hJ'
    have hJ : J < c.circuit.ports.size := by simpa [RecPiop.Circuit.nP, RecCircuit.Circuit.toPiop] using hJ'
    obtain ⟨hcR, hcE⟩ := publicCounts_port c.circuit hJ
    show c.circuit.toPiop.limbVals (RecCircuit.emb w) J = pubOfC c.circuit _ J
    rw [limbVals_toPiop hc hJ w]
    unfold pubOfC
    cases hs : (c.circuit.ports.getD J default).source with
    | zero =>
      obtain ⟨hmem, hl⟩ := RecCircuit.Compiled.zero_port_sat hc hsat hJ hs
      rw [hl, hpub, hstr, hzero _ hmem]
      simp [RecCircuit.Compiled.limbsL, pubOfSource]
    | pad =>
      rw [RecCircuit.Compiled.ports_carry hck hsat J hJ, RecCircuit.Compiled.portMeaning, hs]
      simp [pubOfSource]
    | element e =>
      rw [RecCircuit.Compiled.ports_carry hck hsat J hJ, RecCircuit.Compiled.portMeaning, hs]
      simp only [pubOfSource]
      rw [pubs_elem _ _ _ _ _ _ (hcE e hs)]
      rfl
    | statement =>
      rw [RecCircuit.Compiled.ports_carry hck hsat J hJ, RecCircuit.Compiled.portMeaning, hs, hpub]
      simp only [pubOfSource]
      rw [pubs_statement _ _ (by norm_num), pubs_statement _ _ (by norm_num), pubs_statement _ _ (by norm_num),
        pubs_statement _ _ (by norm_num), canon2_word, canon2_word]
      have hb : ∀ k < 4, F64.ofNat (RecCircuit.beNat (RecCircuit.slice input.toList (8 * k) 8)) =
          K.ofLane (UniStatement.beWordAt input.toList.toArray (8 * k)) := fun k hk ↦ by
        rw [RecCircuit.beWordAt_eq _ _ (by simp; omega)]
      simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append]
      rw [hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num)]
    | root i =>
      rw [RecCircuit.Compiled.ports_carry hck hsat J hJ, RecCircuit.Compiled.portMeaning, hs, hstr]
      simp only [pubOfSource]
      obtain ⟨h0, h1⟩ := pubs_root input.toList nR nE C.rootsAt s elt (hcR i hs)
      rw [h1, h0]
      -- the root's bytes are in the stream
      have hat : C.rootsAt.getD i 0 + 32 ≤ s.size := by
        obtain ⟨-, -, hsize, -, -⟩ := RecCircuit.Compiled.portsOk_parts hck.ports J hJ
        rw [hs] at hsize
        simp only [RecCircuit.Compiled.portValues, hs, RecCircuit.Source.limbs] at hsize
        have hro := hck.roots
        unfold RecCircuit.Compiled.rootsOk at hro
        simp only [Bool.and_eq_true, beq_iff_eq] at hro
        have hi : i < C.rootsAt.length := by
          show i < r.rootsAt.length
          rw [← hro.1]
          by_contra hn
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hsize
          simp at hsize
        have hb := RecCircuit.allBelow_spec hro.2 i hi
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hb
        have h255 := hb.1.2 255 (by norm_num)
        have hbs : 8 * r.rootsAt.getD i 0 + 255 < c.bitSelf.size := by
          by_contra hn
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h255
          simp at h255
        rw [hck.sizes.2.2.2.1, show r.rootsAt = C.rootsAt from rfl] at hbs
        have : r.graph.streamLen = s.size := by rw [hrdef, ofRG_streamLen]; exact hsz.symm
        rw [this] at hbs
        omega
      have hw' : ∀ off, off + 8 ≤ 32 →
          K.ofLane (UniStatement.beWordAt (rootBytes C.rootsAt s i).toArray off) =
            F64.ofNat (RecCircuit.beNat (RecCircuit.slice s.toList (C.rootsAt.getD i 0 + off) 8)) := by
        intro off hoff
        rw [beWordAt_rootBytes _ _ _ _ hoff, RecCircuit.beWordAt_eq _ _ (by omega)]
      simp only [halvesOf, eNew_eq_ofF64, canon2_ofF64]
      rw [hw' 24 (by norm_num), hw' 16 (by norm_num), hw' 8 (by norm_num), hw' 0 (by norm_num)]
      simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
        add_zero]
      rfl
  · -- the stream
    show D.pi1Stream w = s
    rw [C.stream_eq, hstr, Array.toArray_toList]

end RecCompose.Pi2W

/-- info: 'RecCompose.Pi2W.pi2WitnessComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2W.pi2WitnessComplete
