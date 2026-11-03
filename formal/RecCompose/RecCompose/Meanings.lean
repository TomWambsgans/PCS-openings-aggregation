-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Facts
import RecCompose.Bridge
import RecCompose.Pi2Run

/-!
# The ports' and the calls' meaning, proved

For `pi2Facts hD C hchk` (`Facts.lean`): **`statementPortMeaning`**, **`zeroPortsMeaning`**, **`callWordsAgree`**. On a run
of π2's verifier that succeeds on the calldata, its public scalars are the statement's four words, π1's two roots' halves
at the stream's offsets `0`, `32`, and the `17` elements at `64 + 24 j` (`data_pi2Pubs`, `runWith_post`); `pubOfC` of
them is their limbs (`canon2` of a word or a half with no `Y²` limb is its two limbs). So the statement port carries the
input's words, a zero port zeros, and the words the circuit rebuilds from its ports (`callWordBytes`, on a witness
satisfying it at these limbs) are the contract's (`callWord`): a root port's four limbs rebuild the stream's 32 bytes
(`RecCircuit.root_bytes`), an element port's three the element (`limbsE_limbsL`), its pair point the contract's
(`pairPoint` the same map); the calls themselves are `Data.pi1Calls` (`viewCheck`), every port they name exists (the
checker's `wordOk`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Primitives

/-! ## π2's public scalars on the real circuit -/

theorem spec_reads_data : (Spec.of Data.circuit).reads = Data.reads := by
  unfold Spec.of
  rw [show Data.circuit.publicTerms = Data.publicTerms from rfl, data_zeroCoset]
  rfl

theorem data_pi2Pubs (input : List UInt8) (stream : Array UInt8) : pi2Pubs (Spec.of Data.circuit) input stream =
    UniStatement.publicWordsOf input ++ [halfAt stream 0, halfAt stream 16, halfAt stream 32, halfAt stream 48] ++
      (List.range 17).map fun j ↦ scalarAt stream (64 + 24 * j) := by
  unfold pi2Pubs
  rw [spec_reads_data]
  simp [Data.reads, foldReads, pubsStep, readValue, Read.bytes, List.range_succ]

theorem data_elementIndices : ∀ e < 17, (elementIndices Data.reads).getD e 0 = 8 + e := by decide +kernel

theorem data_rootsAt : rootsAt Data.reads = [0, 32, 472, 504] := by decide +kernel

theorem data_pi2Bytes : pi2Bytes (Spec.of Data.circuit) = 944 := by
  unfold pi2Bytes
  rw [spec_reads_data, show (Spec.of Data.circuit).logRow = 4 by
    unfold Spec.of
    rw [show Data.circuit.publicTerms = Data.publicTerms from rfl, data_zeroCoset]
    rfl]
  decide +kernel

/-- What `Data.pi1Calls`' words name: roots `0`, `1`; elements below `17`; pair coordinates `0`, `1`. -/
def dataWordOk : CallWord → Bool
  | .root i => decide (i < 2)
  | .element e => decide (e < 17)
  | .pair e co => decide (e < 17) && decide (co < 2)
  | .const _ => true

theorem data_words : ∀ ci < 3, ∀ k < (Data.pi1Calls.getD ci []).length,
    dataWordOk ((Data.pi1Calls.getD ci []).getD k default) = true := by decide +kernel

theorem data_calls_length : Data.pi1Calls.length = 3 := by decide +kernel

/-- **π2's run on the real circuit**: the stream's size, the public scalars. -/
theorem run_data {D : RecDeployment} (hD : D.Real) {roots : RecSetupRoots} {input : Vector UInt8 32}
    {stream : Array UInt8} {r : Reduced}
    (hr : (run (Spec.of (D.circuitAt roots.pi1).circuit) [] input.toList stream).result = .ok r) :
    stream.size = 944 ∧ r.scalars = pi2Pubs (Spec.of Data.circuit) input.toList stream ∧
      r.pairPoints = r.scalars.map pairPoint := by
  rw [show (D.circuitAt roots.pi1).circuit = Data.circuit from hD.1 _] at hr
  have h := holds_id (runWith_post (m := Id) (fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))
    (Spec.of Data.circuit) [] input.toList stream)
  obtain ⟨h1, h2, h3⟩ := h.1 r hr
  exact ⟨h1.trans data_pi2Bytes, h2, h3⟩

theorem pi2Scalars_of_ok {D : RecDeployment} {roots : RecSetupRoots} {input : Vector UInt8 32} {stream : Array UInt8}
    {r : Reduced} (hr : (run (Spec.of (D.circuitAt roots.pi1).circuit) [] input.toList stream).result = .ok r) :
    pi2Scalars D roots input stream = r.scalars := by
  unfold pi2Scalars
  rw [hr]

/-! ## Limbs of the scalars -/

theorem eNew_eq_ofF64 (a b : UInt64) :
    UniStatement.eNew a b 0 = F192.ofF64 (K.ofLane a) + F192.Y * F192.ofF64 (K.ofLane b) := by
  show F192.ofLimbs (K.ofLane a) (K.ofLane b) (K.ofLane 0) = _
  rw [F192.ofLimbs_eq, show K.ofLane 0 = 0 from rfl, F192.ofF64_zero]
  ring

theorem canon2_halfAt (d : Array UInt8) (cur : ℕ) :
    canon2 (halfAt d cur) = [F192.ofF64 (K.ofLane (UniStatement.beWordAt (d.extract cur (cur + 16)) 8)),
      F192.ofF64 (K.ofLane (UniStatement.beWordAt (d.extract cur (cur + 16)) 0))] := by
  unfold halfAt
  rw [eNew_eq_ofF64, canon2_ofF64]

theorem canon2_word (a b : UInt64) :
    canon2 (UniStatement.eK a + F192.Y * UniStatement.eK b) = [F192.ofF64 (K.ofLane a), F192.ofF64 (K.ofLane b)] := by
  have h : ∀ w : UInt64, UniStatement.eK w = F192.ofF64 (K.ofLane w) := fun w ↦ by
    rw [UniStatement.eK, eNew_eq_ofF64, show K.ofLane 0 = 0 from rfl, F192.ofF64_zero, mul_zero, add_zero]
  rw [h, h, canon2_ofF64]

/-! ## The statement port, the zero ports -/

section Meanings

variable {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)

include hchk in
/-- A port's source from `Data`'s public term. -/
theorem source_of_term (roots : RecSetupRoots) {j : ℕ} (hj : j < 36) :
    Data.publicTerms.getD j default = ⟨2 ^ 24 + j,
      ⟨termOf 2 ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.getD j default).source, none⟩⟩ := by
  obtain ⟨hview, -, -⟩ := viewChecked_at C hchk roots
  rw [← viewOf_terms hview, publicTermsOf_getD _ (by rw [viewOf_ports hview]; exact hj), viewOf_logN hview,
    viewOf_roots hview]

include hchk in
theorem statement_source (roots : RecSetupRoots) :
    ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.getD 32 default).source = .statement := by
  have h := source_of_term C hchk roots (j := 32) (by norm_num)
  have hd : Data.publicTerms.getD 32 default = ⟨16777248, ⟨[(⟨1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0⟩, 1), (⟨1, 0, 0, 1⟩, 2),
      (⟨0, 1, 0, 1⟩, 3)], none⟩⟩ := by decide +kernel
  rw [hd] at h
  have ht := congrArg (fun t : PublicTerm ↦ t.value.terms.length) h
  cases hs : ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.getD 32 default).source <;>
    simp_all [termOf]

include hD in
/-- **The statement port's public limbs are the calldata's four words.** -/
theorem statementPortMeaning : StatementPortMeaning D C (pi2Facts hD C hchk) := by
  intro roots input stream r hr
  obtain ⟨hview, -, -⟩ := viewChecked_at C hchk roots
  refine ⟨32, by rw [viewOf_ports hview]; norm_num, statement_source C hchk roots, ?_⟩
  show pubOfC (C.compiled (D.pi1IvAt roots.pi1)).circuit (pi2Scalars D roots input stream) 32 = _
  unfold pubOfC
  rw [statement_source C hchk roots, pi2Scalars_of_ok hr, (run_data hD hr).2.1, data_pi2Pubs]
  have e : ∀ k < 4, (UniStatement.publicWordsOf input.toList ++
      [halfAt stream 0, halfAt stream 16, halfAt stream 32, halfAt stream 48] ++
      (List.range 17).map (fun j ↦ scalarAt stream (64 + 24 * j))).getD k 0 =
        UniStatement.eK (UniStatement.beWordAt input.toList.toArray (8 * k)) := by
    intro k hk
    interval_cases k <;> rfl
  simp only [pubOfSource]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), canon2_word, canon2_word]
  rfl

include hD in
/-- **A zero port's public limbs are zero.** -/
theorem zeroPortsMeaning : ZeroPortsMeaning D C (pi2Facts hD C hchk) := by
  intro roots input stream J _ hz
  show pubOfC (C.compiled (D.pi1IvAt roots.pi1)).circuit (pi2Scalars D roots input stream) J = _
  unfold pubOfC
  rw [hz]
  rfl

end Meanings

/-! ## The calls -/

/-- **The checker's calls**: a root, element or pair word names a port that exists. -/
theorem wordOk_ports {c : RecCircuit.Compiled} {r : RecCircuit.Recorded} {k : ℕ} {cw : RecCircuit.CallWord}
    {gw : RecCircuit.Word} (h : c.wordOk r k cw gw = true) :
    (∀ i, cw = .root i → (c.circuit.portOf (.root i)).isSome) ∧
      (∀ e, cw = .element e → (c.circuit.portOf (.element e)).isSome) ∧
      (∀ e co, cw = .pair e co → (c.circuit.portOf (.element e)).isSome) := by
  cases cw <;> cases gw <;> simp_all [RecCircuit.Compiled.wordOk]

theorem callsOk_spec {c : RecCircuit.Compiled} {r : RecCircuit.Recorded} (h : c.callsOk r = true) :
    ∀ ci < c.circuit.calls.length, ∀ k < (c.circuit.calls.getD ci []).length,
      ∃ gw, c.wordOk r k ((c.circuit.calls.getD ci []).getD k default) gw = true := by
  unfold RecCircuit.Compiled.callsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hl, ha⟩ := h
  intro ci hci k hk
  have h1 := RecCircuit.allBelow_spec ha ci (hl ▸ hci)
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨_, RecCircuit.allBelow_spec h1.2 k (h1.1 ▸ hk)⟩

theorem slice_extract (d : Array UInt8) {a b k n : ℕ} (h : a + k + n ≤ b) :
    RecCircuit.slice (d.extract a b).toList k n = RecCircuit.slice d.toList (a + k) n := by
  unfold RecCircuit.slice
  rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_take, List.take_take, List.drop_drop,
    Nat.min_eq_left (by omega)]

theorem getD_map_pairPoint (l : List E) (n : ℕ) : (l.map pairPoint).getD n (0, 0) = pairPoint (l.getD n 0) := by
  rw [show ((0 : E), (0 : E)) = pairPoint 0 by simp [pairPoint], List.getD_map]

theorem length_elementWord (x : E) : (UniStatement.elementWord x).length = 32 := by
  simp [UniStatement.elementWord, UniStatement.be64]

theorem length_streamWord (stream : Array UInt8) {at' : ℕ} (h : at' + 32 ≤ stream.size) :
    (streamWord stream at').length = 32 := by
  simp [streamWord]
  omega

section Calls

variable {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)

include hD in
/-- **The circuit rebuilds the contract's π1 call words.** -/
theorem callWordsAgree : CallWordsAgree D C (pi2Facts hD C hchk) := by
  intro roots input stream w r hw hr
  obtain ⟨hview, hcallsv, -⟩ := viewChecked_at C hchk roots
  have hc := C.compile_ok (D.pi1IvAt roots.pi1)
  have hck := RecCircuit.Compiled.checked_of_compile hc
  have hcallsD : D.pi1Calls = callsOf (C.compiled (D.pi1IvAt roots.pi1)).circuit := hD.2.1.trans hcallsv.symm
  obtain ⟨hsize, hsc, hpp⟩ := run_data hD hr
  have hreads : (D.circuitAt roots.pi1).circuit.reads = Data.reads := by
    show (D.pi2 (D.pi1IvAt roots.pi1)).circuit.reads = _
    rw [hD.1]
    rfl
  have hroots := viewOf_roots hview
  have hs := hsc.trans (data_pi2Pubs input.toList stream)
  generalize hcd : C.compiled (D.pi1IvAt roots.pi1) = c at hw hview hcallsv hc hck hcallsD hroots
  have hP : ∀ J < c.circuit.ports.size, (c.circuit.portLimbs w J).map F192.ofF64 = pubOfC c.circuit r.scalars J := by
    intro J hJ
    rw [← pi2Scalars_of_ok hr]
    have h1 := limbVals_toPiop hc hJ w
    have h2 := hw.ports J (by simpa [RecPiop.Circuit.nP, RecCircuit.Circuit.toPiop] using hJ)
    rw [h1] at h2
    have : pubAt D C (pi2Facts hD C hchk) roots input stream J = pubOfC c.circuit (pi2Scalars D roots input stream) J := by
      show pubOfC (C.compiled (D.pi1IvAt roots.pi1)).circuit _ J = _
      rw [hcd]
    rw [← this]
    exact h2
  rw [hreads, hcallsD]
  have hlen : (callsOf c.circuit).length = c.circuit.calls.length := by simp [callsOf]
  refine ⟨hlen.symm, fun ci hci ↦ ?_⟩
  have hci' : ci < c.circuit.calls.length := hlen ▸ hci
  have hgetci : (callsOf c.circuit).getD ci [] = (c.circuit.calls.getD ci []).map callOf := by
    rw [List.getD_eq_getElem _ _ hci, List.getD_eq_getElem _ _ hci']
    simp [callsOf]
  refine ⟨by rw [hgetci, List.length_map], fun k hk ↦ ?_⟩
  rw [hgetci, List.length_map] at hk
  have hgetk : ((c.circuit.calls.getD ci []).map callOf).getD k default =
      callOf ((c.circuit.calls.getD ci []).getD k default) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
  rw [hgetci, hgetk]
  have hci3 : ci < 3 := by rw [← data_calls_length, ← hcallsv, hlen]; exact hci'
  have hdw := data_words ci hci3 k (by rw [← hcallsv, hgetci, List.length_map]; exact hk)
  rw [← hcallsv, hgetci, hgetk] at hdw
  obtain ⟨gw, hwok⟩ := callsOk_spec hck.calls ci hci' k hk
  obtain ⟨hpr, hpe, hpp'⟩ := wordOk_ports hwok
  generalize (c.circuit.calls.getD ci []).getD k default = cw at hdw hpr hpe hpp' ⊢
  cases cw with
  | const x =>
    refine ⟨rfl, ?_⟩
    show (RecCircuit.wordBytes32 x).length = 32
    simp [RecCircuit.wordBytes32]
  | root i =>
    have hi : i < 2 := by simpa [dataWordOk, callOf] using hdw
    obtain ⟨J, hJs⟩ := Option.isSome_iff_exists.mp (hpr i rfl)
    obtain ⟨hJ, hsrc⟩ := RecCircuit.Compiled.portOf_spec hJs
    have hcur : 32 * i + 32 ≤ stream.size := by omega
    have hlimbs : c.circuit.portLimbs w J =
        [K.ofLane (UniStatement.beWordAt (stream.extract (32 * i + 16) (32 * i + 16 + 16)) 8),
          K.ofLane (UniStatement.beWordAt (stream.extract (32 * i + 16) (32 * i + 16 + 16)) 0),
          K.ofLane (UniStatement.beWordAt (stream.extract (32 * i) (32 * i + 16)) 8),
          K.ofLane (UniStatement.beWordAt (stream.extract (32 * i) (32 * i + 16)) 0)] := by
      refine map_ofF64_inj ((hP J hJ).trans ?_)
      unfold pubOfC
      rw [hsrc, hroots]
      have e1 : r.scalars.getD (4 + 2 * i + 1) 0 = halfAt stream (32 * i + 16) := by
        rw [hs]; interval_cases i <;> rfl
      have e0 : r.scalars.getD (4 + 2 * i) 0 = halfAt stream (32 * i) := by
        rw [hs]; interval_cases i <;> rfl
      simp only [pubOfSource]
      rw [e1, e0, canon2_halfAt, canon2_halfAt]
      rfl
    have hraw := length_streamWord stream hcur
    have hrt : (rootsAt Data.reads).getD i 0 = 32 * i := by rw [data_rootsAt]; interval_cases i <;> rfl
    show RecCircuit.Circuit.limbsBytes (c.circuit.portLimbs w ((c.circuit.portOf (.root i)).getD 0)) =
      streamWord stream ((rootsAt Data.reads).getD i 0) ∧ (streamWord stream ((rootsAt Data.reads).getD i 0)).length = 32
    rw [hJs, Option.getD_some, hrt]
    refine ⟨?_, hraw⟩
    rw [← RecCircuit.root_bytes _ hraw, hlimbs]
    have hsz : ∀ a, a + 16 ≤ stream.size → (stream.extract a (a + 16)).size = 16 := fun a ha ↦ by
      simp [Array.size_extract]; omega
    have bw : ∀ a j, a + 16 ≤ stream.size → j + 8 ≤ 16 → K.ofLane (UniStatement.beWordAt (stream.extract a (a + 16)) j) =
        F64.ofNat (RecCircuit.beNat (RecCircuit.slice stream.toList (a + j) 8)) := fun a j ha hj ↦ by
      rw [RecCircuit.beWordAt_eq _ _ (by rw [hsz a ha]; exact hj), slice_extract _ (by omega)]
    have sw : ∀ j, j + 8 ≤ 32 → RecCircuit.slice (streamWord stream (32 * i)) j 8 =
        RecCircuit.slice stream.toList (32 * i + j) 8 := fun j hj ↦ by
      unfold streamWord
      rw [slice_extract _ (by omega)]
    simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero]
    rw [bw _ 8 (by omega) (by norm_num), bw _ 0 (by omega) (by norm_num), bw _ 8 (by omega) (by norm_num),
      bw _ 0 (by omega) (by norm_num), sw 0 (by norm_num), sw 8 (by norm_num), sw 16 (by norm_num),
      sw 24 (by norm_num)]
  | element e =>
    have he : e < 17 := by simpa [dataWordOk, callOf] using hdw
    obtain ⟨J, hJs⟩ := Option.isSome_iff_exists.mp (hpe e rfl)
    obtain ⟨hJ, hsrc⟩ := RecCircuit.Compiled.portOf_spec hJs
    have hlimbs : c.circuit.portLimbs w J = RecCircuit.Compiled.limbsL (r.scalars.getD (8 + e) 0) := by
      refine map_ofF64_inj ((hP J hJ).trans ?_)
      unfold pubOfC
      rw [hsrc, hroots]
      simp only [pubOfSource, show 4 + 2 * 2 + e = 8 + e by omega]
      rfl
    show UniStatement.elementWord (RecCircuit.Circuit.limbsE (c.circuit.portLimbs w ((c.circuit.portOf
        (.element e)).getD 0))) = UniStatement.elementWord (r.scalars.getD ((elementIndices Data.reads).getD e 0) 0) ∧
      (UniStatement.elementWord (r.scalars.getD ((elementIndices Data.reads).getD e 0) 0)).length = 32
    rw [hJs, Option.getD_some, hlimbs, RecCircuit.limbsE_limbsL, data_elementIndices e he]
    exact ⟨rfl, length_elementWord _⟩
  | pair e co =>
    have he : e < 17 ∧ co < 2 := by simpa [dataWordOk, callOf] using hdw
    obtain ⟨J, hJs⟩ := Option.isSome_iff_exists.mp (hpp' e co rfl)
    obtain ⟨hJ, hsrc⟩ := RecCircuit.Compiled.portOf_spec hJs
    have hlimbs : c.circuit.portLimbs w J = RecCircuit.Compiled.limbsL (r.scalars.getD (8 + e) 0) := by
      refine map_ofF64_inj ((hP J hJ).trans ?_)
      unfold pubOfC
      rw [hsrc, hroots]
      simp only [pubOfSource, show 4 + 2 * 2 + e = 8 + e by omega]
      rfl
    show UniStatement.elementWord ((UniStatement.pairPoint (RecCircuit.Circuit.limbsE (c.circuit.portLimbs w
        ((c.circuit.portOf (.element e)).getD 0)))).getD co 0) =
        UniStatement.elementWord (if co = 0 then (r.pairPoints.getD ((elementIndices Data.reads).getD e 0) (0, 0)).1
          else (r.pairPoints.getD ((elementIndices Data.reads).getD e 0) (0, 0)).2) ∧
      (UniStatement.elementWord (if co = 0 then (r.pairPoints.getD ((elementIndices Data.reads).getD e 0) (0, 0)).1
          else (r.pairPoints.getD ((elementIndices Data.reads).getD e 0) (0, 0)).2)).length = 32
    rw [hJs, Option.getD_some, hlimbs, RecCircuit.limbsE_limbsL, data_elementIndices e he.1, hpp, getD_map_pairPoint]
    refine ⟨?_, length_elementWord _⟩
    obtain ⟨-, hco⟩ := he
    interval_cases co <;> rfl

end Calls

end RecCompose
