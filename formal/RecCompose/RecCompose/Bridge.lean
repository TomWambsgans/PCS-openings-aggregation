-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Circuit
import RecCompose.Layers
import RecCompose.CallsPure
import RecCompose.OpeningsAgree
import RecCompose.End

/-!
# `CircuitBridge`, proved from the ports' and the calls' meaning

`circuitBridge`: RecCircuit's end statement (`EndStatement`, `pi1rec3_end`) at π2's public limbs of the calldata gives
RecStatement's `Pi1GraphAccepts` with the contract's π1 openings (`pi1OpsOf`). The proof:

* the ports' limbs are the public limbs (`Satisfies.ports`, `limbVals_toPiop`);
* **the public input**: the statement port's limbs are the calldata's four words (`StatementPortMeaning`), so the
  witness's public input is the calldata's (`bytes_eq_of_words`);
* **the zero checks**: a zero port's public limbs are zero (`ZeroPortsMeaning`), so every zero check the circuit carries
  is zero; the zero ports carry every zero check whose image is not a constant (the checker's count,
  `exists_zero_port`); the others are zero by `EndStatement`; π1-rec3's emitted graph has no nonzero check;
* **the calls**: the circuit's rebuilt words are the contract's π1 call words (`CallWordsAgree`), and RecCircuit's
  `compile_sound_calls` makes them the graph's words, word 0 as `pcsWord` of it; so the contract's decoding of each call
  (`decodeWith`) and `decodePi1Call` of the graph's agree (`decode_agree`): the layouts and claims, and `C1`'s, `C2`'s
  roots as the stream carries them (`pi1RootWordOk`: with the root-word fix, branch `fix-pi1-root`, `pcsWord` keeps a
  stream root's word as it is).

The named facts (`StatementPortMeaning`, `ZeroPortsMeaning`, `CallWordsAgree`, `Pi1CallsLayouts`) are what the
compiler's ports and calls mean in the contract's terms: the runners establish them (RecCircuitTest's ports and calls
against the Rust, RecStatementTest's public terms and π1's calls' constants, `tests/pi2.rs`'s "π1's calls rebuilt from
π2's ports equal the vector's").
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash Primitives
open scoped ENNReal

set_option linter.unusedSectionVars false

/-! ## Bytes -/

theorem beNat_inj : ∀ (a b : List UInt8), a.length = b.length → RecCircuit.beNat a = RecCircuit.beNat b → a = b := by
  intro a
  induction a using List.reverseRecOn with
  | nil =>
    intro b hl _
    exact (List.length_eq_zero_iff.mp hl.symm).symm
  | append_singleton a x ih =>
    intro b hl he
    cases b using List.reverseRecOn with
    | nil => simp at hl
    | append_singleton b y =>
      rw [RecCircuit.beNat_append, RecCircuit.beNat_append] at he
      have h1 : (RecCircuit.beNat a * 256 + x.toNat) % 256 = (RecCircuit.beNat b * 256 + y.toNat) % 256 := by
        rw [he]
      rw [Nat.mul_add_mod_of_lt x.toNat_lt, Nat.mul_add_mod_of_lt y.toNat_lt] at h1
      have hxy : x = y := UInt8.toNat.inj h1
      subst hxy
      have h2 : RecCircuit.beNat a = RecCircuit.beNat b :=
        Nat.eq_of_mul_eq_mul_right (by decide : 0 < 256) (Nat.add_right_cancel he)
      rw [ih b (by simpa using hl) h2]

/-- **Four big-endian words give their 32 bytes back.** -/
theorem bytes_eq_of_words (a b : List UInt8) (ha : a.length = 32) (hb : b.length = 32)
    (h : ∀ k < 4, K.ofLane (UniStatement.beWordAt a.toArray (8 * k)) =
      K.ofLane (UniStatement.beWordAt b.toArray (8 * k))) : a = b := by
  have hs : ∀ k < 4, RecCircuit.slice a (8 * k) 8 = RecCircuit.slice b (8 * k) 8 := by
    intro k hk
    have e := h k hk
    rw [RecCircuit.beWordAt_eq _ _ (by rw [List.size_toArray, ha]; omega),
      RecCircuit.beWordAt_eq _ _ (by rw [List.size_toArray, hb]; omega)] at e
    have e2 := congrArg K.lane e
    rw [← RecCircuit.ofLane_ofNat, ← RecCircuit.ofLane_ofNat, RecCircuit.lane_ofLane, RecCircuit.lane_ofLane] at e2
    have la : (RecCircuit.slice a (8 * k) 8).length = 8 := RecCircuit.slice_length _ _ _ (by rw [ha]; omega)
    have lb : (RecCircuit.slice b (8 * k) 8).length = 8 := RecCircuit.slice_length _ _ _ (by rw [hb]; omega)
    have hla := RecCircuit.beNat_lt (RecCircuit.slice a (8 * k) 8)
    have hlb := RecCircuit.beNat_lt (RecCircuit.slice b (8 * k) 8)
    rw [la] at hla
    rw [lb] at hlb
    have e3 := congrArg UInt64.toNat e2
    rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hla, Nat.mod_eq_of_lt hlb] at e3
    exact beNat_inj _ _ (by rw [la, lb]) e3
  apply List.ext_getElem (by rw [ha, hb])
  intro i hi1 hi2
  have hk : i / 8 < 4 := by rw [ha] at hi1; omega
  have e := congrArg (fun l ↦ l.getD (i % 8) 0) (hs (i / 8) hk)
  rw [RecCircuit.slice_getD _ _ _ _ (Nat.mod_lt _ (by norm_num)),
    RecCircuit.slice_getD _ _ _ _ (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod] at e
  rwa [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at e

/-! ## The ports -/

/-- **A port's limbs in `RecPiop`'s relation are the circuit's port limbs.** -/
theorem limbVals_toPiop {r : RecCircuit.Recorded} {c : RecCircuit.Compiled} (hc : RecCircuit.compile r = .ok c)
    {J : ℕ} (hJ : J < c.circuit.ports.size) (w : ℕ → K) :
    c.circuit.toPiop.limbVals (RecCircuit.emb w) J = (c.circuit.portLimbs w J).map F192.ofF64 := by
  have hck := RecCircuit.Compiled.checked_of_compile hc
  have hparts := RecCircuit.Compiled.portsOk_parts hck.ports J hJ
  dsimp only at hparts
  have hnP : J < c.circuit.toPiop.nP := by simpa [RecPiop.Circuit.nP, RecCircuit.Circuit.toPiop] using hJ
  have hport : c.circuit.toPiop.port J = (c.circuit.ports.getD J default).position := by
    simp only [RecPiop.Circuit.port, RecCircuit.Circuit.toPiop, List.getD_eq_getElem?_getD,
      Array.getD_eq_getD_getElem?, List.getElem?_map, Array.getElem?_toList]
    rw [Array.getElem?_eq_getElem hJ]
    rfl
  have hW : c.circuit.toPiop.W = c.circuit.width := rfl
  unfold RecPiop.Circuit.limbVals RecCircuit.Circuit.portLimbs
  dsimp only
  rw [limbs_toPiop hc hnP, hport, hparts.2.1]
  rcases source_limbs (c.circuit.ports.getD J default).source with h | h <;> rw [h] <;>
    simp [RecCircuit.portWeights, RecPiop.Circuit.base, hW, RecCircuit.Circuit.cells, RecCircuit.emb,
      List.range_succ, mul_comm]

/-! ## The zero ports -/

/-- The `m`-th entry satisfying `p` has `m` entries satisfying `p` before it. -/
theorem exists_nth_filter {α : Type} [Inhabited α] (p : α → Bool) :
    ∀ (l : List α) (m : ℕ), m < (l.filter p).length →
      ∃ J < l.length, p (l.getD J default) = true ∧ ((l.take J).filter p).length = m
  | [], m, h => by simp at h
  | a :: l, m, h => by
    by_cases ha : p a = true
    · cases m with
      | zero => exact ⟨0, by simp, by simpa using ha, by simp⟩
      | succ m =>
        rw [List.filter_cons_of_pos ha, List.length_cons] at h
        obtain ⟨J, hJ, hp, hc⟩ := exists_nth_filter p l m (by omega)
        refine ⟨J + 1, by simpa using hJ, by simpa using hp, ?_⟩
        rw [List.take_succ_cons, List.filter_cons_of_pos ha, List.length_cons, hc]
    · rw [List.filter_cons_of_neg ha] at h
      obtain ⟨J, hJ, hp, hc⟩ := exists_nth_filter p l m h
      refine ⟨J + 1, by simpa using hJ, by simpa using hp, ?_⟩
      rw [List.take_succ_cons, List.filter_cons_of_neg ha, hc]


/-! ## The calls' decodings -/

/-- `claimsOfWords` reads the words after the first. -/
theorem claimsOfWords_congr {ws ws' : List (List UInt8)} (h : ∀ i, ws.getD (i + 1) [] = ws'.getD (i + 1) [])
    (k v : ℕ) : claimsOfWords ws k v = claimsOfWords ws' k v := by
  have hg : ∀ c j, ws.getD (3 + c * (v + 1) + j) [] = ws'.getD (3 + c * (v + 1) + j) [] := fun c j ↦ by
    have := h (2 + c * (v + 1) + j)
    rwa [show 2 + c * (v + 1) + j + 1 = 3 + c * (v + 1) + j by omega] at this
  unfold claimsOfWords
  simp only [hg]

/-- **The contract's decoding of a call and `decodePi1Call` of the graph's agree**: words of 32 bytes (the graph's),
the contract's the same but for word 0 (`r0`), word 1 registered with π1's opener at its variables. -/
theorem decode_agree (reg : List (List UInt8 × Opener)) (w0 w1 w2 : List UInt8) (ws : List (List UInt8))
    (r0 : List UInt8) (hws : ∀ x ∈ w0 :: w1 :: w2 :: ws, x.length = 32)
    (hlook : reg.lookup w1 = some (.pi1 (UniStatement.layoutWordVars w1)))
    (x : Digest × Opener × List PcsQuotient.Claim) (hx : decodeWith reg (r0 :: w1 :: w2 :: ws) = some x) :
    decodePi1Call (w0 :: w1 :: w2 :: ws).flatten =
        some ((if Pi1Decode.codeOf w1 = 0x5503 then UniStatement.digestOfBytes32 w0 else rootOfWord w0), w1, x.2.2) ∧
      x.1 = rootOfWord r0 := by
  have hcl := claimsOfWords_congr (ws := r0 :: w1 :: w2 :: ws) (ws' := w0 :: w1 :: w2 :: ws) (fun i ↦ rfl)
  unfold decodeWith at hx
  simp only [List.head?_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_eq_bind,
    Option.bind_some, hlook, Opener.vars] at hx
  cases hk : countOfWord w2 with
  | none => simp [hk] at hx
  | some k =>
    simp only [hk, Option.bind_some] at hx
    split at hx
    · exact absurd hx (by simp)
    · rename_i hguard0
      have hguard : 1 ≤ k ∧ (r0 :: w1 :: w2 :: ws).length = 3 + k * (UniStatement.layoutWordVars w1 + 1) ∧
          r0.length = 32 := Classical.byContradiction fun hn ↦ hguard0 (by
            rw [Bool.not_eq_true']; exact decide_eq_false hn)
      cases hc : claimsOfWords (r0 :: w1 :: w2 :: ws) k (UniStatement.layoutWordVars w1) with
      | none => simp [hc] at hx
      | some cl =>
        simp only [hc, Option.bind_some, Option.pure_def, Option.some.injEq] at hx
        subst hx
        refine ⟨?_, rfl⟩
        have hlen := Pi1Decode.length_flatten_32 _ hws
        have hch := Pi1Decode.chunks_flatten _ hws
        unfold decodePi1Call
        rw [ite_eq_right (by rw [hlen]; omega)]
        simp only [hch, List.head?_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_eq_bind,
          Option.bind_some, hk]
        rw [ite_eq_right (by
          rw [Bool.not_eq_true', decide_eq_false_iff_not, not_not]
          exact ⟨hguard.1, by simpa using hguard.2.1⟩)]
        rw [← hcl, hc]
        rfl


/-- A call's decoded root: `decodePi1Call`'s, the setup's (code `0x5503`) as its hash, the others as root words. -/
def digOf (ws : List (List UInt8)) : Digest :=
  if Pi1Decode.codeOf (ws.getD 1 []) = 0x5503 then UniStatement.digestOfBytes32 (ws.getD 0 []) else rootOfWord (ws.getD 0 [])

/-- **One call**: the graph's words `gws` (32 bytes each) and the contract's `cws`, equal but for word 0, word 1
registered with π1's opener: the contract's decoding and `decodePi1Call` of the graph's agree. -/
theorem per_call (reg : List (List UInt8 × Opener)) (gws cws : List (List UInt8)) (hlen : cws.length = gws.length)
    (htail : ∀ k, 1 ≤ k → k < gws.length → cws.getD k [] = gws.getD k []) (hgl : ∀ x ∈ gws, x.length = 32)
    (hlook : reg.lookup (gws.getD 1 []) = some (.pi1 (UniStatement.layoutWordVars (gws.getD 1 []))))
    (x : Digest × Opener × List PcsQuotient.Claim) (hx : decodeWith reg cws = some x) :
    decodePi1Call gws.flatten = some (digOf gws, gws.getD 1 [], x.2.2) ∧ x.1 = rootOfWord (cws.getD 0 []) := by
  match cws, gws, hlen with
  | [], _, _ => simp [decodeWith] at hx
  | [_], _, _ => simp [decodeWith] at hx
  | [_, _], _, _ => simp [decodeWith] at hx
  | c0 :: c1 :: c2 :: cr, g0 :: g1 :: g2 :: gr, hlen =>
    have hcr : cr = gr := by
      apply List.ext_getElem (by simpa using hlen)
      intro i h1 h2
      have := htail (i + 3) (by omega) (by simp; omega)
      simpa [List.getD_eq_getElem?_getD, h1, h2] using this
    have h1 : c1 = g1 := by simpa using htail 1 le_rfl (by simp)
    have h2 : c2 = g2 := by simpa using htail 2 (by norm_num) (by simp)
    subst hcr h1 h2
    have hd := decode_agree reg g0 c1 c2 cr c0 hgl (by simpa using hlook) x hx
    exact ⟨by rw [hd.1]; rfl, hd.2⟩

/-! ## The named facts -/

section Facts

variable (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)

/-- π2's public limbs of the calldata, at the setup's roots. -/
abbrev pubAt (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) : ℕ → List E :=
  Fa.pubOf roots (pi2Scalars D roots input stream)

/-- **The statement port's public limbs are the calldata's four words**, on a stream π2's verifier reads (the verifier's
statement term, `SpecOf.term_value`, at the compiler's statement port; proved for `pi2Facts`:
`RecCompose.statementPortMeaning`). (Composition, `lean-pi2-facts`: on a stream the run rejects, π2's scalars are empty,
`pi2Scalars`, so no public limbs are the input's words there; the bridge reads it on accepted runs only.) -/
def StatementPortMeaning : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) (r : Reduced),
    (run (Spec.of (D.circuitAt roots.pi1).circuit) [] input.toList stream).result = .ok r →
    ∃ J < (C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.size,
      ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.getD J default).source = .statement ∧
      pubAt D C Fa roots input stream J =
        ((List.range 4).map fun k ↦ K.ofLane (UniStatement.beWordAt input.toList.toArray (8 * k))).map F192.ofF64

/-- **A zero port's public limbs are zero** (the zero coset, `SpecOf.zero_ports`, at the compiler's zero ports). -/
def ZeroPortsMeaning : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8),
    ∀ J < (C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.size,
      ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.getD J default).source = .zero →
        pubAt D C Fa roots input stream J = [0, 0, 0]

/-- **The circuit rebuilds the contract's π1 call words**: on a witness satisfying the circuit at the calldata's
public limbs, and π2's run over Keccak-f[1600] on the calldata (`pi1OpsOf`'s), the circuit's calls are `D.pi1Calls`
word for word: each word the circuit rebuilds from its ports (`callWordBytes`) is RecStatement's `callWord` of the
contract's (the stream's root words, the claims' elements, their pair points, the constants), 32 bytes
(`tests/pi2.rs`: "π1's calls rebuilt from π2's ports equal the vector's"; RecStatementTest: the contract's words). -/
def CallWordsAgree : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) (w : ℕ → K) (r : Reduced),
    ((C.compiled (D.pi1IvAt roots.pi1)).circuit.toPiop).Satisfies (pubAt D C Fa roots input stream)
      (RecCircuit.emb w) →
    (run (Spec.of (D.circuitAt roots.pi1).circuit) [] input.toList stream).result = .ok r →
      (C.compiled (D.pi1IvAt roots.pi1)).circuit.calls.length = D.pi1Calls.length ∧
      ∀ ci < D.pi1Calls.length,
        ((C.compiled (D.pi1IvAt roots.pi1)).circuit.calls.getD ci []).length = (D.pi1Calls.getD ci []).length ∧
        ∀ k < (D.pi1Calls.getD ci []).length,
          (C.compiled (D.pi1IvAt roots.pi1)).circuit.callWordBytes w
              (((C.compiled (D.pi1IvAt roots.pi1)).circuit.calls.getD ci []).getD k default) =
            callWord (D.circuitAt roots.pi1).circuit.reads stream r ((D.pi1Calls.getD ci []).getD k default) ∧
          (callWord (D.circuitAt roots.pi1).circuit.reads stream r ((D.pi1Calls.getD ci []).getD k default)).length =
            32

/-- **π1's calls' layout words are π1-rec3's** (RecStatementTest: π1's calls' constants, the reference layout words). -/
def Pi1CallsLayouts : Prop :=
  ∀ ci < 3, (D.pi1Calls.getD ci []).getD 1 default = .const (w1 ci)

end Facts

/-- `Data.pi1Calls`' heads: `C1`'s and `C2`'s roots, then the setup's constant root word. -/
theorem data_pi1Calls_shape : ∃ i ra j rb x rd, Data.pi1Calls = [.root i :: ra, .root j :: rb, .const x :: rd] :=
  ⟨_, _, _, _, _, _, rfl⟩


theorem pi1CallsWith_shape (i j : ℕ) (ra rb rd : List CallWord) (x : List UInt8) (f : Digest) :
    pi1CallsWith [.root i :: ra, .root j :: rb, .const x :: rd] f =
      [.root i :: ra, .root j :: rb, .const (rootWordOfBytes (digestBytes f)) :: rd] := rfl

theorem limbsL_zero : RecCircuit.Compiled.limbsL (0 : E) = [0, 0, 0] := by
  simp [RecCircuit.Compiled.limbsL]

theorem eq_zero_of_limbsL {x : E} (h : RecCircuit.Compiled.limbsL x = [0, 0, 0]) : x = 0 := by
  rw [← RecCircuit.limbsE_limbsL x, h, ← limbsL_zero, RecCircuit.limbsE_limbsL]

theorem map_ofF64_inj {a b : List K} (h : a.map F192.ofF64 = b.map F192.ofF64) : a = b :=
  List.map_injective_iff.mpr F192.ofF64_injective h

theorem length_wordBytes_le (s : Array UInt8) (vals : Array RecGraph.Value) (w : RecGraph.Word) :
    (RecGraph.wordBytes s vals w).length ≤ 32 := by
  cases w with
  | node id => simp [RecGraph.wordBytes]
  | const x => simp [RecGraph.wordBytes, RecGraph.beBytes32]
  | stream at_ => simp [RecGraph.wordBytes]

theorem length_rootWordBytes (b : List UInt8) : (RecCircuit.rootWordBytes b).length = b.length := by
  simp [RecCircuit.rootWordBytes]; omega

theorem pcsWord_ne_zero {k : ℕ} (hk : k ≠ 0) (wd : RecGraph.Word) (b : List UInt8) : RecCircuit.pcsWord k wd b = b := by
  cases wd <;> simp [RecCircuit.pcsWord, hk]

theorem length_pcsWord (k : ℕ) (wd : RecGraph.Word) (bs : List UInt8) :
    (RecCircuit.pcsWord k wd bs).length = bs.length := by
  cases wd with
  | const x => by_cases hk : k = 0 <;> simp [RecCircuit.pcsWord, hk, length_rootWordBytes]
  | node id => rfl
  | stream at_ => rfl

/-- `C1`'s and `C2`'s calls' word 0 in the emitted graph: the stream's root. -/
theorem emitted_root_words (k : ℕ) (hk : k < 2) :
    ∃ a, (RecGraph.Emitted.graph.calls.getD k []).getD 0 default = .stream a := by
  interval_cases k <;> exact ⟨_, rfl⟩

theorem getD_map_of_lt {α β : Type} (f : α → β) (l : List α) {k : ℕ} (hk : k < l.length) (d : β) (d' : α) :
    (l.map f).getD k d = f (l.getD k d') := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem ofRG_streamLen (g : RecGraph.Graph) (rootsAt : List ℕ) (iv : List UInt8) :
    (RecCircuit.ofRG g rootsAt iv).graph.streamLen = g.streamLen := rfl

theorem rgVals_eq (g : RecGraph.Graph) (iv pub stream : List UInt8) :
    RecCircuit.rgVals g iv pub stream =
      Id.run (RecGraph.evalNodes (m := Id) (fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) g iv pub stream.toArray) :=
  rfl

theorem ofRG_zero (g : RecGraph.Graph) (rootsAt : List ℕ) (iv : List UInt8) :
    (RecCircuit.ofRG g rootsAt iv).graph.zero = g.zero := rfl

theorem evalGraphDeployed_of_size (g : RecGraph.Graph) (iv pub : List UInt8) (s : Array UInt8)
    (h : s.size = g.streamLen) :
    RecGraph.evalGraphDeployed g iv pub s = some (RecGraph.outputsOf g s
      (Id.run (RecGraph.evalNodes (m := Id) (fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) g iv pub s))) := by
  unfold RecGraph.evalGraphDeployed RecGraph.evalGraph
  rw [ite_eq_left h]
  rfl

/-- `pi1CallsWith` keeps every word but a constant word 0, and the calls' lengths. -/
theorem pi1CallsWith_words (i j : ℕ) (ra rb rd : List CallWord) (x : List UInt8) (f : Digest) (ci : ℕ)
    (hci : ci < 3) :
    let ds : List (List CallWord) := [.root i :: ra, .root j :: rb, .const x :: rd]
    ((pi1CallsWith ds f).getD ci []).length = (ds.getD ci []).length ∧
      (∀ k, 1 ≤ k → ((pi1CallsWith ds f).getD ci []).getD k default = (ds.getD ci []).getD k default) ∧
      (ci < 2 → (pi1CallsWith ds f).getD ci [] = ds.getD ci []) := by
  intro ds
  rw [show pi1CallsWith ds f = _ from pi1CallsWith_shape i j ra rb rd x f]
  interval_cases ci
  · exact ⟨rfl, fun _ _ ↦ rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ _ ↦ rfl, fun _ ↦ rfl⟩
  · refine ⟨rfl, fun k hk ↦ ?_, fun h ↦ absurd h (by norm_num)⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl

theorem list3_getD {α : Type} (l : List α) (h : l.length = 3) (d : α) : l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [_, _, _], _ => rfl

theorem three_le_of_decodeWith {reg : List (List UInt8 × Opener)} {ws : List (List UInt8)}
    {x : Digest × Opener × List PcsQuotient.Claim} (h : decodeWith reg ws = some x) : 3 ≤ ws.length := by
  match ws, h with
  | [], h => simp [decodeWith] at h
  | [_], h => simp [decodeWith] at h
  | [_, _], h => simp [decodeWith] at h
  | _ :: _ :: _ :: _, _ => simp

/-- **`CircuitBridge` for the real deployment**, from the ports' and the calls' meaning, the compiler's run at the
emitted graph's roots and the graphs agreeing (the root words as `fix-pi1-root` corrects them). -/
theorem circuitBridge (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa) (hcalls : CallWordsAgree D C Fa)
    (hlay : Pi1CallsLayouts D) :
    CircuitBridge D C.compiled fun roots input stream ↦ Fa.pubOf roots (pi2Scalars D roots input stream) := by
  intro roots input stream w ops hw hE hops
  have hrun : ∃ r0, (run (Spec.of (D.circuitAt roots.pi1).circuit) [] input.toList stream).result = .ok r0 := by
    unfold pi1OpsOf at hops
    dsimp only at hops
    split at hops
    · exact absurd hops (by simp)
    · exact ⟨_, by assumption⟩
  obtain ⟨r0, hr0⟩ := hrun
  unfold GraphsAgree at hg
  have hc : RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt
      (D.pi1IvAt roots.pi1)) = .ok (C.compiled (D.pi1IvAt roots.pi1)) := by
    have h := C.compile_ok (D.pi1IvAt roots.pi1)
    rw [hroots, hg] at h
    exact h
  generalize hcd : C.compiled (D.pi1IvAt roots.pi1) = c at hc hw hE
  generalize hiv : D.pi1IvAt roots.pi1 = iv at hc hE hcd
  have hck := RecCircuit.Compiled.checked_of_compile hc
  -- The ports' limbs are the public limbs.
  have hP : ∀ J < c.circuit.ports.size,
      (c.circuit.portLimbs w J).map F192.ofF64 = Fa.pubOf roots (pi2Scalars D roots input stream) J := fun J hJ ↦
    (limbVals_toPiop hc hJ w).symm.trans
      (hw.ports J (by simpa [RecPiop.Circuit.nP, RecCircuit.Circuit.toPiop] using hJ))
  -- The witness's public input is the calldata's.
  have hpub : c.pubW w = input.toList := by
    obtain ⟨J, hJ, hsrc, hpJ⟩ := hstmt roots input stream r0 hr0
    rw [hiv, hcd] at hJ hsrc
    have h1 := hE.1 J hJ hsrc
    have h2 := (hP J hJ).trans hpJ
    rw [h1] at h2
    have h3 := map_ofF64_inj h2
    refine bytes_eq_of_words _ _ (RecCircuit.Compiled.decodePublic_length _) (by simp) fun k hk ↦ ?_
    have := congrArg (fun l ↦ l.getD k 0) h3
    simpa [List.getD_eq_getElem?_getD, hk] using this
  -- The stream.
  have hs : D.pi1Stream w = (c.streamW (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) w).toArray := by
    rw [C.stream_eq (D.pi1IvAt roots.pi1) w, hroots, hg, hiv, hcd]
  have hsize : (c.streamW (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) w).toArray.size =
      RecGraph.Emitted.graph.streamLen := by
    rw [List.size_toArray, RecCircuit.Compiled.streamW_length, ofRG_streamLen]
  have hVr : RecCircuit.rgVals RecGraph.Emitted.graph iv (c.pubW w)
      (c.streamW (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) w) =
      Id.run (RecGraph.evalNodes (m := Id) (fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) RecGraph.Emitted.graph iv
        input.toList (c.streamW (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) w).toArray) := by
    rw [hpub, rgVals_eq]
  generalize hSd : (c.streamW (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) w).toArray = S
    at hs hsize hVr
  generalize hVd : Id.run (RecGraph.evalNodes (m := Id) (fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))
    RecGraph.Emitted.graph iv input.toList S) = V at hVr
  unfold RecCircuit.Compiled.EndStatement at hE
  rw [hVr, hSd] at hE
  -- The goal.
  unfold Pi1GraphAccepts
  rw [hs, hg, evalGraphDeployed_of_size _ _ _ _ hsize, hVd]
  -- The contract's π1 openings.
  unfold pi1OpsOf at hops
  dsimp only at hops
  split at hops
  · exact absurd hops (by simp)
  rename_i r hr
  obtain ⟨hcl, hcw⟩ := hcalls roots input stream w r (by rw [hiv, hcd]; exact hw) hr
  rw [hiv, hcd] at hcl hcw
  obtain ⟨hgl, hgw⟩ := RecCircuit.Compiled.compile_sound_calls hc hw
  rw [hVr, hSd] at hgw
  have hD3 : D.pi1Calls.length = 3 := (pi1CallsShape_data D hD.2.1).1
  obtain ⟨i, ra, j, rb, x, rd, hdata⟩ := data_pi1Calls_shape
  have hcalls3 : D.pi1Calls = [.root i :: ra, .root j :: rb, .const x :: rd] := hD.2.1.trans hdata
  have hg3 : RecGraph.Emitted.graph.calls.length = 3 := by rw [← hgl, hcl, hD3]
  set f := roots.pi1.bytecode with hf
  set cwf := callWord (D.circuitAt roots.pi1).circuit.reads stream r with hcwf
  set P := pi1CallsWith D.pi1Calls f with hP3
  have hPl : P.length = 3 := by rw [hP3, hcalls3, pi1CallsWith_shape]; rfl
  -- Each call.
  have key : ∀ k < 3, ∀ xk : Digest × Opener × List PcsQuotient.Claim,
      decodeWith (registryAt D roots) ((P.getD k []).map cwf) = some xk →
        decodePi1Call ((RecGraph.Emitted.graph.calls.getD k []).flatMap (RecGraph.wordBytes S V)) =
            some (digOf ((RecGraph.Emitted.graph.calls.getD k []).map (RecGraph.wordBytes S V)), w1 k, xk.2.2) ∧
          ((P.getD k []).map cwf).getD 1 [] = w1 k ∧
          (k < 2 → xk.1 = digOf ((RecGraph.Emitted.graph.calls.getD k []).map (RecGraph.wordBytes S V))) := by
    intro k hk xk hxk
    have hkD : k < D.pi1Calls.length := by rw [hD3]; exact hk
    have hkg : k < RecGraph.Emitted.graph.calls.length := by rw [hg3]; exact hk
    obtain ⟨hcwl, hcww⟩ := hcw k hkD
    obtain ⟨hgwl, hgww⟩ := hgw k hkg
    have hpw := pi1CallsWith_words i j ra rb rd x f k hk
    rw [← hcalls3] at hpw
    obtain ⟨hpl, hpk, hp2⟩ := hpw
    -- the graph's words and the contract's
    set gws := (RecGraph.Emitted.graph.calls.getD k []).map (RecGraph.wordBytes S V) with hgws
    set cws := (P.getD k []).map cwf with hcws
    have hlg : gws.length = (D.pi1Calls.getD k []).length := by
      rw [hgws, List.length_map, ← hgwl, hcwl]
    have hlc : cws.length = gws.length := by rw [hcws, List.length_map, hpl, hlg]
    have hword : ∀ kk < (D.pi1Calls.getD k []).length,
        cwf ((D.pi1Calls.getD k []).getD kk default) =
          RecCircuit.pcsWord kk ((RecGraph.Emitted.graph.calls.getD k []).getD kk default) (gws.getD kk []) ∧
          (cwf ((D.pi1Calls.getD k []).getD kk default)).length = 32 := by
      intro kk hkk
      obtain ⟨h1, h2⟩ := hcww kk hkk
      have h3 := hgww kk (by rw [← hgwl, hcwl]; exact hkk)
      rw [hgws, getD_map_of_lt _ _ (by rw [← hgwl, hcwl]; exact hkk) _ default]
      exact ⟨h1.symm.trans h3, h2⟩
    have htail : ∀ kk, 1 ≤ kk → kk < gws.length → cws.getD kk [] = gws.getD kk [] := by
      intro kk h1 h2
      rw [hlg] at h2
      rw [hcws, getD_map_of_lt _ _ (by rw [hpl]; exact h2) _ default, hpk kk h1, (hword kk h2).1,
        pcsWord_ne_zero (by omega)]
    have h32 : ∀ y ∈ gws, y.length = 32 := by
      intro y hy
      obtain ⟨kk, hkk, rfl⟩ := List.getElem_of_mem hy
      have hkk' : kk < (D.pi1Calls.getD k []).length := by rw [← hlg]; exact hkk
      have h := (hword kk hkk').2
      rw [(hword kk hkk').1, List.getD_eq_getElem _ _ hkk, length_pcsWord] at h
      exact h
    have h3c := three_le_of_decodeWith hxk
    have hlay1 : cws.getD 1 [] = w1 k := by
      have h1 : 1 < (D.pi1Calls.getD k []).length := by omega
      rw [hcws, getD_map_of_lt _ _ (by rw [hpl]; exact h1) _ default, hpk 1 le_rfl, hlay k hk]
      rfl
    have hg1 : gws.getD 1 [] = w1 k := by
      rw [← htail 1 le_rfl (by omega), hlay1]
    have hlook : (registryAt D roots).lookup (gws.getD 1 []) =
        some (.pi1 (UniStatement.layoutWordVars (gws.getD 1 []))) := by
      rw [hg1]; exact registryAt_lookup D roots hD.2.2.1 k hk
    obtain ⟨hdec, hroot0⟩ := per_call (registryAt D roots) gws cws hlc htail h32 hlook xk hxk
    refine ⟨by rw [hg1] at hdec; exact hdec, hlay1, fun hk2 ↦ ?_⟩
    rw [hroot0]
    have h0 : 0 < (D.pi1Calls.getD k []).length := by omega
    obtain ⟨a, ha⟩ := emitted_root_words k hk2
    rw [hcws, hp2 hk2, getD_map_of_lt _ _ h0 _ default, (hword 0 h0).1, ha, pi1RootWordOk a]
    unfold digOf
    rw [hg1, ite_eq_right (by
      have := w1_codes
      interval_cases k
      · rw [this.1]; decide
      · rw [this.2.1]; decide)]
  -- The three calls.
  have htake := pcsCalls_take (D.circuitAt roots.pi1).circuit P (digestBytes roots.pi2) stream r hPl
  unfold contractPi1Openings at hops
  rw [htake, list3_getD P hPl []] at hops
  simp only [List.map_cons, List.map_nil] at hops
  obtain ⟨o0, o1, o2, hops3, h0, h1, h2⟩ := mapM_three _ _ _ _ ops hops
  obtain ⟨x0, hx0, rfl⟩ := Option.map_eq_some_iff.mp h0
  obtain ⟨x1, hx1, rfl⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨x2, hx2, rfl⟩ := Option.map_eq_some_iff.mp h2
  have k0 := key 0 (by norm_num) x0 hx0
  have k1 := key 1 (by norm_num) x1 hx1
  have k2 := key 2 (by norm_num) x2 hx2
  subst hops3
  refine ⟨_, [(digOf ((RecGraph.Emitted.graph.calls.getD 0 []).map (RecGraph.wordBytes S V)), w1 0, x0.2.2),
    (digOf ((RecGraph.Emitted.graph.calls.getD 1 []).map (RecGraph.wordBytes S V)), w1 1, x1.2.2),
    (digOf ((RecGraph.Emitted.graph.calls.getD 2 []).map (RecGraph.wordBytes S V)), w1 2, x2.2.2)],
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- the zero checks
    intro z hz
    simp only [RecGraph.outputsOf, List.mem_map] at hz
    obtain ⟨id, hid, rfl⟩ := hz
    rcases Bool.eq_false_or_eq_true (RecCircuit.Compiled.notConst (c.nodes.getD (c.map.getD id 0) default))
      with hn | hn
    · have hcount : (c.circuit.ports.toList.filter fun p ↦ p.source == .zero).length = c.zeroNodes.length := by
        have h := hck.ports
        unfold RecCircuit.Compiled.portsOk at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact h.1
      have hzn : c.zeroNodes.length = (RecGraph.Emitted.graph.zero.filter fun id ↦
          RecCircuit.Compiled.notConst (c.nodes.getD (c.map.getD id 0) default)).length := by
        have hz := (RecCircuit.Compiled.graphOk_parts hck.graph).2.1
        unfold RecCircuit.Compiled.zeroNodes
        rw [hz, ofRG_zero, List.filter_map, List.length_map]
        rfl
      have hmem : id ∈ RecGraph.Emitted.graph.zero.filter fun id ↦
          RecCircuit.Compiled.notConst (c.nodes.getD (c.map.getD id 0) default) := List.mem_filter.mpr ⟨hid, hn⟩
      obtain ⟨m, hm, hmid⟩ := List.getElem_of_mem hmem
      obtain ⟨J, hJ, hpJ, hcJ⟩ := exists_nth_filter (fun p : RecCircuit.Port ↦ p.source == .zero)
        c.circuit.ports.toList m (by rw [hcount, hzn]; exact hm)
      have hJ' : J < c.circuit.ports.size := by simpa using hJ
      have hsrc : (c.circuit.ports.getD J default).source = .zero := by
        rw [← RecCircuit.arr_toList_getD]; simpa using hpJ
      have hzi : c.zeroIndex J = m := hcJ
      have e1 := hE.2.2.1 J hJ' hsrc
      have e2 := (hP J hJ').trans (hzero roots input stream J (by rw [hiv, hcd]; exact hJ')
        (by rw [hiv, hcd]; exact hsrc))
      rw [e1, show ([0, 0, 0] : List E) = [(0 : K), 0, 0].map F192.ofF64 by simp] at e2
      have e3 := map_ofF64_inj e2
      have e4 : RecCircuit.zeroOrig c (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv)
          (c.zeroIndex J) = id := by
        rw [hzi]
        unfold RecCircuit.zeroOrig
        rw [ofRG_zero, List.getD_eq_getElem _ _ hm]
        exact hmid
      rw [e4] at e3
      exact eq_zero_of_limbsL e3
    · exact hE.2.2.2.1 id hid hn
  · -- no nonzero check
    intro z hz
    simp only [RecGraph.outputsOf] at hz
    rw [show RecGraph.Emitted.graph.nonzero = [] from rfl] at hz
    simp at hz
  · -- the calls decode
    show (RecGraph.Emitted.graph.calls.map (·.flatMap (RecGraph.wordBytes S V))).mapM decodePi1Call = _
    rw [list3_getD RecGraph.Emitted.graph.calls hg3 []]
    simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, k0.1, k1.1, k2.1, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rfl
  · -- the layouts and claims
    simp only [List.map_cons, List.map_nil]
    rw [k0.2.1, k1.2.1, k2.2.1]
  · -- `C1`'s and `C2`'s roots
    simp only [List.take, List.map_cons, List.map_nil]
    rw [k0.2.2 (by norm_num), k1.2.2 (by norm_num)]


/-- **π2's part at the real deployment, the bridge proved**: `recKnowledgeSoundness2_real` with `CircuitBridge` from
`circuitBridge` (the ports' and calls' meaning, `Pi1CallsLayouts`; the root word `pi1RootWordOk`). -/
theorem recKnowledgeSoundness2_real_bridge (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (T : Pi2Tables D C) (hfs : Pi2FsLayer D) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa)
    (hcalls : CallWordsAgree D C Fa) (hlay : Pi1CallsLayouts D) :
    RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  recKnowledgeSoundness2_real D hD C Fa T hfs hroots hg (circuitBridge D hD C Fa hroots hg hstmt hzero hcalls hlay)

end RecCompose

/-- info: 'RecCompose.circuitBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.circuitBridge

/-- info: 'RecCompose.recKnowledgeSoundness2_real_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_real_bridge
