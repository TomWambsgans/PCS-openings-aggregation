-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The contract's π1 calls (`formal/RecStatement`:
-- `pi1OpsOf`, `decodeWith`; `Data.pi1Calls`, the Rust's `spec::Circuit::calls`) on π2's honest stream, and π1-rec3's
-- graph's openings (`pi1GraphVerifierWith`, with Keccak-256 explicit in `Pi2CompleteH`).
import RecCompose.Pi2ProbStaged
import RecCompose.Layouts
import RecCompose.FsVerifier
import RecCompose.Meanings
import RecCompose.End

/-!
# π1's openings in the contract, on π2's honest proof

**`pi2Pi1Openings hD C hchk hroots hg : Pi2Pi1Openings D C (pi2Facts hD C hchk)`**: at pure `(H, F)`, on a π1 proof
π1-rec3's graph accepts (its openings over `(H, F)`) with the honest witness π2's prover takes, the contract's three π1
calls on π2's honest proof decode (`pi1OpsOf_some`: each of `Data.pi1Calls` is a root word, a registered layout word, the
count one and one claim's element words, `decode_call`) and their openings accept: the circuit's corollary
(`circuitBridge` with the facts helper's meanings, `Pi2CircuitAccepts`) makes the graph's decoded calls the contract's
(their layouts, claims and `C1`'s, `C2`'s roots; the setup's root the contract's constant), so the graph's three
openings (`graphH_eq`) are the contract's `openSeqH` (`openSeqH_eq`).

**`recCompleteness2_pi2_closed`**, **`recCompleteness_pi2_closed_fs`**: `Pi2ProbStaged`'s, without `Pi2Pi1Openings`
(taking `GraphsAgree`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2O

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM (KeccakCalls)
open LeanVM.Protocol.Compile.Rom (missProb)
open Pi2S Pi2K Pi2E Pi2G
open scoped ENNReal

/-! ## A call's words decode -/

/-- The words that are claims' elements. -/
def isElt : CallWord → Bool
  | .element _ => true
  | .pair _ _ => true
  | _ => false

/-- An element word's element. -/
def cwE (reads : List Read) (r : Reduced) : CallWord → E
  | .element i => r.scalars.getD ((elementIndices reads).getD i 0) 0
  | .pair e c =>
    let pp := r.pairPoints.getD ((elementIndices reads).getD e 0) (0, 0)
    if c = 0 then pp.1 else pp.2
  | _ => 0

theorem callWord_of_isElt (reads : List Read) (stream : Array UInt8) (r : Reduced) (c : CallWord)
    (h : isElt c = true) : callWord reads stream r c = UniStatement.elementWord (cwE reads r c) := by
  cases c with
  | const w => simp [isElt] at h
  | root i => simp [isElt] at h
  | element i => rfl
  | pair e c => rfl

/-- **A call of a root, a registered π1 layout word, the count one and one claim's elements decodes.** -/
theorem decode_call (reg : List (List UInt8 × Opener)) (reads : List Read) (stream : Array UInt8) (r : Reduced)
    (call : List CallWord) (lw : List UInt8) (v : ℕ) (hlen3 : 3 ≤ call.length)
    (hroot : (callWord reads stream r (call.getD 0 default)).length = 32)
    (h1 : call.getD 1 default = .const lw) (h2 : call.getD 2 default = .const (UniStatement.numberWord 1))
    (hlook : reg.lookup lw = some (.pi1 v)) (hl : (call.drop 3).length = v + 1)
    (hall : (call.drop 3).all isElt = true) :
    ∃ cl, decodeWith reg (call.map (callWord reads stream r)) =
      some (rootOfWord (callWord reads stream r (call.getD 0 default)), .pi1 v, cl) ∧
      (call.map (callWord reads stream r)).getD 1 [] = lw := by
  match call, hlen3 with
  | a :: b :: c :: rest, _ =>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hroot h1 h2
    subst h1 h2
    simp only [List.drop_succ_cons, List.drop_zero] at hl hall
    have hne : rest.map (cwE reads r) ≠ [] := by
      intro h
      rw [List.map_eq_nil_iff] at h
      subst h
      simp at hl
    have hmap : rest.map (callWord reads stream r) = (rest.map (cwE reads r)).map UniStatement.elementWord := by
      rw [List.map_map]
      exact List.map_congr_left fun c hc ↦ callWord_of_isElt reads stream r c (List.all_eq_true.mp hall c hc)
    have hw : (a :: .const lw :: .const (UniStatement.numberWord 1) :: rest).map (callWord reads stream r) =
        [callWord reads stream r a, lw, UniStatement.numberWord 1] ++
          ([((rest.map (cwE reads r)).dropLast, (rest.map (cwE reads r)).getLast hne)].map claimWords).flatten := by
      rw [List.map_cons, List.map_cons, List.map_cons, hmap]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, claimWords,
        List.dropLast_append_getLast]
      rfl
    have hdc := decodeWith_mk reg _ lw (.pi1 v)
      [((rest.map (cwE reads r)).dropLast, (rest.map (cwE reads r)).getLast hne)] hroot hlook (by simp) Pi1Decode.countOfWord_numberWord_one
      (fun c hc ↦ by
        simp only [List.mem_singleton] at hc
        subst hc
        simp [Opener.vars, hl])
    rw [List.length_singleton, ← hw] at hdc
    exact ⟨_, hdc, rfl⟩

/-! ## `Data.pi1Calls` -/

/-- A call's layout word, as `Data` writes it. -/
def litWord (k : ℕ) : List UInt8 :=
  match (Data.pi1Calls.getD k []).getD 1 default with
  | .const w => w
  | _ => []

theorem litWord_eq (k : ℕ) (hk : k < 3) : litWord k = w1 k := by
  unfold litWord
  rw [data_pi1Calls_layouts k hk]

/-- **`Data.pi1Calls`' shape** (kernel decisions on the recorded calls): three calls of a root (`C1`'s, `C2`'s, the
setup's constant), the layout word, the count one, and one claim of the layout's variables. -/
theorem data_calls :
    Data.pi1Calls.length = 3 ∧
    (∀ k < 3, 3 ≤ (Data.pi1Calls.getD k []).length ∧
      (Data.pi1Calls.getD k []).getD 2 default = .const (UniStatement.numberWord 1) ∧
      ((Data.pi1Calls.getD k []).drop 3).length = UniStatement.layoutWordVars (litWord k) + 1 ∧
      ((Data.pi1Calls.getD k []).drop 3).all isElt = true) ∧
    (Data.pi1Calls.getD 0 []).getD 0 default = .root 0 ∧ (Data.pi1Calls.getD 1 []).getD 0 default = .root 1 := by
  decide +kernel

/-- `pi1CallsWith` on `Data.pi1Calls`: the setup's constant root word replaced. -/
theorem pi1CallsWith_data (f : Digest) :
    pi1CallsWith Data.pi1Calls f = [Data.pi1Calls.getD 0 [], Data.pi1Calls.getD 1 [],
      .const (rootWordOfBytes (digestBytes f)) :: (Data.pi1Calls.getD 2 []).tail] := rfl

/-- **The contract's π1 calls decode on π2's stream**, its run over Keccak-f[1600] succeeding: their layout words are
π1-rec3's, the third's root the setup's. -/
theorem pi1OpsOf_some (D : RecDeployment) (hD : D.Real) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (stream : Array UInt8) (r : Reduced)
    (hr : (run (Spec.of (D.circuitAt roots.pi1).circuit) [] input.toList stream).result = .ok r)
    (hsz : stream.size = pi2Bytes (Spec.of Data.circuit)) :
    ∃ o0 o1 o2 : Pi1Opening, pi1OpsOf D roots input stream = some [o0, o1, o2] ∧ o0.2.1 = w1 0 ∧ o1.2.1 = w1 1 ∧
      o2.2.1 = w1 2 ∧ o2.1 = roots.pi1.bytecode := by
  have hview : (D.circuitAt roots.pi1).circuit = Data.circuit := hD.1 _
  obtain ⟨hl3, hk, h0r, h1r⟩ := data_calls
  have hsh : D.pi1.shape = UniStatement.reference := hD.2.2.1
  have hlook : ∀ k < 3, (registryOf D.pi1.shape (D.circuitAt roots.pi1).circuit.logN).lookup (litWord k) = some (.pi1 (UniStatement.layoutWordVars (litWord k))) := by
    intro k hk3
    rw [litWord_eq k hk3]
    exact registryAt_lookup D roots hsh k hk3
  have hrl : ∀ i < 2, (callWord (D.circuitAt roots.pi1).circuit.reads stream r (.root i)).length = 32 := by
    intro i hi
    show (streamWord stream ((rootsAt (D.circuitAt roots.pi1).circuit.reads).getD i 0)).length = 32
    refine streamWord_length _ _ ?_
    rw [hsz, hview]
    interval_cases i <;> decide +kernel
  obtain ⟨hk0, hn0, hv0, ha0⟩ := hk 0 (by decide)
  obtain ⟨hk1, hn1, hv1, ha1⟩ := hk 1 (by decide)
  obtain ⟨hk2, hn2, hv2, ha2⟩ := hk 2 (by decide)
  obtain ⟨cl0, hd0, hw0⟩ := decode_call (registryOf D.pi1.shape (D.circuitAt roots.pi1).circuit.logN)
    (D.circuitAt roots.pi1).circuit.reads stream r (Data.pi1Calls.getD 0 []) (litWord 0) _ hk0
    (by rw [h0r]; exact hrl 0 (by decide)) (by rw [litWord_eq 0 (by decide)]; exact data_pi1Calls_layouts 0 (by decide)) hn0 (hlook 0 (by decide)) hv0 ha0
  obtain ⟨cl1, hd1, hw1⟩ := decode_call (registryOf D.pi1.shape (D.circuitAt roots.pi1).circuit.logN)
    (D.circuitAt roots.pi1).circuit.reads stream r (Data.pi1Calls.getD 1 []) (litWord 1) _ hk1
    (by rw [h1r]; exact hrl 1 (by decide))
    (by rw [litWord_eq 1 (by decide)]; exact data_pi1Calls_layouts 1 (by decide)) hn1 (hlook 1 (by decide)) hv1 ha1
  obtain ⟨cl2, hd2, hw2⟩ := decode_call (registryOf D.pi1.shape (D.circuitAt roots.pi1).circuit.logN)
    (D.circuitAt roots.pi1).circuit.reads stream r
    (.const (rootWordOfBytes (digestBytes roots.pi1.bytecode)) :: (Data.pi1Calls.getD 2 []).tail) (litWord 2) _
    (by rw [show (CallWord.const (rootWordOfBytes (digestBytes roots.pi1.bytecode)) :: (Data.pi1Calls.getD 2 []).tail).length = (Data.pi1Calls.getD 2 []).length from rfl]; exact hk2)
    (by
      show (rootWordOfBytes (digestBytes roots.pi1.bytecode)).length = 32
      simp [rootWordOfBytes, Pi1Decode.length_digestBytes])
    (by
      rw [show (CallWord.const (rootWordOfBytes (digestBytes roots.pi1.bytecode)) :: (Data.pi1Calls.getD 2 []).tail).getD 1 default = (Data.pi1Calls.getD 2 []).getD 1 default from rfl, litWord_eq 2 (by decide)]
      exact data_pi1Calls_layouts 2 (by decide))
    (by rw [show (CallWord.const (rootWordOfBytes (digestBytes roots.pi1.bytecode)) :: (Data.pi1Calls.getD 2 []).tail).getD 2 default = (Data.pi1Calls.getD 2 []).getD 2 default from rfl]; exact hn2)
    (hlook 2 (by decide))
    (by rw [show (CallWord.const (rootWordOfBytes (digestBytes roots.pi1.bytecode)) :: (Data.pi1Calls.getD 2 []).tail).drop 3 = (Data.pi1Calls.getD 2 []).drop 3 from rfl]; exact hv2)
    (by rw [show (CallWord.const (rootWordOfBytes (digestBytes roots.pi1.bytecode)) :: (Data.pi1Calls.getD 2 []).tail).drop 3 = (Data.pi1Calls.getD 2 []).drop 3 from rfl]; exact ha2)
  rw [h0r] at hd0
  rw [h1r] at hd1
  have hlist : (pi1CallsWith D.pi1Calls roots.pi1.bytecode).map
      (·.map (callWord (D.circuitAt roots.pi1).circuit.reads stream r)) =
      [(Data.pi1Calls.getD 0 []).map (callWord (D.circuitAt roots.pi1).circuit.reads stream r),
        (Data.pi1Calls.getD 1 []).map (callWord (D.circuitAt roots.pi1).circuit.reads stream r),
        (CallWord.const (rootWordOfBytes (digestBytes roots.pi1.bytecode)) :: (Data.pi1Calls.getD 2 []).tail).map (callWord (D.circuitAt roots.pi1).circuit.reads stream r)] := by
    rw [hD.2.1, pi1CallsWith_data]
    rfl
  have hops : pi1OpsOf D roots input stream = some
      [(rootOfWord (callWord (D.circuitAt roots.pi1).circuit.reads stream r (.root 0)), litWord 0, cl0),
        (rootOfWord (callWord (D.circuitAt roots.pi1).circuit.reads stream r (.root 1)), litWord 1, cl1),
        (rootOfWord (callWord (D.circuitAt roots.pi1).circuit.reads stream r ((CallWord.const (rootWordOfBytes (digestBytes roots.pi1.bytecode)) :: (Data.pi1Calls.getD 2 []).tail).getD 0 default)),
          litWord 2, cl2)] := by
    unfold pi1OpsOf
    dsimp only
    rw [hr]
    dsimp only
    unfold contractPi1Openings
    rw [pcsCalls_take _ _ _ _ _ (by simp [pi1CallsWith, hD.2.1, hl3]), hlist]
    simp only [List.mapM_cons, List.mapM_nil, hd0, hw0, hd1, hw1, hd2, hw2, Option.map_some, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  exact ⟨_, _, _, hops, litWord_eq 0 (by decide), litWord_eq 1 (by decide), litWord_eq 2 (by decide),
    rootOfWord_rootWordOfBytes_digestBytes _⟩

/-! ## The graph's openings and the contract's -/

/-- **π1-rec3's graph with its openings over `(H, F)`**, its checks holding and its calls decoding to three openings:
the three openings, the setup's root the deployment's. -/
theorem graphH_eq (H : List UInt8 → Id Digest) (F : KeccakState → Id KeccakState) (D : RecDeployment)
    (roots : UniStatement.SetupRoots) (input : Vector UInt8 32) (p1 : UniStatement.UniProof)
    (gout : RecGraph.Outputs) (g0 g1 g2 : Pi1Opening)
    (hev : RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph (D.pi1IvAt roots) input.toList p1.stream = some gout)
    (hchk : (gout.zeros.all (· == 0) && gout.nonzeros.all (· != 0)) = true)
    (hdec : gout.calls.mapM decodePi1Call = some [g0, g1, g2]) :
    Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) H F D roots input p1) =
      (((true && Id.run (UniComplete.pcsOpenWithH H F (UniStatement.layoutWordVars g0.2.1) g0.1 g0.2.2 p1.c1)) &&
        Id.run (UniComplete.pcsOpenWithH H F (UniStatement.layoutWordVars g1.2.1) g1.1 g1.2.2 p1.c2)) &&
        Id.run (UniComplete.pcsOpenWithH H F (UniStatement.layoutWordVars g2.2.1) roots.bytecode g2.2.2
          p1.setup)) := by
  unfold Pi2H.pi1GraphVerifierWithH
  rw [hev]
  simp only [hchk, hdec, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **The contract's three π1 openings**, their layout words registered with π1's opener. -/
theorem openSeqH_eq (H : List UInt8 → Id Digest) (F : KeccakState → Id KeccakState)
    (reg : List (List UInt8 × Opener)) (o0 o1 o2 : Pi1Opening) (proof : RecProof) (v0 v1 v2 : ℕ)
    (h0 : reg.lookup o0.2.1 = some (.pi1 v0)) (h1 : reg.lookup o1.2.1 = some (.pi1 v1))
    (h2 : reg.lookup o2.2.1 = some (.pi1 v2)) :
    Id.run (Pi2H.openSeqH (m := Id) H F reg [o0, o1, o2] proof) =
      ((Id.run (UniComplete.pcsOpenWithH H F v0 o0.1 o0.2.2 proof.c1) &&
        Id.run (UniComplete.pcsOpenWithH H F v1 o1.1 o1.2.2 proof.c2)) &&
        Id.run (UniComplete.pcsOpenWithH H F v2 o2.1 o2.2.2 proof.f)) := by
  unfold Pi2H.openSeqH Pi2H.openAtH
  simp only [List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2]
  rfl

/-- **π2's honest proof**: its stream the honest prover's, π1's opening proofs π1's. -/
theorem pi2Prover_some {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (Hk : List UInt8 → Digest)
    (F : KeccakState → Id KeccakState) (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniStatement.UniProof)
    (proof : RecProof) (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C Fa fuel input p1) = some proof) :
    proof.stream = (outOf D Hk (rootsH D Hk F) (C.G (rootsH D Hk F)) input
        (pi2Choice D C Fa (rootsH D Hk F) input p1.stream).1 (pi2Choice D C Fa (rootsH D Hk F) input p1.stream).2).stream ∧
      proof.c1 = p1.c1 ∧ proof.c2 = p1.c2 ∧ proof.f = p1.setup := by
  rw [pi2ProverWith_run, pi2ProveWith_run, logN_G Fa] at hp
  revert hp
  generalize E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).1 _ _ _ = rW
  generalize E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).2.2 _ _ _ = rS
  generalize E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).2.1 _ _ _ = rQ
  intro hp
  cases rW with
  | none => simp at hp
  | some a =>
    cases rS with
    | none => simp at hp
    | some b =>
      cases rQ with
      | none => simp at hp
      | some c =>
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hp
        subst hp
        exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## π1's openings in the contract -/

/-- **`Pi2Pi1Openings` at the real deployment's facts**: the circuit's corollary (`circuitBridge` with the facts
helper's meanings) makes the graph's calls the contract's, so the graph's openings are the contract's. -/
theorem pi2Pi1Openings {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) :
    Pi2Pi1Openings D C (pi2Facts hD C hchk) := by
  intro Ht Ft input p1 proof hgood ha1 hpr
  obtain ⟨hmatch, hsat, hstr⟩ := hgood
  have hview : (D.circuitAt (rootsH D Ht Ft).pi1).circuit = Data.circuit := hD.1 _
  obtain ⟨hps, hc1, hc2, hcf⟩ := pi2Prover_some (pi2Facts hD C hchk) Ht Ft _ input p1 proof hpr
  -- π2's run on the honest stream, over `Ht` and over Keccak-f[1600]
  obtain ⟨r, hr, -, hsc, -, -, -, -, hi, -, -⟩ := runWith_honest Ht (C.G (rootsH D Ht Ft))
    (D.circuitAt (rootsH D Ht Ft).pi1).circuit (D.circuitAt (rootsH D Ht Ft).pi1).setupStack
    (ivOf D Ht (rootsH D Ht Ft)) input.toList (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).1
    (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).2 hmatch
    (by rw [hview, (pi2Facts hD C hchk).logW]; rfl)
  obtain ⟨hpost, -⟩ := holds_id (Pi2H.runWithH_post (m := Id) (Pure.pure ∘ Ht)
    (Spec.of (D.circuitAt (rootsH D Ht Ft).pi1).circuit) (ivOf D Ht (rootsH D Ht Ft)) input.toList
    (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input
      (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).1
      (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).2).stream)
  obtain ⟨hsz, hsc', hpp⟩ := hpost r hr
  obtain ⟨r', hr', hsc'', -⟩ := run_ok_of_runWith (m := Id) _ input.toList _ [] r hsz hsc' hpp
  have hscal : pi2Scalars D (rootsH D Ht Ft) input
      (outOf D Ht (rootsH D Ht Ft) (C.G (rootsH D Ht Ft)) input
        (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).1
        (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).2).stream =
      publicScalarsOf input.toList (pi2Choice D C (pi2Facts hD C hchk) (rootsH D Ht Ft) input p1.stream).1 := by
    unfold pi2Scalars
    rw [hr']
    dsimp only
    rw [hsc'', hsc, hi]
  -- the contract's π1 calls
  obtain ⟨o0, o1, o2, hops, h0, h1, h2, hb⟩ := pi1OpsOf_some D hD (rootsH D Ht Ft) input _ r' hr'
    (by rw [hsz, hview])
  -- the circuit's corollary
  have hca := pi2CircuitAccepts_of_bridge C (pi2Facts hD C hchk) hroots hg
    (circuitBridge D hD C (pi2Facts hD C hchk) hroots hg (statementPortMeaning hD C hchk)
      (zeroPortsMeaning hD C hchk) (callWordsAgree hD C hchk) (pi1CallsLayouts_of_real hD))
  have hacc := hca (rootsH D Ht Ft) input _ _ _ (by rw [hscal]; exact hsat) hops
  rw [hstr] at hacc
  obtain ⟨gout, gops, hev, hz, hnz, hdec, hmap, htake⟩ := hacc
  have hl3 : gops.length = 3 := by
    have := congrArg List.length hmap
    simpa using this
  obtain ⟨g0, g1, g2, rfl⟩ : ∃ a b c, gops = [a, b, c] := by
    match gops, hl3 with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  have hchk' : (gout.zeros.all (· == 0) && gout.nonzeros.all (· != 0)) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨hz, hnz⟩
  rw [graphH_eq _ _ D _ input p1 gout g0 g1 g2 hev hchk' hdec] at ha1
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
  obtain ⟨e0, e1, e2⟩ := hmap
  obtain ⟨r0, r1⟩ : g0.1 = o0.1 ∧ g1.1 = o1.1 := by simpa using htake
  refine ⟨[o0, o1, o2], by rw [hps]; exact hops, ?_⟩
  have hreg : registryOf D.pi1.shape 24 = registryAt D (rootsH D Ht Ft) := by
    unfold registryAt
    rw [hview]
    rfl
  have hsh : D.pi1.shape = UniStatement.reference := hD.2.2.1
  rw [openSeqH_eq _ _ _ o0 o1 o2 proof _ _ _
    (by rw [hreg, h0]; exact registryAt_lookup D _ hsh 0 (by decide))
    (by rw [hreg, h1]; exact registryAt_lookup D _ hsh 1 (by decide))
    (by rw [hreg, h2]; exact registryAt_lookup D _ hsh 2 (by decide))]
  rcases g0 with ⟨a0, w0, k0⟩
  rcases g1 with ⟨a1, w1', k1⟩
  rcases g2 with ⟨a2, w2, k2⟩
  rcases o0 with ⟨b0, u0, l0⟩
  rcases o1 with ⟨b1, u1, l1⟩
  rcases o2 with ⟨b2, u2, l2⟩
  simp only [Prod.mk.injEq] at e0 e1 e2 r0 r1 h0 h1 h2 hb ha1 ⊢
  subst r0 r1 hb
  obtain ⟨rfl, rfl⟩ := e0
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  subst h0 h1 h2
  rw [hc1, hc2, hcf]
  simpa using ha1

/-! ## π2's completeness without `Pi2Pi1Openings` -/

/-- **π2's completeness, `Pi2Pi1Openings` proved** (`pi2Pi1Openings`, from `GraphsAgree`): `recCompleteness2_pi2_staged`
from the staged run's named facts and the witness's completeness. -/
theorem recCompleteness2_pi2_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hhash : Pi2HashBeforeAlpha D C (pi2Facts hD C hchk) P1k) (htf : Pi2TFresh D C (pi2Facts hD C hchk) P1k εt)
    (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_pi2_staged hD C hchk hroots P1 P1k hexp hrun hdup hcost hhash htf
    (pi2Pi1Openings hD C hchk hroots hg) hwc

/-- **The recursive verifier's completeness end to end, `Pi2Pi1Openings` proved.** -/
theorem recCompleteness_pi2_closed_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree) (P1 : Pi1Prover D)
    (P1k : Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniStatement.UniProof))
    {N : ℕ} {εt : ℝ≥0∞}
    (hexp : Pi2ExperimentLe D C (pi2Facts hD C hchk) P1 P1k) (hrun : Pi2RunAt D C (pi2Facts hD C hchk) P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hhash : Pi2HashBeforeAlpha D C (pi2Facts hD C hchk) P1k) (htf : Pi2TFresh D C (pi2Facts hD C hchk) P1k εt)
    (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2 N εt ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_pi2_staged_fs hD C hchk hroots P1 P1k hexp hrun hdup hcost hhash htf
    (pi2Pi1Openings hD C hchk hroots hg) hwc δ1 δh h1 hh

end RecCompose.Pi2O

/-- info: 'RecCompose.Pi2O.pi2Pi1Openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2O.pi2Pi1Openings

/-- info: 'RecCompose.Pi2O.recCompleteness2_pi2_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2O.recCompleteness2_pi2_closed

/-- info: 'RecCompose.Pi2O.recCompleteness_pi2_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2O.recCompleteness_pi2_closed_fs
