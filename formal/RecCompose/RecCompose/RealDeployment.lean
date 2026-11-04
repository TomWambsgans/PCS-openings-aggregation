-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Facts
import RecCompose.Circuit
import UniComplete.Reference

/-!
# The real deployment, and the run-checked inputs that build its circuits

`STATEMENT_REVIEW.md`, findings 1 and 5: no `D` with `D.Real` was exhibited, and `Pi2Circuits D` quantified over IVs
of every length (so it was uninhabited). Here:

* **`realDeployment prog hprog`**: π1's deployment at the reference shape and leanVM's program IV, for the program
  `prog` (any program of the reference shape's size; leanVM 42422001's is not transcribed in Lean); π2's circuit at
  each IV `pi2CircuitOf` of the Lean compiler's (`compiledAt iv`: `RecCircuit.compile` on π1-rec3's emitted graph at
  that IV), so `σ`, `κ` are the compiler's by construction; π1's calls `Data.pi1Calls`; π1's stream `streamW` of the
  compiled circuit at π1's reference IV (`realStream`).
* **`realDeployment_real`**: `(realDeployment prog hprog).Real`, from `GraphsAgree` (the existing run) and two
  evaluated checks of single values: **`DigestChecked`** (the digest of the compiler's `σ`, `κ` at `Data.pi1Iv` is the
  Rust's `Data.digest`) and **`SetupRootChecked`** (their setup tree's root is the Rust's `Data.setupRoot`).
* **`IvChecked`**: one `Bool` per 32-byte IV, `ivCheck iv`: the compiler accepts π1-rec3's emitted graph at `iv`, the
  circuit passes `viewCheck`, and its π1-stream decoding agrees with the reference IV's (`streamAgree`: the same free
  bits and free reads, each of their values read off the witness the same way). **Stated for every 32-byte IV,
  checked by evaluation at three** (π1's reference IV, the zero IV, the all-ones IV: `rec-real-check`,
  `RecComposeTest/RealCheck.lean`), assumed at the others.
* **`pi2Circuits_real`**, **`pi2ViewChecked_real`**: `Pi2Circuits (realDeployment prog hprog)` and its
  `Pi2ViewChecked`, from `GraphsAgree` and `IvChecked`. `stream_eq` at every IV follows from `streamAgree`
  (`streamW_eq_of_streamAgree`), so it is no longer a functional equation no evaluation checks.

**Why `IvChecked` is not proved (IV uniformity).** The IV enters the compiler at one place, the seed's message
(`constantBits NAME ++ constantBits r.iv ++ publicCopy`, one Keccak-f block): its 256 bits are the 256 constants
`fresh 0` / `fresh 1` of the seed's permutation input (`permute`), whose only IV dependence is `setKappa`'s write of
`κ = 1` (a `0` is not stored: the circuit's `κ` is sparse). So κ has exactly one entry more per IV one-bit: 19,143
entries at the reference IV (146 one-bits) and 18,997 at the zero IV (`view9b.log`). Besides `κ`, the IV is in the
traces the checker reads (the seed sponge's message and block input, `nodeOk`'s `seedMessage iv`, `graphOk`'s length
check). A proof that the rest of the run (regions, rows, placements, values, σ, the view, the ports, `validB`, the
checker's verdict, `streamW`) does not depend on those 256 constants is a relational simulation of the whole builder
(`compileM`, the templates and `finish`, about 1,200 lines of monadic code) and of the checker (680 lines); it is not
done. The three evaluated IVs set every IV constant both ways (the zero IV all `0`, the all-ones IV all `1`).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open RecCircuit (NONE)

/-! ## The compiler's circuit at an IV, as the deployment's -/

/-- **The Lean compiler on π1-rec3's emitted graph at `iv`** (the default circuit if it rejects). -/
def compiledAt (iv : List UInt8) : RecCircuit.Compiled :=
  match RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) with
  | .ok c => c
  | .error _ => default

/-- The compiled circuit at π1's reference IV. -/
def refCompiled : RecCircuit.Compiled := compiledAt Data.pi1Iv

/-- **π2's circuit from a compiled one**: `Data.circuit` as the verifier's view, the compiler's `σ` and `κ` (`κ` read
from its dense column on the positions, which is `kappaAt` there: `pi2CircuitOf_kappa`). -/
def pi2CircuitOf (C : RecCircuit.Circuit) : Pi2Circuit :=
  let kd := RecCircuit.denseKappa C
  ⟨Data.circuit, C.sigmaAt, fun i ↦ if i < C.n then kd.getD i 0 else C.kappaAt i⟩

theorem pi2CircuitOf_kappa (C : RecCircuit.Circuit) : (pi2CircuitOf C).kappa = C.kappaAt := by
  funext i
  show (if i < C.n then (RecCircuit.denseKappa C).getD i 0 else C.kappaAt i) = C.kappaAt i
  split_ifs with h
  · exact RecCircuit.denseKappa_getD C i h
  · rfl

/-- **π1's stream on π2's witness**: the compiler's decoding of the free bits (`streamW`) at π1's reference IV. -/
def realStream (w : ℕ → K) : Array UInt8 :=
  (refCompiled.streamW (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt Data.pi1Iv) w).toArray

/-- π1's deployment at the reference shape and leanVM's program IV, for the program `prog`. -/
def realPi1 (prog : Lv42.Semantics.Program) (hprog : UniStatement.reference.logBytecode = prog.logSize) :
    UniStatement.Deployment :=
  ⟨prog, UniStatement.reference, UniStatement.programIv, UniComplete.reference_valid, hprog⟩

/-- **The real deployment**, for π1's program `prog` (`D.pi1.prog` is not pinned by `RecDeployment.Real`: the end
theorems hold for every program of the reference shape). -/
def realDeployment (prog : Lv42.Semantics.Program) (hprog : UniStatement.reference.logBytecode = prog.logSize) :
    RecDeployment where
  pi1 := realPi1 prog hprog
  pi2 iv := pi2CircuitOf (compiledAt iv).circuit
  pi1Calls := Data.pi1Calls
  pi1Stream := realStream

/-! ## The evaluated checks -/

/-- The digest of π2's circuit from a compiled one, over Keccak-f[1600] (`Real`'s expression at `Data.pi1Iv`). -/
def digestOf (C : RecCircuit.Circuit) : List UInt8 :=
  Id.run ((pi2CircuitOf C).digestWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))

/-- The setup root of π2's circuit from a compiled one, over Keccak-f[1600] (`Real`'s expression at `Data.pi1Iv`). -/
def setupRootOf (C : RecCircuit.Circuit) : List UInt8 :=
  digestBytes (Id.run ((pi2CircuitOf C).setupTreeWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))).root

/-- **The digest of the Lean compiler's `σ`, `κ` at π1's reference IV is the Rust's** (`Circuit::digest`, the constant
from which the Rust computes the deployed contract's π2 IV). A `Prop` about one value: **checked by evaluation**
(`rec-real-check`). -/
def DigestChecked : Prop := digestOf refCompiled.circuit = Data.digest

/-- **The setup root of the Lean compiler's `σ`, `κ` at π1's reference IV is the Rust's** (`Setup::new(circuit).root()`,
a WHIR commitment of `2^25` words). A `Prop` about one value: **checked by evaluation** (`rec-real-check --setup`). -/
def SetupRootChecked : Prop := setupRootOf refCompiled.circuit = Data.setupRoot

/-- A value is read off the witness the same way in two circuits' views (`Ctx.val`): the same producer, then the same
first forward (a free value) or the same formula, width and `κ` at the producer. -/
def valAgree (X Y : RecCircuit.Ctx) (v : ℕ) : Bool :=
  decide (X.prod v = Y.prod v) &&
    (if X.prod v = NONE then decide ((X.chain v).getD 0 0 = (Y.chain v).getD 0 0)
     else decide (X.prod v < X.n) && decide (X.prod v < Y.n) && decide (X.C.width = Y.C.width) &&
       decide (X.C.formulaAt (X.prod v) = Y.C.formulaAt (X.prod v)) && decide (X.kap (X.prod v) = Y.kap (X.prod v)))

/-- **Two compiled circuits decode π1's stream alike**: the same free bits and free reads (`bitSelf`, `freeReads`),
each of their values (and `NONE`) read off the witness the same way (`valAgree`). -/
def streamAgree (c c0 : RecCircuit.Compiled) : Bool :=
  let X := c.ctx
  let Y := c0.ctx
  decide (c.bitSelf = c0.bitSelf) && decide (c.freeReads = c0.freeReads) && valAgree X Y NONE &&
    c.bitSelf.all (fun o ↦ match o with
      | some v => valAgree X Y v
      | none => true) &&
    c.freeReads.all (fun e ↦ e.2.all (valAgree X Y))

/-- **The per-IV check**: the compiler accepts π1-rec3's emitted graph at `iv`, the circuit passes the view check, and
it decodes π1's stream as the reference IV's circuit does. -/
def ivCheck (iv : List UInt8) : Bool :=
  match RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) with
  | .ok c => viewCheck c && streamAgree c refCompiled
  | .error _ => false

/-- **The per-IV check holds at every 32-byte IV.** Stated for every 32-byte IV, **checked by evaluation at three**
(π1's reference IV, the zero IV, the all-ones IV: `rec-real-check`), assumed at the others (IV uniformity is not
proved; see the module docstring). -/
def IvChecked : Prop := ∀ iv : List UInt8, iv.length = 32 → ivCheck iv = true

/-! ## From the checks -/

theorem ivCheck_spec {iv : List UInt8} (h : ivCheck iv = true) :
    RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) = .ok (compiledAt iv) ∧
      viewCheck (compiledAt iv) = true ∧ streamAgree (compiledAt iv) refCompiled = true := by
  unfold ivCheck at h
  unfold compiledAt
  split at h
  · next c hc =>
    rw [hc]
    simp only [Bool.and_eq_true] at h
    exact ⟨rfl, h.1, h.2⟩
  · exact absurd h (by simp)

theorem val_eq_of_valAgree {X Y : RecCircuit.Ctx} (hX : X.kd = RecCircuit.denseKappa X.C)
    (hY : Y.kd = RecCircuit.denseKappa Y.C) {v : ℕ} (h : valAgree X Y v = true) (w : ℕ → K) :
    X.val w v = Y.val w v := by
  unfold valAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hp, h2⟩ := h
  unfold RecCircuit.Ctx.val
  rw [← hp]
  split_ifs at h2 ⊢ with hn
  · simp only [decide_eq_true_eq] at h2
    rw [h2]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨⟨hlt, hlt'⟩, hw⟩, hf⟩, hk⟩ := h2
    unfold RecCircuit.Circuit.push RecCircuit.Circuit.cells
    rw [hf, hw, ← RecCircuit.Ctx.kap_eq X hX hlt, ← RecCircuit.Ctx.kap_eq Y hY (hp ▸ hlt'), hk, hp]

theorem decodeStream_congr (c : RecCircuit.Compiled) (n : ℕ) (f g : ℕ → K)
    (hS : ∀ k, f (c.streamBit k) = g (c.streamBit k))
    (hR : ∀ e ∈ c.freeReads, ∀ i, f (e.2.getD i NONE) = g (e.2.getD i NONE)) :
    c.decodeStream n f = c.decodeStream n g := by
  unfold RecCircuit.Compiled.decodeStream
  refine List.map_congr_left fun i _ ↦ ?_
  split_ifs
  · simp only [hS]
  · split
    · next off ls heq =>
      simp only [hR _ (Array.mem_of_find?_eq_some heq)]
    · rfl

theorem decodeStream_eq_of (c c0 : RecCircuit.Compiled) (hb : c.bitSelf = c0.bitSelf)
    (hf : c.freeReads = c0.freeReads) (n : ℕ) (g : ℕ → K) : c.decodeStream n g = c0.decodeStream n g := by
  unfold RecCircuit.Compiled.decodeStream RecCircuit.Compiled.streamBit
  rw [hb, hf]

theorem getD_mem_or {a : Array ℕ} {i : ℕ} : a.getD i NONE ∈ a ∨ a.getD i NONE = NONE := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : a[i]? with
  | none => exact .inr rfl
  | some x => exact .inl (Array.mem_of_getElem? h)

/-- **`streamAgree` gives the same π1 stream** on every witness. -/
theorem streamW_eq_of_streamAgree {c c0 : RecCircuit.Compiled} (h : streamAgree c c0 = true)
    (r r0 : RecCircuit.Recorded) (hn : r.graph.streamLen = r0.graph.streamLen) (w : ℕ → K) :
    c.streamW r w = c0.streamW r0 w := by
  unfold streamAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨⟨⟨hb, hf⟩, hN⟩, hbits⟩, hreads⟩ := h
  have hv : ∀ v, valAgree c.ctx c0.ctx v = true → c.ctx.val w v = c0.ctx.val w v :=
    fun v hv ↦ val_eq_of_valAgree rfl rfl hv w
  unfold RecCircuit.Compiled.streamW
  rw [hn, decodeStream_congr c _ _ (c0.ctx.val w), decodeStream_eq_of c c0 hb hf]
  · intro k
    apply hv
    unfold RecCircuit.Compiled.streamBit
    rw [Array.getD_eq_getD_getElem?]
    cases ho : c.bitSelf[k]? with
    | none => exact hN
    | some o =>
      have hm := hbits o (Array.mem_of_getElem? ho)
      cases o with
      | none => exact hN
      | some v => exact hm
  · intro e he i
    apply hv
    rcases getD_mem_or (a := e.2) (i := i) with hm | hm
    · exact Array.all_eq_true_iff_forall_mem.mp (hreads e he) _ hm
    · rw [hm]; exact hN

/-! ## The real deployment's circuits and `Real` -/

variable (prog : Lv42.Semantics.Program) (hprog : UniStatement.reference.logBytecode = prog.logSize)

theorem compiledAt_of_compile {iv : List UInt8} {c : RecCircuit.Compiled} (hg : GraphsAgree)
    (hc : RecCircuit.compile (RecCircuit.ofRG RecGraph.Pi1.pi1Graph RecGraph.Emitted.rootsAt iv) = .ok c) :
    compiledAt iv = c := by
  unfold GraphsAgree at hg
  rw [hg] at hc
  unfold compiledAt
  rw [hc]

/-- **The real deployment is `Real`**, from `GraphsAgree` and the two evaluated checks (`DigestChecked`,
`SetupRootChecked`). The circuit, the calls, the shape, the program IV and the setup columns hold by construction. -/
theorem realDeployment_real (hg : GraphsAgree) (hd : DigestChecked) (hs : SetupRootChecked) :
    (realDeployment prog hprog).Real :=
  ⟨fun _ ↦ rfl, rfl, rfl, rfl, hd, hs, fun iv _ c hc ↦ by
    have e := compiledAt_of_compile hg hc
    refine ⟨?_, ?_⟩
    · show (compiledAt iv).circuit.sigmaAt = _
      rw [e]
    · show (pi2CircuitOf (compiledAt iv).circuit).kappa = _
      rw [pi2CircuitOf_kappa, e]⟩

/-- **The real deployment's compiled circuits** (`Pi2Circuits`), from `GraphsAgree` and `IvChecked`. -/
def pi2Circuits_real (hg : GraphsAgree) (h : IvChecked) : Pi2Circuits (realDeployment prog hprog) where
  rootsAt := RecGraph.Emitted.rootsAt
  compiled := compiledAt
  compile_ok iv hiv := by
    unfold GraphsAgree at hg
    rw [hg]
    exact (ivCheck_spec (h iv hiv)).1
  stream_eq iv hiv w := by
    show realStream w = _
    unfold realStream
    rw [streamW_eq_of_streamAgree (ivCheck_spec (h iv hiv)).2.2 _ (RecCircuit.ofRG RecGraph.Emitted.graph
      RecGraph.Emitted.rootsAt Data.pi1Iv) (by unfold GraphsAgree at hg; rw [hg]; rfl) w]
    rfl

/-- **The real deployment's circuits pass the view check** at every 32-byte IV, from `IvChecked`. -/
theorem pi2ViewChecked_real (hg : GraphsAgree) (h : IvChecked) : Pi2ViewChecked (pi2Circuits_real prog hprog hg h) :=
  fun iv hiv ↦ (ivCheck_spec (h iv hiv)).2.1

theorem pi2Circuits_real_rootsAt (hg : GraphsAgree) (h : IvChecked) :
    (pi2Circuits_real prog hprog hg h).rootsAt = RecGraph.Emitted.rootsAt := rfl

end RecCompose

/-- info: 'RecCompose.realDeployment_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.realDeployment_real

/-- info: 'RecCompose.pi2Circuits_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Circuits_real

/-- info: 'RecCompose.pi2ViewChecked_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2ViewChecked_real
