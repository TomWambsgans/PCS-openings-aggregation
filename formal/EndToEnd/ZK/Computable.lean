-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The audit `computationalAxioms` is `formal/Compose/Compose/DecoderAxioms.lean`'s (this repository),
-- restated here (that library is not built in this workspace).
import ZK.Final
import ZK.ProverBridge
import ZK.ComputableFacts

/-!
# The end theorem's simulator, compiled

The zero-knowledge end theorems (`zeroKnowledge_deployed_final`, `zeroKnowledge_deployed_whir`) name
the simulator `zkSimulator (fun _ ↦ deployedPub deployedRep) (fun stmt ↦ deployedSimV deployedRep P₀D
(stmtWD stmt) F192.Y R inKD sigmaAtD) skel fmt`, whose view simulator `deployedSimV` is
`noncomputable` (the openings `openW`, `openQ`, the renderer `out`, the parameters `P₀D`, the
wiring value `sigmaAtD = P₀D.sigmaPoly.eval`). Here:

* **`deployedSimVc R`**: the view simulator as a compiled definition (`Compiled.jointSimVm` read
  through `Compiled.outP`, at the public evaluations `peD`, the statement's target `tgtD`, the wiring
  value `sigmaAtC`), **equal to `deployedSimV … R inKD sigmaAtD`** (`deployedSimVc_eq`);
* **`Render.whirRendererC`**: WHIR's honest renderer, compiled (`whirRendererC_eq`);
* **`zkSimulatorC`**: the end theorem's simulator with both, **equal to the named one**
  (`zkSimulatorC_eq`);
* **the end theorems restated with it**: `zeroKnowledge_deployed_final_computable` (any renderer
  `R`; the simulator is compiled when `R` is) and **`zeroKnowledge_deployed_computable`**
  (`zeroKnowledge_deployed_whir` at the deployed instance, its facts discharged as
  `zeroKnowledge_deployed_final` discharges them; `CoreWhir`, `hnone`, the prover's budget named;
  the simulator `zkSimulatorC`);
* **the audit** (`#computational_axioms`): every constant `zkSimulatorDeployed` (`zkSimulatorC` at
  the global instances) reaches outside proofs and types is followed through its definition; no axiom
  is reached (`Classical.choice` appears only in proofs), and no constant outside Lean's core whose
  compiled code is not its definition. Being a `def` (not `noncomputable`), it is compiled.

## The simulator and its cost

`zkSimulatorC stmtBytes idW idσ idQ rowsW stmt` is `rpmSimulator` (`ZK/Simulator.lean`) at the public
part `deployedPub deployedRep` (`n = nRaw = 394` challenges; when each secret table is committed; the
opened positions `slotsW`, `slotsQ` of the challenges), the view simulator `deployedSimVc`, the skeleton
`skelSetup` and the proof's format `fmt`. Counted in operations of `K = GF(2^64)` and `E = GF(2^192)`
(an `E` product is a few dozen `K` products), on a run:

1. **The challenges**: `394` uniform draws.
2. **The view** (`deployedSimVc`, once): the challenges' decoding (`chOf`, `O(400)`); **`σ(t)`**
   (`sigmaAtC`: `3 · 2^24` products in `E`, `2 · 24 · 2^24` additions in `K`); the four values (`4`
   draws); the two paddings (`40 · 2^19 + 63 · 2^22` uniform words of `K`); **the two tables**
   (`solW`, `solQ`: the Gaussian elimination of `Instance/Builder.lean`, `O(k·(4·10^3 m + r² + r 2^r))`
   for a scan of `k` entries, `k = 6` and `9` at the generic challenge, at most
   `6 + 40·2^19`, `9 + 63·2^22`; the quotient values read `v_rows(t)`, `2^22` products, and
   `pub(γ)(t)`, `2·10^3`); **the two level-0 views** (`viewW`, `viewQ`, stored once in arrays):
   the encoding's table (`ℓ²` operations per opened position, `ℓ = 19, 22`; `224`, `225` positions),
   the six lane rounds (each `2^(ℓ+6)` reads of the batched weight and of the stack, a read of the
   weight `|ι|·6` comparisons and `m + 1 ≤ 3` claim weights of `Layout.claimW`, about `4·10^3` and
   `7·10^3` operations), the folded table (`2^ℓ · |ι|` products), the opened rows
   (`|Q|·|ι|·2^ℓ` reads of the encoding, at most `ℓ` products each; `|ι| = 40, 63`). The total is
   dominated by the lane rounds' weights: about `6 · 2^25 · 2 · 8·10^3 ≈ 3·10^12` (witness) and
   `6 · 2^28 · 2 · 2·10^4 ≈ 7·10^13` (quotient) operations, then the opened rows (`≈ 10^11`,
   `≈ 1.3·10^12`).
3. **The messages** (`outP`, at each of the `394` steps the skeleton reads): the claims' bytes
   (`claimMsgP`; at step `242` one `v_rows(t)`, `2^22` products) and the renderer's message
   (`whirRendererC`): WHIR's honest prover, the script run from the opening's start up to the step,
   on the stored view (arrays read, no recomputation of the view): at most one honest WHIR opening of
   the witness (`2^25` words), the wiring (`2^24`) or the quotient table (`2^28`) per step.
4. **The skeleton** (`skelSetup`): at most `2^24 + 2^70` operations (`skelSetup_queryBound`; the
   worst-case grinding counted, `2^17` expected tries a grind), each a cache lookup, a programmed
   answer or a uniform digest.
5. **The format** (`fmt`): at most `2^23` permutation calls (`fmt_queryBound`), each one step of the
   two-oracle simulator `S₂`; then per distinguisher query one step of `S₂`.

No step reads the witness; none calls a real permutation.
-/

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open LeanVM.Parameters Primitives
open scoped ENNReal

/-! ## WHIR's honest renderer, compiled -/

namespace PcsQuotient.EndToEnd.Render

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete
open QuotientZk.Deployed (Item)

variable (rep : QuotientZk.Instance.Rep K E)

/-- `word0W`, compiled. -/
def word0Wc (h : List Out) (va : JV K E) : Word := fun p ↦
  leafWords (va.2.2.1.2.2 (slotOf 20 224 (drawsW (chOf rep.limbs h)) p))

/-- `word0Q`, compiled. -/
def word0Qc (h : List Out) (va : JV K E) : Word := fun p ↦
  leafWords (va.2.2.2.2.2 (slotOf 23 225 (drawsQ (chOf rep.limbs h)) p))

/-- `word0σ`, compiled. -/
def word0σc : Word :=
  stackWordFast (cellVars logRows) 1 (membership logRows).wiringTable

/-- **WHIR's honest renderer, compiled** (`whirRenderer`). -/
def whirRendererC (stmt : Statement) : Renderer K E := fun k h va ↦
  if k = 4 then [.scalars ((List.ofFn va.1.1 ++ [va.1.2]).map limbsOf)]
  else
    match chainClaims stmt h va.1 with
    | none => []
    | some cl =>
      if 6 ≤ k ∧ k < 128 then
        openingMsg (QuotientZk.Deployed.witnessShape default)
          (hybridScript (witnessLayout logRows) [cl.witness] (laneAt va.2.2.1.1)
            (Array.ofFn va.2.2.1.2.1))
          (word0Wc rep h va) (h.drop 5)
      else if 129 ≤ k ∧ k < 242 then
        openingMsg (QuotientZk.Deployed.wiringShape default [])
          (openingScript (wiringLayout logRows) (membership logRows).wiringTable [cl.wiring])
          word0σc (h.drop 128)
      else if 243 ≤ k ∧ k < 394 then
        openingMsg (QuotientZk.Deployed.quotientShape default)
          (hybridScript (quotientLayout logRows) [cl.quotient, cl.sum] (laneAt va.2.2.2.1)
            (Array.ofFn va.2.2.2.2.1))
          (word0Qc rep h va) (h.drop 242)
      else []

/-- **The compiled renderer is WHIR's honest renderer**: the same program, the leaf images read by
the compiled copies (case on the chain's claims; nothing is evaluated). -/
theorem whirRendererC_eq (stmt : Statement) : whirRendererC rep stmt = whirRenderer rep stmt := by
  funext k h va
  rw [whirRendererC.eq_1, whirRenderer.eq_1]
  rcases hc : chainClaims stmt h va.1 with _ | cl
  · simp only
  · simp only
    rfl

end PcsQuotient.EndToEnd.Render

namespace PcsQuotient.EndToEnd

set_option linter.unusedSectionVars false

/-! ## The view simulator and the simulator -/

section Sim

variable [Fintype E] [SampleableType K] [SampleableType E]

/-- **The deployed view simulator, compiled**: the joint view simulator `jointSimVm` at the challenges
the answers give, read through the public renderer `outP` with the renderer `R`; the reduction's
parameters only through their public evaluations `peD`, the statement through its target
`tgtD stmt`, the wiring value `sigmaAtC`. -/
def deployedSimVc (R : Renderer K E) (stmt : Statement) :
    List Out → ProbComp (QuotientZk.View Msg Inp Tbl Pos) :=
  fun σ ↦ Compiled.outP deployedRep peD (tgtD stmt) F192.Y R σ <$>
    Compiled.jointSimVm deployedRep peD (tgtD stmt) F192.Y inKD sigmaAtC (chOf deployedRep.limbs σ)

/-- **`deployedSimVc` is the end theorem's view simulator.** -/
theorem deployedSimVc_eq (R : Renderer K E) (stmt : Statement) :
    deployedSimVc R stmt = deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y R inKD sigmaAtD := by
  funext σ
  have hs : sigmaAtC = sigmaAtD := funext sigmaAtC_eq
  have hj := Compiled.jointSimVm_eq (P := P₀D) deployedRep peD_matches (stmt := stmtWD stmt)
    (tgtD_eq stmt) F192.Y inKD sigmaAtC (chOf deployedRep.limbs σ)
  have ho : Compiled.outP deployedRep peD (tgtD stmt) F192.Y R σ =
      out deployedRep P₀D 0 0 (stmtWD stmt) F192.Y (fun _ _ _ ↦ 0) (fun _ _ _ _ ↦ 0) R σ :=
    funext fun v ↦ Compiled.outP_eq deployedRep peD_matches (tgtD_eq stmt) F192.Y R 0 0 _ _ σ v
  rw [deployedSimVc.eq_1,
    deployedSimV.eq_1 deployedRep P₀D (stmtWD stmt) F192.Y R inKD sigmaAtD σ, hj, ho, hs]

/-- **The end theorem's simulator, compiled**: `zkSimulator` at the deployed public part, the
compiled view simulator with WHIR's honest renderer (compiled), the skeleton `skelSetup` and the
format `fmt`. Its cost is the module's (`ZK/Computable.lean`, "The simulator and its cost"). -/
def zkSimulatorC (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) : Statement → StateT RpmSimState ProbComp (Option Proof) :=
  zkSimulator (fun _ ↦ deployedPub deployedRep)
    (fun stmt ↦ deployedSimVc (Render.whirRendererC deployedRep stmt) stmt)
    (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt

/-- **`zkSimulatorC` is the simulator the end theorem names** (with WHIR's honest renderer). -/
theorem zkSimulatorC_eq (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) :
    zkSimulatorC stmtBytes idW idσ idQ rowsW =
      zkSimulator (fun _ ↦ deployedPub deployedRep)
        (fun stmt ↦ deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y
          (Render.whirRenderer deployedRep stmt) inKD sigmaAtD)
        (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt := by
  simp only [zkSimulatorC, deployedSimVc_eq, Render.whirRendererC_eq]

end Sim

/-! ## The end theorems with the compiled simulator -/

/-- **Zero knowledge of the membership proof, the deployed instance plugged in, the simulator
compiled**: `zeroKnowledge_deployed_final` with its simulator's view simulator `deployedSimV …`
replaced by the compiled `deployedSimVc R` (`deployedSimVc_eq`). -/
theorem zeroKnowledge_deployed_final_computable (R : Renderer K E)
    (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (Qp : ℕ) (εR : ℕ → ℝ≥0∞) (s₀ : RpmSimState)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (deployedJD R stmt w).P keccak256OverPermutation
        queryPermutation (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost Qp)
    (hbridge : ∀ stmt w, Relation stmt w →
      ProverBridge stmt w (deployedJD R stmt w).P (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)
        (fmt stmt) (decodeCoins ∘ eD) εR) :
    ZeroKnowledgeWith s₀
      (zkSimulator (fun _ ↦ deployedPub deployedRep) (fun stmt ↦ deployedSimVc R stmt)
        (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt)
      rpmSimOracle (zkBoundEnd Qp fmtBudget εR) := by
  have h := zeroKnowledge_deployed_final R stmtBytes idW idσ idQ rowsW hrows Qp εR s₀ hprover hbridge
  rwa [show (fun stmt ↦ deployedSimVc R stmt) =
      fun stmt ↦ deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y R inKD sigmaAtD from
    funext fun stmt ↦ deployedSimVc_eq R stmt]

/-- **Zero knowledge of the membership proof, WHIR's honest prover as the renderer, the deployed
instance plugged in, the simulator compiled**: `zeroKnowledge_deployed_whir` at the deployed
fields, instance, tables and coins (every hypothesis of the field, of F1, of the simulator's public
functions and of the honest tables' claims discharged as in `zeroKnowledge_deployed_final`), its
simulator `zkSimulatorC` (`zkSimulatorC_eq`). **Named**: the prover's permutation budget `Qp`
(`hprover`), `CoreWhir` (`hcore`) and the probability `δ` that the statement's prover makes no
proof (`hnone`). `ζ Q = δ + 2^-113 + epsHV + … ≤ δ + 2^-113 + 2^-165 + 2^-2200 + (Qp + 2^23 + Q)² /
2^508` for `Q ≤ 2^126`. -/
theorem zeroKnowledge_deployed_computable
    (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (Qp : ℕ) (δ : ℝ≥0∞) (s₀ : RpmSimState)
    (hprover : ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ
          (deployedJD (Render.whirRenderer deployedRep stmt) stmt w).P
        keccak256OverPermutation queryPermutation (QuotientZk.DRpm.coinR KSt)
        (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost Qp)
    (hcore : ∀ stmt w, Relation stmt w →
      CoreWhir deployedRep P₀D (stmtWD stmt) F192.Y (gKD w) vanD (TWD w) (TQD w) stmt w
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW) (decodeCoins ∘ eD))
    (hnone : ∀ stmt w, Relation stmt w → ∀ s, noneProb stmt w ((decodeCoins ∘ eD) s) ≤ δ) :
    ZeroKnowledgeWith s₀ (zkSimulatorC stmtBytes idW idσ idQ rowsW) rpmSimOracle
      (zkBoundEnd Qp fmtBudget fun _ ↦ δ) := by
  rw [zkSimulatorC_eq]
  exact zeroKnowledge_deployed_whir deployedRep P₀D F192.Y inKD sigmaAtD stmtWD (fun _ w ↦ gKD w)
    (fun _ _ ↦ vanD) (fun _ w ↦ TWD w) (fun _ w ↦ TQD w) finrank_KE card_E card_K linIndep_Y hED hND
    (fun _ _ _ ↦ hvanD) (fun stmt w hw ↦ hsatD stmt w hw) (fun _ _ _ ↦ hvan0D) (fun _ _ _ ↦ hdegD)
    inKD_iff (fun _ ↦ rfl) (fun _ w _ ↦ hTWD w) (fun stmt w hw ↦ hTQD stmt w hw) stmtBytes idW idσ
    idQ rowsW hrows eD eD_bijective Qp δ s₀ hprover hcore hnone

/-- **The compiled simulator at the deployed (global) instances**, the definition the audit below
reads. -/
def zkSimulatorDeployed (stmtBytes : Statement → Vector UInt8 64)
    (idW idσ idQ : QuotientRpm.Bytes32) (rowsW : List (List UInt8)) :
    Statement → StateT RpmSimState ProbComp (Option Proof) :=
  zkSimulatorC stmtBytes idW idσ idQ rowsW

end PcsQuotient.EndToEnd

/-! ## The audit: what the compiled simulator computes with -/

namespace PcsQuotient.EndToEnd.Audit

open Lean Meta Elab Command

/-- Whether a constant comes from Lean's core library. -/
def isCore (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`Init).isPrefixOf m || (`Std).isPrefixOf m || (`Lean).isPrefixOf m
  | none => false

/-- The constants a term mentions outside proofs and types (the positions the compiler erases). -/
def computationalConsts (v : Expr) : MetaM (Array Name) := do
  let ref ← IO.mkRef (#[] : Array Name)
  let _ ← Meta.transform v (pre := fun e => do
    if e.isSort then return .done e
    if (← isProof e) || (← isType e) || (← isTypeFormer e) then return .done e
    if let .const n _ := e then ref.modify (·.push n)
    return .continue)
  ref.get

/-- **The computational axioms of a definition**: the axioms reached from its value through
computational positions only, following every definition and `opaque`; the non-core constants
reached whose compiled code is not their definition (`implemented_by`, `extern`, `opaque`); the
non-core constants reached that are marked `noncomputable`. -/
partial def computationalAxioms (root : Name) :
    MetaM (Array Name × Array Name × Array Name × Nat) := do
  let env ← getEnv
  let mut todo : Array Name := #[root]
  let mut seen : NameSet := {}
  let mut axs : Array Name := #[]
  let mut special : Array Name := #[]
  let mut nc : Array Name := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | continue
    let core := isCore env n
    if !core && ((Compiler.getImplementedBy? env n).isSome || isExtern env n) then
      special := special.push n
    if !core && isNoncomputable env n then nc := nc.push n
    match info with
    | .axiomInfo _ => axs := axs.push n
    | .defnInfo v =>
      for c in ← computationalConsts v.value do
        unless seen.contains c do todo := todo.push c
    | .opaqueInfo v =>
      unless core do special := special.push n
      for c in ← computationalConsts v.value do
        unless seen.contains c do todo := todo.push c
    | _ => pure ()
  return (axs, special, nc, seen.size)

/-- Print the computational audit of a definition. -/
elab "#computational_axioms " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let (axs, special, nc, _) ← withOptions (fun o => maxRecDepth.set o 100000) <|
    computationalAxioms n
  logInfo m!"{n}: computational axioms {axs.toList}, non-core implemented_by/extern/opaque \
    {special.toList}, non-core noncomputable {nc.toList}"

end PcsQuotient.EndToEnd.Audit

/-! ## Axioms and the audit -/

/--
info: 'PcsQuotient.EndToEnd.deployedSimVc_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.deployedSimVc_eq

/--
info: 'PcsQuotient.EndToEnd.Render.whirRendererC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.Render.whirRendererC_eq

/--
info: 'PcsQuotient.EndToEnd.zkSimulatorC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zkSimulatorC_eq

/--
info: 'PcsQuotient.EndToEnd.zeroKnowledge_deployed_final_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed_final_computable

/--
info: 'PcsQuotient.EndToEnd.zeroKnowledge_deployed_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed_computable

/--
info: PcsQuotient.EndToEnd.zkSimulatorDeployed: computational axioms [], non-core implemented_by/extern/opaque [], non-core noncomputable []
-/
#guard_msgs (whitespace := lax) in
#computational_axioms PcsQuotient.EndToEnd.zkSimulatorDeployed

/--
info: PcsQuotient.EndToEnd.Render.whirRendererC: computational axioms [], non-core implemented_by/extern/opaque [], non-core noncomputable []
-/
#guard_msgs (whitespace := lax) in
#computational_axioms PcsQuotient.EndToEnd.Render.whirRendererC
