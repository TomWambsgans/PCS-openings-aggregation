-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The Fiat–Shamir layer's form is
-- `formal/UniSound/UniSound/Fs128.lean`'s `FsLayer128` (every round-by-round sound protocol on the rounds, its first state
-- the relation of round `0`'s candidate, its last following from the verifier's checks with true claims); the protocol
-- is `formal/RecPiop`'s `piop`, the verifier's arithmetic `formal/RecStatement`'s `checks_claims_iff_post2`.
import RecCompose.Part1
import RecCompose.Numbers
import RecStatement.Lemmas.Main
import RecPiop
import UniSound.FsChain
import UniComplete.DomainBasis

/-!
# π2's extraction from its layers

`Pi2Layers.extraction` (`Pi2Extraction`: if the contract accepts, a candidate of `W`'s committed word satisfies the
compiled circuit's relation, but with probability `ε2 Q`) refined into the layers that give it:

* **`Pi2FsLayer D`** (the Fiat–Shamir layer and the openings; **open, `lean-rec-compose`**): for every round-by-round
  sound protocol on π2's rounds (`RecPiop.pi2Rounds 4`: `W`'s root then `α, β, γ`; `Q`'s root then `t`; the fold values
  and `ξ` then `ρ`), its errors times the lists of the roots before them at most `e`, whose state before round `0` is a
  property `P` of `W`'s candidate and whose last state follows from π2's checks (`all ≠ 0`) with the four claims true on
  the candidates (`Pi2ClaimsHold`), π2's experiment accepts while no candidate of `W` (as π2's extractor lists them) has
  `P`, with probability at most `pi2BoundE e Q`. It is `UniSound.FsLayer128` for π2: its proof is the port of
  `UniSound/{Fs128, FsGame128, FsFinal128}.lean` (and the bridges `FsCouple`, `FsVerifier`, `FsWalk*`, `FsExtract`,
  `FsSetup`) to π2's transcript, through `Compose.knowledgeSoundness_listChainU_closed128` (π2's three rounds),
  `Compose.prEvent_doomF_le` at `WhirBridge.largeShapes` (`W` of `2^24` words, the setup `2^25`, `Q` `2^28`, once per
  fresh query) and `Compose.prEvent_pairTr_le` (π2's seed `name ‖ iv ‖ input`).
* **`Pi2Tables D C`** (the tables' layer; **open, `lean-rec-compose`**): what the candidates stand for (`RecPiop.Model`:
  `W`'s polynomial, which takes the candidate's witness values on `V_m`, and its true fold values; `Q`'s `h`, `q`; the
  setup's `σ`, `κ`), and the claims on the candidates as the model's values (`checks_claims_iff_post2`'s left side).
* **`Pi2Facts D C`** (the circuit's facts, established by the compiler's checks and tests, `RecCircuitTest/Main.lean`,
  `RecStatementTest/Runner.lean`; `SpecOf` by `RecStatement.Lemmas.SpecLink` and the circuit compiler, `lean-rec-statement`
  and `lean-rec-circuit`): `SpecOf` of π2's verifier's constants and the compiled circuit, the circuit valid, its shape
  (`2^24` positions, rows of `16`), the four-limb ports three, the public limbs in `K`.

**Proved** (`pi2Extraction_of_layers`): from them, `Pi2Extraction D (the compiled circuit's relation) pi2Bound`. The
protocol is `RecPiop.piop` at each setup's circuit (`pi2Piop`): its errors are `pi2_rounds_le`'s, the copy argument's
binding `hbind` is `RecPiop.Circuit.bind_elem`/`bind_root` (`d_j = 0` for three limbs, `1` for four, read off the
compiler's checked ports: `limbs_toPiop`; `1, Y, Y²` independent over `K`: `indep_K`), its last state from the checks
by `RecStatement.checks_claims_iff_post2`, and its first state is the circuit's relation for the candidate's witness
(`satisfies_congr`). `pi2Layers_of` assembles `Pi2Layers D pi2Bound`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash Finset
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## The candidates, the statement, the chain's rounds -/

/-- A candidate: a stack, as its words. -/
abbrev Stk : Type := ℕ → K

/-- π2's PIOP statement: the public input and π2's public scalars (the statement's four words, π1's roots' halves and
claims' elements). -/
abbrev Pi2St : Type := Vector UInt8 32 × List E

/-- A decoded stack as its words. -/
def stkOf {n : ℕ} (w : Vector K n) : Stk := fun j ↦ w.toArray.getD j 0

/-- **A stack's witness values** `w(ω_i)` (its table read back through `W`'s layout, `basisValue` in the `B` basis). -/
def witnessOfStk (D : RecDeployment) (roots : RecSetupRoots) (c : Stk) : ℕ → K :=
  let cc := (D.circuitAt roots.pi1).circuit
  let table := Array.ofFn (n := 2 ^ cc.logN) fun i ↦ (wLayout D roots).readEntry c i.val
  fun i ↦ UniStatement.basisValue table cc.logN i

theorem witnessOf_eq (D : RecDeployment) (roots : RecSetupRoots) (w : Vector K (2 ^ (wLayout D roots).logN)) :
    witnessOf D roots w = witnessOfStk D roots (stkOf w) := rfl

/-- **π2's public scalars from the calldata** (π2's run over Keccak-f[1600], any IV: they are the stream's public data,
read before any hash). -/
def pi2Scalars (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) :
    List E :=
  match (run (Spec.of (D.circuitAt roots.pi1).circuit) [] input.toList stream).result with
  | .ok r => r.scalars
  | .error _ => []

/-- π2's statement of an outcome. -/
def pi2StmtOf (D : RecDeployment) (z : RecOutcome2) : Pi2St := (inp z, pi2Scalars D (rts z) (inp z) (prf z).stream)

/-- The statement's bytes: a zero byte, the public input, the scalars (an odd length: never a chain step's input). -/
def pi2Label (s : Pi2St) : List UInt8 := 0 :: (s.1.toList ++ UniSound.scalars24 s.2)

theorem pi2Label_injective : Function.Injective pi2Label := by
  rintro ⟨a, l⟩ ⟨a', l'⟩ h
  simp only [pi2Label, List.cons.injEq, true_and] at h
  have ha : a.toList = a'.toList := by
    have := congrArg (List.take 32) h
    rwa [List.take_append_of_le_length (by simp), List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp), List.take_of_length_le (by simp)] at this
  have hl : UniSound.scalars24 l = UniSound.scalars24 l' := by
    rw [ha] at h
    exact List.append_cancel_left h
  have hlen : l.length = l'.length := by
    have := congrArg List.length hl
    rw [UniSound.length_scalars24, UniSound.length_scalars24] at this
    omega
  rw [Vector.toList_inj.mp ha, UniSound.scalars24_inj hlen hl]

/-- **π2's rounds as a chain** (`Compose.ChainSpec`): the field's limbs, the statement's label, `RecPiop.pi2Rounds 4`
(rows of `16`). -/
def pi2K : Compose.ChainSpec E Pi2St where
  lim := UniSound.uLimbs
  label := pi2Label
  label_injective := pi2Label_injective
  label_len s := by
    simp only [pi2Label, List.length_cons, List.length_append, Vector.length_toList, UniSound.length_scalars24]
    omega
  rounds := RecPiop.pi2Rounds 4

/-- The lists of the roots before round `j` (`Compose.facL`): `L_W` for round `0`, `L_W L_Q` after. -/
def pi2Fac (j : ℕ) : ℕ := if j = 0 then 9952 else 9952 * 3564

/-! ## The claims on the candidates -/

/-- **A claim holds of a stack under a layout**: the table the layout reads off the stack (`readEntry`) has, at the
point, the multilinear extension the value (`opening::Claim`; `eqBits`, the first coordinate the lowest bit). -/
def ClaimOn (L : PcsQuotient.Layout) (stack : Stk) (c : List E × E) : Prop :=
  ∑ i ∈ range (2 ^ L.vars), PcsQuotient.eqBits c.1 i * ofK (L.readEntry stack i) = c.2

/-- **π2's four claims hold of the candidates**, for the run's inputs at the setup's roots: `W`'s (its fold at `ρ`) of
`cW`, `Q`'s two (the combination at `t`, `h`'s top coefficient) of `cQ`, the setup's (at `β`, value `ξ`) of the setup's
table (`Pi2Circuit.setupStack`). -/
def Pi2ClaimsHold (D : RecDeployment) (roots : RecSetupRoots) (inp : Inputs E) (cW cQ : Stk) : Prop :=
  let c := D.circuitAt roots.pi1
  let out := (Spec.of c.circuit).core.run inp
  ClaimOn (layoutsOf c.circuit.logN).1 cW (out.witnessPoint, out.fold) ∧
    ClaimOn (layoutsOf c.circuit.logN).2.1 cQ (out.quotientPoint, out.quotientValue) ∧
    ClaimOn (layoutsOf c.circuit.logN).2.1 cQ (out.sumPoint, out.sumValue) ∧
    ClaimOn (layoutsOf c.circuit.logN).2.2 (fun j ↦ c.setupStack.getD j 0) (out.setupPoint, inp.ξ)

/-- The opened transcript of a run's first two rounds, on the candidates `cW`, `cQ` (round `0`: `W`'s root, `α, β, γ`;
round `1`: `Q`'s root, `t`). -/
def pi2Opened (cW cQ : Stk) (inp : Inputs E) : Compose.Opened Stk E :=
  [((some cW, []), [inp.α, inp.β, inp.γ]), ((some cQ, []), [inp.t])]

/-! ## The Fiat–Shamir layer -/

/-- **π2's bound at the rounds' error `e`** (`pi2Bound`'s form): the openings once, the chain, the seed's pair, the
permutation. -/
noncomputable def pi2BoundE (e : ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  (pi2N Q : ℝ≥0∞) * (269 * (2 : ℝ≥0∞)⁻¹ ^ 137 + ((5 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (pi2N Q : ℝ≥0∞) * (e + ((8 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((2 * pi2N Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

theorem pi2BoundE_roundErr (Q : ℕ) : pi2BoundE pi2RoundErr Q = pi2Bound Q := rfl

/-- **The Fiat–Shamir layer for π2** (open, `lean-rec-compose`): for every family, over the setup's roots, of
round-by-round sound protocols on π2's rounds, their errors times the lists of the roots before them at most `e`, whose
state before round `0` is a property `P` of `W`'s candidate and whose state after `ρ` follows from π2's check
(`all ≠ 0`, the contract's one) with the four claims true on the candidates, the contract accepts while no candidate of
`W`'s committed word (π2's extractor's list) has `P` with probability at most `pi2BoundE e Q`.

Its proof (to do, on this branch) is `UniSound.fsLayer128_holds`'s for π2's transcript: the chain
`Compose.ChainSpecU` over π2's encoding (the 24-byte scalars, the roots' reversed halves, the public data as round
`0`'s bytes before `W`'s root), `Compose.knowledgeSoundness_listChainU_closed128`, π2's three openings as `WhirOp`s on
π2's public layouts (`W` `2^24`, the setup `2^25`, `Q` `2^28`) bounded once (`Compose.prEvent_doomF_le_large`), the
seed's pair (`Compose.prEvent_pairTr_le`), and the bridges from `recSoundnessExperiment2` to the composed game (the
setup's four trees and π2's IV, the verifier as the chain, the extractor's decoders listing the chain's candidates). -/
def Pi2FsLayer (D : RecDeployment) : Prop :=
  ∀ (R : RecSetupRoots → Compose.Piop pi2K Stk) (e : ℝ≥0∞),
    (∀ roots, ∀ j < 3, (pi2Fac j : ℝ≥0∞) * (R roots).err j ≤ e) →
    ∀ (P : RecSetupRoots → Pi2St → Stk → Prop),
      (∀ roots s c m, (R roots).pre s [] (some c, m) → P roots s c) →
      (∀ roots (s : Pi2St) (cW cQ : Stk) (inp : Inputs E), inp.scalars = s.2 →
        inp.a.length = 2 ^ (Spec.of (D.circuitAt roots.pi1).circuit).core.logRow →
        ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).all ≠ 0 →
        Pi2ClaimsHold D roots inp cW cQ →
        (R roots).post s (pi2Opened cW cQ inp) (none, inp.a ++ [inp.ξ]) [inp.ρ]) →
      ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
        Pr{let z ← recSoundnessExperiment2 D A}[acc z = true ∧
          ¬ ∃ w ∈ outcomeCandidates D z, P (rts z) (pi2StmtOf D z) (stkOf w)] ≤ pi2BoundE e Q

/-! ## The compiled circuit and its facts -/

/-- **π2's circuit, as the Lean compiler builds it** from π1-rec3's recorded graph at every π1 IV (`Pi2Layers`'
`rootsAt`, `compiled`, `compile_ok`, `stream_eq`). -/
structure Pi2Circuits (D : RecDeployment) where
  rootsAt : List ℕ
  compiled : List UInt8 → RecCircuit.Compiled
  compile_ok : ∀ iv, RecCircuit.compile (RecCircuit.ofRG RecGraph.Pi1.pi1Graph rootsAt iv) = .ok (compiled iv)
  stream_eq : ∀ iv (w : ℕ → K),
    D.pi1Stream w = ((compiled iv).streamW (RecCircuit.ofRG RecGraph.Pi1.pi1Graph rootsAt iv) w).toArray

variable {D : RecDeployment}

/-- The compiled circuit at the setup's roots, as `RecPiop`'s (`RecCircuit.Circuit.toPiop`). -/
abbrev Pi2Circuits.G (C : Pi2Circuits D) (roots : RecSetupRoots) : RecPiop.Circuit E :=
  (C.compiled (D.pi1IvAt roots.pi1)).circuit.toPiop

/-- Port `j`'s binding count: `1` for a four-limb port (the statement, a root), `0` for three limbs. -/
def Pi2Circuits.d (C : Pi2Circuits D) (roots : RecSetupRoots) (j : ℕ) : ℕ :=
  if ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.getD j default).source.limbs = 4 then 1 else 0

/-- The subfield `K` of `E`. -/
abbrev subK : Subfield E := (algebraMap K E).fieldRange

/-- **The circuit's facts** (established, not proved here): `SpecOf` of π2's verifier's constants and the compiled
circuit on the Cantor basis `UniComplete.Domain.basisE` (`ω = pointE`), its pairs, ports and public limbs `pubOf`
(`RecStatement.Lemmas.SpecLink` proves `Spec::of`'s constants `SpecOf`'s, `lean-rec-statement`; that they are the
compiled circuit's is the compiler's, `lean-rec-circuit`, and the runners' comparison of the tables, compiled
evaluation); the circuit valid (`RecPiop.Circuit.validate`, the Rust's `validate` and `check_shape`); `2^24` positions,
rows of `16`; three four-limb ports (the statement, π1's two roots); every public limb in `K`, as many as the port's. -/
structure Pi2Facts (D : RecDeployment) (C : Pi2Circuits D) where
  pairOf : RecSetupRoots → ℕ → RecPiop.Block × ℕ
  portOf : RecSetupRoots → ℕ → ℕ
  nz : RecSetupRoots → ℕ
  pubOf : RecSetupRoots → List E → ℕ → List E
  spec : ∀ roots, SpecOf (Spec.of (D.circuitAt roots.pi1).circuit).core (C.G roots) UniComplete.Domain.basisE
    (pairOf roots) (portOf roots) (nz roots) (pubOf roots)
  valid : ∀ roots, (C.G roots).Valid
  logN : ∀ roots, (C.G roots).logN = 24
  logW : ∀ roots, (C.G roots).logW = 4
  four : ∀ roots, ∑ j ∈ range (C.G roots).nP, C.d roots j = 3
  pub_len : ∀ roots scalars, ∀ j < (C.G roots).nP, (pubOf roots scalars j).length = ((C.G roots).limbs j).length
  pub_K : ∀ roots scalars, ∀ j < (C.G roots).nP, ∀ x ∈ pubOf roots scalars j, x ∈ subK

/-- The points `ω_i` (`Heap.omega` of the Cantor basis, `pointE`). -/
noncomputable abbrev pi2Omega : ℕ → E := Heap.omega UniComplete.Domain.basisE

/-- **The tables' layer** (open, `lean-rec-compose`): for each setup, what the candidates stand for (`RecPiop.Model` of
the compiled circuit: `W`'s polynomial `wP c`, of degree below `N`, taking the candidate's witness values on `V_m`, and
its true fold values, the cells from them the row's cells `w(t + ω_x)`; `Q`'s `h` below `N` and `q` below `4N`; the
setup's `σ`, `κ`), and the claims, true on the candidates, as the model's values: `Q`'s two the identity's combination
`(1 + ρ') h(t) + ρ' q(t)` and `Σ_V h` the target, the setup's `ξ = κ(t) + β σ(t)`, `W`'s its true fold at `ρ`
(`RecStatement.checks_claims_iff_post2`'s left side; the claims' points are `run_u`, `run_digitsScale`, `RecPiop`'s
`sum_tablePoly_omega`). -/
structure Pi2Tables (D : RecDeployment) (C : Pi2Circuits D) where
  model : ∀ roots, RecPiop.Model (C.G roots) pi2Omega Stk
  witness_eval : ∀ roots (c : Stk), ∀ i < (C.G roots).N,
    ((model roots).wP c).eval (pi2Omega i) = ofK (witnessOfStk D roots c i)
  claims : ∀ roots (cW cQ : Stk) (inp : Inputs E),
    ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).all ≠ 0 → Pi2ClaimsHold D roots inp cW cQ →
      ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).combination =
          (1 + ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).rhoQ) * ((model roots).hP cQ).eval inp.t +
            ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).rhoQ * ((model roots).qP cQ).eval inp.t ∧
        ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).target =
          ∑ i ∈ range (C.G roots).N, ((model roots).hP cQ).eval (pi2Omega i) ∧
        inp.ξ = (model roots).setup.κP.eval inp.t + inp.β * (model roots).setup.σP.eval inp.t ∧
        ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).fold =
          RecPiop.foldAt (C.G roots).logW ((model roots).fold cW inp.t) inp.ρ

/-! ## Lemmas: congruence, the subfield, the ports' limbs -/

/-- **The relation reads the witness on `[0, N)` only.** -/
theorem satisfies_congr {G : RecPiop.Circuit E} (hV : G.Valid) {pub : ℕ → List E} {w w' : ℕ → E}
    (hw : ∀ i < G.N, w i = w' i) (h : G.Satisfies pub w) : G.Satisfies pub w' := by
  refine ⟨fun i hi hh ↦ ?_, fun j hj ↦ ?_⟩
  · rw [← hw _ (hV.sigma_inside i hi hh).1, h.copy i hi hh]
    exact G.push_congr_off_holes hV (fun j hj _ ↦ hw j hj) 0 hi
  · rw [← h.ports j hj]
    unfold RecPiop.Circuit.limbVals
    refine List.map_congr_left fun l hl ↦ (hw _ ?_).symm
    have hp := G.port_lt hV hj
    refine G.base_add_lt hV hp.1 (G.role_reads_lt hV (i := G.port j) ?_)
    unfold RecPiop.Circuit.limbs at hl
    cases hr : G.role (G.port j) with
    | port ls =>
      rw [hr] at hl
      rw [RecPiop.Role.reads]
      exact List.mem_map.mpr ⟨l, hl, rfl⟩
    | forward => rw [hr] at hl; simp at hl
    | expr p => rw [hr] at hl; simp at hl

/-- **`1, Y, Y²` are independent over `K`** (`E = K[Y]`, `Y³ = Y + 1`). -/
theorem indep_K : RecPiop.Indep subK Primitives.F192.Y := by
  intro a ha b hb c hc h
  obtain ⟨a', rfl⟩ := RingHom.mem_fieldRange.mp ha
  obtain ⟨b', rfl⟩ := RingHom.mem_fieldRange.mp hb
  obtain ⟨c', rfl⟩ := RingHom.mem_fieldRange.mp hc
  have e : Primitives.F192.ofLimbs a' b' c' = 0 := by
    rw [Primitives.F192.ofLimbs_eq, ← Primitives.F192.ofF64_eq_algebraMap, ← Primitives.F192.ofF64_eq_algebraMap,
      ← Primitives.F192.ofF64_eq_algebraMap] at *
    rw [← h]
    ring
  have h0 := congrArg (fun x : Primitives.F192 ↦ x.limb 0) e
  have h1 := congrArg (fun x : Primitives.F192 ↦ x.limb 1) e
  have h2 := congrArg (fun x : Primitives.F192 ↦ x.limb 2) e
  simp only [Primitives.F192.limb_ofLimbs_zero, Primitives.F192.limb_ofLimbs_one,
    Primitives.F192.limb_ofLimbs_two, Primitives.F192.limb_zero] at h0 h1 h2
  subst h0 h1 h2
  simp

/-- **The compiled circuit's port `J` has the compiler's limbs**, weighted as `PI2.md` §4.2: `[0, 1, 2]` (an element,
a zero check, a padding port) or `[0, 1, 2, 3]` (the statement, a root) (`portsOk`). -/
theorem limbs_toPiop {r : RecCircuit.Recorded} {c : RecCircuit.Compiled} (hc : RecCircuit.compile r = .ok c)
    {J : ℕ} (hJ : J < c.circuit.toPiop.nP) :
    c.circuit.toPiop.limbs J = RecCircuit.portWeights (List.range (c.circuit.ports.getD J default).source.limbs) := by
  have hck := RecCircuit.Compiled.checked_of_compile hc
  have hsz : J < c.circuit.ports.size := by
    simpa [RecPiop.Circuit.nP, RecCircuit.Circuit.toPiop] using hJ
  have hparts := RecCircuit.Compiled.portsOk_parts hck.ports J hsz
  have hport : c.circuit.toPiop.port J = (c.circuit.ports.getD J default).position := by
    simp only [RecPiop.Circuit.port, RecCircuit.Circuit.toPiop, List.getD_eq_getElem?_getD,
      Array.getD_eq_getD_getElem?, List.getElem?_map, Array.getElem?_toList]
    rw [Array.getElem?_eq_getElem hsz]
    rfl
  unfold RecPiop.Circuit.limbs
  rw [hport, RecCircuit.toPiop_role, hparts.2.1]
  rfl

theorem source_limbs (s : RecCircuit.Source) : s.limbs = 3 ∨ s.limbs = 4 := by
  cases s <;> simp [RecCircuit.Source.limbs]

/-- **The copy argument's binding**: a port's limbs that are not the public ones agree on at most `d_j` of the `γ`s
(`0` for three limbs, `1` for four), for limbs in `K` (`RecPiop.Circuit.bind_elem`, `bind_root`). -/
theorem hbind_of (C : Pi2Circuits D) (Fa : Pi2Facts D C) (T : Pi2Tables D C) (roots : RecSetupRoots)
    (s : Pi2St) (c : Stk) :
    ∀ j < (C.G roots).nP,
      (C.G roots).limbVals (fun i ↦ ((T.model roots).wP c).eval (pi2Omega i)) j ≠ Fa.pubOf roots s.2 j →
      (univ.filter fun γ : E ↦ (C.G roots).push (fun i ↦ ((T.model roots).wP c).eval (pi2Omega i)) γ
        ((C.G roots).port j) = (C.G roots).pubFp γ (Fa.pubOf roots s.2) j).card ≤ C.d roots j := by
  intro j hj hne
  have hV := Fa.valid roots
  have hl := limbs_toPiop (C.compile_ok (D.pi1IvAt roots.pi1)) hj
  have hwK : ∀ x ∈ (C.G roots).limbVals (fun i ↦ ((T.model roots).wP c).eval (pi2Omega i)) j, x ∈ subK := by
    intro x hx
    unfold RecPiop.Circuit.limbVals at hx
    obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hx
    have hp := (C.G roots).port_lt hV hj
    have hlt : (C.G roots).base ((C.G roots).port j) + l.cell < (C.G roots).N := by
      refine (C.G roots).base_add_lt hV hp.1 ((C.G roots).role_reads_lt hV (i := (C.G roots).port j) ?_)
      unfold RecPiop.Circuit.limbs at hl'
      cases hr : (C.G roots).role ((C.G roots).port j) with
      | port ls =>
        rw [hr] at hl'
        rw [RecPiop.Role.reads]
        exact List.mem_map.mpr ⟨l, hl', rfl⟩
      | forward => rw [hr] at hl'; simp at hl'
      | expr p => rw [hr] at hl'; simp at hl'
    simp only
    rw [T.witness_eval roots c _ hlt]
    exact RingHom.mem_fieldRange.mpr ⟨_, rfl⟩
  have hpK := Fa.pub_K roots s.2 j hj
  have hpl := Fa.pub_len roots s.2 j hj
  unfold Pi2Circuits.d
  rcases source_limbs ((C.compiled (D.pi1IvAt roots.pi1)).circuit.ports.getD j default).source with h3 | h4
  · have e3 : List.range 3 = [0, 1, 2] := rfl
    rw [h3, e3] at hl
    have hl' : (C.G roots).limbs j = RecPiop.elemLimbs 0 1 2 Primitives.F192.Y := hl
    rw [ite_eq_right (by omega)]
    exact RecPiop.Circuit.bind_elem hV indep_K hj hl' _ _ hwK hpK (by rw [hpl, hl']; rfl) hne
  · have e4 : List.range 4 = [0, 1, 2, 3] := rfl
    rw [h4, e4] at hl
    have hl' : (C.G roots).limbs j = RecPiop.rootLimbs 0 1 2 3 Primitives.F192.Y := hl
    rw [ite_eq_left h4]
    exact RecPiop.Circuit.bind_root hV indep_K hj hl' _ _ hwK hpK (by rw [hpl, hl']; rfl) hne

/-! ## The protocol -/

theorem pi2K_rounds (C : Pi2Circuits D) (Fa : Pi2Facts D C) (roots : RecSetupRoots) :
    pi2K.rounds = RecPiop.pi2Rounds (C.G roots).logW := by
  rw [Fa.logW roots]
  rfl

/-- **π2's PIOP at the setup's circuit** (`RecPiop.piop`): the compiled circuit, its points, the tables' model, the
public limbs of the statement's scalars, the ports' binding. -/
noncomputable def pi2Piop (C : Pi2Circuits D) (Fa : Pi2Facts D C) (T : Pi2Tables D C) (roots : RecSetupRoots) :
    Compose.Piop pi2K Stk :=
  RecPiop.piop (T.model roots) (fun s ↦ Fa.pubOf roots s.2) pi2K (pi2K_rounds C Fa roots) (Fa.valid roots)
    (RecPiop.Points.ofCantor UniComplete.Domain.basisE) (by rw [Fa.logN roots]; norm_num) (C.d roots)
    (fun s c ↦ hbind_of C Fa T roots s c)

theorem pi2Piop_err (C : Pi2Circuits D) (Fa : Pi2Facts D C) (T : Pi2Tables D C) (roots : RecSetupRoots) :
    ∀ j < 3, (pi2Fac j : ℝ≥0∞) * (pi2Piop C Fa T roots).err j ≤ pi2RoundErr := by
  intro j hj
  obtain ⟨h0, h1, h2⟩ := pi2_rounds_le (C.G roots) (Fa.logN roots) (Fa.logW roots) (C.d roots) (Fa.four roots)
  show (pi2Fac j : ℝ≥0∞) * RecPiop.err (C.G roots) (C.d roots) j ≤ pi2RoundErr
  interval_cases j
  · exact h0
  · exact h1
  · exact h2

/-- **The protocol's first state is the circuit's relation** of the candidate's witness values. -/
theorem pi2Piop_pre (C : Pi2Circuits D) (Fa : Pi2Facts D C) (T : Pi2Tables D C) (roots : RecSetupRoots)
    (s : Pi2St) (c : Stk) (m : List E) (h : (pi2Piop C Fa T roots).pre s [] (some c, m)) :
    (C.G roots).Satisfies (Fa.pubOf roots s.2) (RecCircuit.emb (witnessOfStk D roots c)) := by
  change RecPiop.pre (C.G roots) pi2Omega (T.model roots) (fun s ↦ Fa.pubOf roots s.2) s [] (some c, m) at h
  unfold RecPiop.pre at h
  rw [ite_eq_left List.length_nil] at h
  obtain ⟨c', hc', hrel⟩ := h
  cases Option.some.inj hc'
  refine satisfies_congr (Fa.valid roots) (fun i hi ↦ ?_) hrel
  rw [T.witness_eval roots c i hi]
  rfl

/-- **The protocol's last state follows from π2's check with true claims** (`checks_claims_iff_post2`). -/
theorem pi2Piop_post (C : Pi2Circuits D) (Fa : Pi2Facts D C) (T : Pi2Tables D C) (roots : RecSetupRoots)
    (s : Pi2St) (cW cQ : Stk) (inp : Inputs E) (hs : inp.scalars = s.2)
    (ha : inp.a.length = 2 ^ (Spec.of (D.circuitAt roots.pi1).circuit).core.logRow)
    (hall : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).all ≠ 0)
    (hcl : Pi2ClaimsHold D roots inp cW cQ) :
    (pi2Piop C Fa T roots).post s (pi2Opened cW cQ inp) (none, inp.a ++ [inp.ξ]) [inp.ρ] := by
  have hS := Fa.spec roots
  have ha' : inp.a.length = 2 ^ (C.G roots).logW := by rw [ha, hS.logRow]
  obtain ⟨hc, ht, hξ, hf⟩ := T.claims roots cW cQ inp hall hcl
  have key := (checks_claims_iff_post2 hS (Fa.valid roots) inp (T.model roots) (fun s ↦ Fa.pubOf roots s.2) s
    (by rw [hs]) cW cQ ha').mp ⟨hall, hc, ht, hξ, hf⟩
  change RecPiop.post (C.G roots) pi2Omega (T.model roots) (fun s ↦ Fa.pubOf roots s.2) s (pi2Opened cW cQ inp)
    (none, inp.a ++ [inp.ξ]) [inp.ρ]
  unfold RecPiop.post
  rw [ite_eq_right (by simp [pi2Opened]), ite_eq_right (by simp [pi2Opened]), ite_eq_left (by simp [pi2Opened])]
  exact ⟨cW, cQ, rfl, rfl, key.2.2⟩

/-! ## π2's extraction -/

/-- **π2's extraction from its layers**: the Fiat–Shamir layer, the tables' layer and the circuit's facts give
`Pi2Extraction` for the compiled circuit's relation, the public limbs of the statement's scalars, at `pi2Bound`. -/
theorem pi2Extraction_of_layers (C : Pi2Circuits D) (Fa : Pi2Facts D C) (T : Pi2Tables D C)
    (hfs : Pi2FsLayer D) :
    Pi2Extraction D (fun roots input stream w ↦ (C.G roots).Satisfies
      (Fa.pubOf roots (pi2Scalars D roots input stream)) (RecCircuit.emb w)) pi2Bound := by
  intro A Q hQ
  have h := hfs (pi2Piop C Fa T) pi2RoundErr (pi2Piop_err C Fa T)
    (fun roots s c ↦ (C.G roots).Satisfies (Fa.pubOf roots s.2) (RecCircuit.emb (witnessOfStk D roots c)))
    (fun roots s c m hpre ↦ pi2Piop_pre C Fa T roots s c m hpre)
    (fun roots s cW cQ inp hs ha hall hcl ↦ pi2Piop_post C Fa T roots s cW cQ inp hs ha hall hcl) A Q hQ
  rw [pi2BoundE_roundErr] at h
  refine (prEvent_mono _ _ _ fun z hz ↦ ⟨hz.1, fun ⟨w, hw, hrel⟩ ↦ hz.2 ⟨w, hw, ?_⟩⟩).trans h
  exact hrel

/-- **The circuit's corollary** (open, `lean-rec-circuit`: `ExpandSound` and `call_inputs`), for the public limbs of
the statement's scalars: a witness satisfying the compiled circuit holds a π1 stream π1-rec3's graph accepts with the
contract's openings on that calldata. -/
def Pi2CircuitAccepts (C : Pi2Circuits D) (Fa : Pi2Facts D C) : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) (w : ℕ → K) (ops : List Pi1Opening),
    (C.G roots).Satisfies (Fa.pubOf roots (pi2Scalars D roots input stream)) (RecCircuit.emb w) →
      pi1OpsOf D roots input stream = some ops →
        Pi1GraphAccepts (D.pi1IvAt roots.pi1) input (D.pi1Stream w) ops

/-- **π2's layers, assembled**: the compiled circuit, its facts, the tables' layer, the Fiat–Shamir layer and the
circuit's corollary give `Pi2Layers D pi2Bound`. -/
noncomputable def pi2Layers_of (C : Pi2Circuits D) (Fa : Pi2Facts D C) (T : Pi2Tables D C) (hfs : Pi2FsLayer D)
    (hcirc : Pi2CircuitAccepts C Fa) : Pi2Layers D pi2Bound where
  rootsAt := C.rootsAt
  compiled := C.compiled
  compile_ok := C.compile_ok
  stream_eq := C.stream_eq
  pub roots input stream := Fa.pubOf roots (pi2Scalars D roots input stream)
  extraction := pi2Extraction_of_layers C Fa T hfs
  circuit := hcirc

end RecCompose

/-- info: 'RecCompose.pi2Extraction_of_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Extraction_of_layers

/-- info: 'RecCompose.pi2Layers_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Layers_of

/-- info: 'RecCompose.hbind_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hbind_of
