-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The model (`RandomPermutationOracles`, `runWithRandomPermutation`, `queryPermutation`) is leanerVM's
-- (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`).
import ZK.ProverBridge
import ZK.Final
import E2ECompleteness.End

/-!
# The prover bridge off the degenerate challenges

`CoreWhir` (`ProverBridge.lean`) asks the skeleton, formatted, to reproduce the statement's proof for
**every** permutation. That is false: at challenges `α, β` where a denominator of the sum vanishes at a
cell (`BadAB`, `formal/Completeness`), the statement's prover inverts `0` as `0` and computes no quotient
(its coset values interpolate a polynomial that is not F1's), while the joint model's quotient table
(`TQD`, `ZK/FactsClaims.lean`) is F1's honest quotient; the skeleton's quotient leaves are then not the
statement's. Here:

* **`abDet π stmt w c`**: the statement's `α, β` at the permutation `π` (its run's first two chain
  challenges, `abWith`, the prover's own prefix);
* **`CoreWhirG`**: `CoreWhir` for the permutations whose `α, β` are not degenerate for the witness and
  the masks (`BadABD`, the completeness side's `badSet`'s first part);
* **`badProb`**: the probability that the statement's prover makes no proof **or** its `α, β` are
  degenerate;
* **`proverBridge_of_detG`**: `ProverBridge` at `εR Q = δ` from `CoreWhirG` and `badProb ≤ δ`
  (`proverBridge_of_det` with the degenerate permutations added to the bad set);
* the deployed public data the skeleton reads: `stmtBytesD` (the label's `y ‖ root`), the layouts'
  identifiers `idWD`, `idσD`, `idQD` (`Layout.id`), the wiring codeword's rows `rowsWD`;
* **`zeroKnowledge_final`**: `zeroKnowledge_end` at the deployed instance (`ZK/Final.lean`'s facts),
  the renderer WHIR's honest prover per statement (`whirRenderer deployedRep stmt`), the bridge from
  `CoreWhirG` and `badProb`.
-/

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open PcsQuotient.Domain PcsQuotient.Transcript
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open QuotientZk.DRpm (implJ proverJ coinR zkGameRpmD)
open Primitives
open scoped ENNReal

/- The fields' instances of `formal/Field` (`F64`, `F192`), as `ZK/Final.lean` has them: the
completeness side's imports bring others of the same types. -/
attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

namespace PcsQuotient.EndToEnd

open QuotientZk (Close Proto)
open Eager (St permImpl frac)

set_option linter.unusedSectionVars false

/-! ## The statement's `α, β` -/

/-- **The statement's prover's `α, β`** over `F`: the circuit's commitment, the witness table's, the
chain seeded by the label, the witness root absorbed, two challenges (`proveWith`'s prefix). -/
def abWith {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (stmt : Statement)
    (w : Secret) (coins : Masks × Padding × Padding) : m (E × E) := do
  let circuit := membership logRows
  let mv := cellVars circuit.logRows
  let indexTree ← commitWith F mv circuit.wiringTable
  let wHat := coefficients mv 0 (circuit.cells (membershipInputs w))
  let wStack := witnessStack circuit.logRows wHat (maskEntries coins.1) coins.2.1
  let witnessTree ← commitWith F (mv + 1) wStack
  let c ← Chain.startWith F (label indexTree.root stmt)
  let witnessRoot := digestScalars witnessTree.root
  let c := (c.absorb witnessRoot.1).absorb witnessRoot.2
  let (α, c) ← c.squeezeWith F
  let (β, _) ← c.squeezeWith F
  return (α, β)

/-- `α, β` at the permutation `π`. -/
def abDet (π : Equiv.Perm St) (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding) :
    E × E :=
  (abWith (permId π) stmt w c).run

/-- **Degenerate `α, β`** for the witness and the masks: a denominator of the sum vanishes at a cell
(`formal/Completeness`'s `BadAB` on the deployed instance, the first part of `badSet`). -/
def BadABD (w : Secret) (m : Masks) (ab : E × E) : Prop :=
  Completeness.Reduction.BadAB Completeness.deployedInstanceE (E2ECompleteness.honestMsg w m) ab.1
    ab.2

open Classical in
/-- **The statement's prover fails or meets degenerate `α, β`**, over `F`. -/
noncomputable def badWith {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)
    (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding) : m Bool := do
  let r ← prover F stmt w coins
  let ab ← abWith F stmt w coins
  return (r.isNone || decide (BadABD w coins.1 ab))

/-- **The probability that the statement's prover makes no proof or meets degenerate `α, β`**, at
the coins `c`. -/
noncomputable def badProb (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding) : ℝ≥0∞ :=
  Pr{let b ← runWithRandomPermutation (badWith queryPermutation stmt w c)}[b = true]

theorem sim_abWith (π : Equiv.Perm St) (stmt : Statement) (w : Secret)
    (c : Masks × Padding × Padding) :
    simulateQ (permImpl π) (abWith queryPermutation stmt w c) = pure (abDet π stmt w c) := by
  have h1 : (simHom (permImpl π)).app (abWith queryPermutation stmt w c) =
      abWith (fun x ↦ (simHom (permImpl π)).app (queryPermutation x)) stmt w c := by
    simp only [abWith, MHom.app_bind, MHom.app_pure, Param.commitWith_hom, Param.startWith_hom,
      Param.squeezeWith_hom]
  have h2 : (idHom ProbComp).app (abWith (permId π) stmt w c) =
      abWith (fun x ↦ (idHom ProbComp).app (permId π x)) stmt w c := by
    simp only [abWith, MHom.app_bind, MHom.app_pure, Param.commitWith_hom, Param.startWith_hom,
      Param.squeezeWith_hom]
  simp only [simHom_app, sim_queryPermutation] at h1
  simp only [idHom_app] at h2
  rw [h1]
  exact h2.symm

open Classical in
theorem sim_badWith (π : Equiv.Perm St) (stmt : Statement) (w : Secret)
    (c : Masks × Padding × Padding) :
    simulateQ (permImpl π) (badWith queryPermutation stmt w c) =
      pure ((proverDet π stmt w c).isNone || decide (BadABD w c.1 (abDet π stmt w c))) := by
  unfold badWith
  rw [simulateQ_bind, sim_prover, pure_bind, simulateQ_bind, sim_abWith, pure_bind,
    simulateQ_pure]

/-! ## The core and the bridge -/

/-- **The deterministic core, off the degenerate challenges**: for every coins `s` of the skeleton
model, permutation `π` and completions `gH`, `gF`, whenever the statement's prover with `π` makes the
proof `x` and its `α, β` are not degenerate, `fmt` with `π` makes `x` of the skeleton's proof against
`Gof (kDet π) π gH gF`. -/
def CoreWhirG (rep : QuotientZk.Instance.Rep K E) (P₀ : Params E) (stmtE : Fin P₀.words → E)
    (Y : E) (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (R : Renderer K E) (stmt : Statement)
    (w : Secret) (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (coinsOf : RandD K → Masks × Padding × Padding) : Prop :=
  ∀ (s : RandD K) (π : Equiv.Perm St) (gH : List UInt8 → KSt) (gF : KSt → DigestBytes) (x : Proof),
    proverDet π stmt w (coinsOf s) = some x → ¬ BadABD w (coinsOf s).1 (abDet π stmt w (coinsOf s)) →
      fmtDet π stmt (skelDet (QuotientZk.DRpm.ofBytes (Pb rep P₀ gK van stmtE Y TW TQ R))
        (Gof (kDet π) π gH gF) s skel) = some x

/-- **The prover bridge from programs, off a deterministic bad set**: if the formatted skeleton's
proof is the statement's prover's for every permutation at which the prover makes one and `Bad` fails
(`hcore`), the prover bridge holds with `εR Q = δ`, `δ` a bound on the probability that the prover
makes no proof or `Bad` holds. -/
theorem proverBridge_of_detG {S : Type} [SampleableType S] (stmt : Statement) (w : Secret)
    (P : Proto S Inp Out Msg Tbl Pos) (skel : OracleComp DSpec QuotientZk.Deployed.Proof)
    (coinsOf : S → Masks × Padding × Padding) (δ : ℝ≥0∞)
    (hcore : ∀ (s : S) (π : Equiv.Perm St) (gH : List UInt8 → KSt) (gF : KSt → DigestBytes)
      (x : Proof), proverDet π stmt w (coinsOf s) = some x →
        ¬ BadABD w (coinsOf s).1 (abDet π stmt w (coinsOf s)) →
        fmtDet π stmt (skelDet P (Gof (kDet π) π gH gF) s skel) = some x)
    (hbad : ∀ s : S, badProb stmt w (coinsOf s) ≤ δ) :
    ProverBridge stmt w P skel (fmt stmt) coinsOf (fun _ ↦ δ) := by
  classical
  intro D₀ Q _ s
  let Bad : Equiv.Perm St → Prop := fun π ↦
    (proverDet π stmt w (coinsOf s)).isNone = true ∨
      BadABD w (coinsOf s).1 (abDet π stmt w (coinsOf s))
  have hc := Eager.close_of_perm
    (prover queryPermutation stmt w (coinsOf s) >>= fun pf ↦ simulateQ liftPerm (D₀ pf))
    (zkGameRpmD P skel (fun pf ↦ fmt stmt pf >>= D₀) s) Bad ?_
  · refine hc.mono ?_
    have hfrac : badProb stmt w (coinsOf s) = frac Bad := by
      refine Eager.prEvent_eq_frac _ _ Bad fun π ↦ ?_
      rw [sim_badWith, prEvent_pure]
      simp only [Bad, Bool.or_eq_true, decide_eq_true_eq]
    calc frac Bad = badProb stmt w (coinsOf s) := by convert hfrac.symm
      _ ≤ δ := hbad s
  · intro π hπ
    simp only [Bad, not_or, Option.isNone_iff_eq_none] at hπ
    obtain ⟨hπ, hab⟩ := hπ
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hπ
    have hL : simulateQ (permImpl π)
        (prover queryPermutation stmt w (coinsOf s) >>= fun pf ↦ simulateQ liftPerm (D₀ pf)) =
        simulateQ (permImpl π) (simulateQ QuotientZk.permQuery (D₀ (some x))) := by
      rw [simulateQ_bind, sim_prover, pure_bind, hx]
      rfl
    have hR : simulateQ (permImpl π) (zkGameRpmD P skel (fun pf ↦ fmt stmt pf >>= D₀) s) =
        proverJ P (fun m ↦ pure (kDet π m)) (fun x ↦ pure (π x))
          (simulateQ (permImpl π) (coinR KSt)) (simulateQ (permImpl π) (coinR DigestBytes)) s skel
          >>= fun pf ↦ simulateQ (permImpl π)
            (simulateQ QuotientZk.permQuery (D₀ (fmtDet π stmt pf))) := by
      unfold zkGameRpmD
      rw [simulateQ_bind, sim_proverJ]
      refine bind_congr fun pf ↦ ?_
      rw [simulateQ_bind, simulateQ_bind, sim_permQuery, pure_bind]
      rfl
    rw [hL, hR, prEvent_bind_true]
    rw [OracleComp.prEvent_bind_congr_of_support _ _
      (fun _ ↦ (fun b ↦ b = true) <$>
        simulateQ (permImpl π) (simulateQ QuotientZk.permQuery (D₀ (some x)))) ?_]
    · rw [OracleComp.prEvent_bind_const]
    · intro pf hpf
      obtain ⟨gH, gF, rfl⟩ := mem_support_proverJ P (kDet π) π _ _ s skel pf hpf
      rw [hcore s π gH gF x hx hab]

/-! ## The deployed public data -/

/-- **The statement's bytes** in the chain's label: `y ‖ root`. -/
def stmtBytesD (stmt : Statement) : Vector UInt8 64 := stmt.y ++ stmt.root

/-- **The layouts' identifiers** (`Layout.id`, constants of the verifier), as bytes. -/
def idWD : QuotientRpm.Bytes32 := Digest.toBytes (witnessLayout logRows).id
def idσD : QuotientRpm.Bytes32 := Digest.toBytes (wiringLayout logRows).id
def idQD : QuotientRpm.Bytes32 := Digest.toBytes (quotientLayout logRows).id

/-- **The wiring codeword's rows**, as the leaves' bytes: row `i` of the circuit's wiring table's
WHIR word (`commitWith`'s `stackWordFast`), its words little-endian. Irreducible: unfolded, its
`List.range (2^19)` is a list of `2^19` cells, which elaboration must not reduce. -/
noncomputable def rowsWD : List (List UInt8) :=
  (List.range (2 ^ 19)).map fun i ↦
    (stackWordFast (cellVars logRows) 1 (membership logRows).wiringTable i).flatMap kBytes

theorem rowsWD_eq : rowsWD = (List.range (2 ^ 19)).map fun i ↦
    (stackWordFast (cellVars logRows) 1 (membership logRows).wiringTable i).flatMap kBytes := rfl

attribute [irreducible] rowsWD

theorem length_rowsWD : rowsWD.length = 2 ^ 19 := by
  rw [rowsWD_eq, List.length_map, List.length_range]

/-- **The deployed joint model rendered by WHIR's honest prover** for the statement. -/
noncomputable abbrev jdW (stmt : Statement) (w : Secret) :=
  deployedJointData deployedRep P₀D (stmtWD stmt) F192.Y (gKD w) vanD (TWD w) (TQD w)
    (Render.whirRenderer deployedRep stmt) inKD sigmaAtD

/-- **The deployed core**: `CoreWhirG` at the deployed instance, tables, coins and renderer. -/
def CoreD (stmt : Statement) (w : Secret) : Prop :=
  CoreWhirG deployedRep P₀D (stmtWD stmt) F192.Y (gKD w) vanD (TWD w) (TQD w)
    (Render.whirRenderer deployedRep stmt) stmt w
    (skelSetup (stmtBytesD stmt) idWD idσD idQD rowsWD) (decodeCoins ∘ eD)

/-- **The deployed prover bridge** from the deployed core and `badProb ≤ δ`. -/
theorem proverBridge_deployed (stmt : Statement) (w : Secret) (δ : ℝ≥0∞) (hcore : CoreD stmt w)
    (hbad : ∀ s, badProb stmt w ((decodeCoins ∘ eD) s) ≤ δ) :
    ProverBridge stmt w (jdW stmt w).P (skelSetup (stmtBytesD stmt) idWD idσD idQD rowsWD)
      (fmt stmt) (decodeCoins ∘ eD) (fun _ ↦ δ) :=
  proverBridge_of_detG stmt w _ _ _ δ hcore hbad

end PcsQuotient.EndToEnd
