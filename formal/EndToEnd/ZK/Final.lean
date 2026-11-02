-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.End
import ZK.FactsField
import ZK.FactsF1
import ZK.FactsClaims

/-!
# Zero knowledge of the membership proof, the deployed instance plugged in

**`zeroKnowledge_deployed_final`**: `zeroKnowledge_deployed_end` (`ZK/End.lean`) at the deployed
fields, instance, tables and coins, every hypothesis of the field, of F1, of the simulator's public
functions, of the honest tables' claims and of the coins discharged:

* **the fields** (`FactsField.lean`): `K = F64`, `E = F192` (the Statement's `LeanVM.Parameters.K`,
  `E`), `[E : K] = 3` (`finrank_KE`), `|E| = 2^192`, `|K| = 2^64` (`card_E`, `card_K`),
  `1, Y, Y²` independent for `Y = F192::Y` (`linIndep_Y`); the representations `deployedRep`: `K`'s
  words `F64.ofNat` (the novel basis's points `K(q)`), `F64.toU64`, `E`'s limbs `(c0, c1, c2)`;
* **F1's facts** (`FactsF1.lean`): the parameters `P₀D` of the deployed instance (`beta()`'s Cantor
  basis in `K`, the deployed σ, `coordinate_weight`'s weights), the statement's words `stmtWD stmt`
  (`statement::halves`, then `1, 0, 0, 0`), the witness's row polynomials `gKD w` (the cells of F0b's
  honest assignment of the secret, as Completeness's witness table holds them), `vanD = w_22`:
  `Exact`, `2^24` cells, `w_22` vanishing on the rows, nonzero, of degree `2^22`, and the relation
  (`hsatD`, for every witness of the statement's relation);
* **the simulator's public functions**: `inKD` (the `y`, `y²` limbs zero, computable) and the
  wiring polynomial's value `P₀D.sigmaPoly.eval`;
* **the honest tables' claims** (`FactsClaims.lean`): the deployed tables `TWD`, `TQD` (Completeness's
  witness and quotient tables, by numbers, placed where `witness_layout(22)`, `quotient_layout(22)` hold
  them) meet the verifier's claims at every good challenge and non-degenerate masks (`hTWD`, `hTQD`);
* **the coins** (`FactsField.lean`): `eD`, a bijection of the skeleton model's randomness onto the
  statement's coins' words (`eD_bijective`): the masks' words `3j + i`, each table's padding word
  `l · 2^ℓ + j` the model's lane `l` entry `j`, but on the overflow lane, whose stream continues past
  its held pieces (`Layout.stackOf`'s `pad l (i − held · 2^8)`), entry `padSrc ℓ held l j`.

**What remains named**: the renderer `R` (WHIR's honest prover is one), the prover's permutation
budget (`hprover`: at most `Qp` calls of `π`; it reads the renderer's messages, whose rows the
skeleton hashes), and **`ProverBridge`** (`hbridge`) at the coins `decodeCoins ∘ eD`. The simulator
is `zkSimulator` at `deployedPub deployedRep` and `deployedSimV` (its tables `simTW`, `simTQ` are
computed, `Instance/Builder.lean`'s Gaussian elimination in `deployedRep`'s coordinates; its wiring
value `P₀D.sigmaPoly.eval` is the polynomial `Completeness.wiringTableK`'s table holds).

`ζ Q = εR Q + 2^-113 + epsHV + 2^24 (2^24 + 2^70 + 2^23 + Q) 2^-2368 + 2^48 2^-2368 +
(Qp + 2^23 + Q)² / 2^508`, `epsHV = 2^-165 + 2^-125 + 2/2^192` (`zkBoundEnd`, `zkBoundEnd_le`).
-/

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open LeanVM.Parameters Primitives
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-- The deployed wiring polynomial's value, the simulator's public `sigmaAt`. -/
noncomputable def sigmaAtD (t : E) : E := P₀D.sigmaPoly.eval t

/-- **The deployed joint model** of a statement's witness: `deployedJointData` at the deployed
fields, instance, tables and the renderer `R`. -/
noncomputable abbrev deployedJD (R : Renderer K E) (stmt : Statement) (w : Secret) :=
  deployedJointData deployedRep P₀D (stmtWD stmt) F192.Y (gKD w) vanD (TWD w) (TQD w) R inKD
    sigmaAtD

/-- **Zero knowledge of the membership proof, the deployed instance plugged in.** For every
renderer `R` of the prover's messages, the skeleton of the statement's prover on `skelSetup`, the
proof formatted by `fmt`: `ZeroKnowledgeWith` for `zkSimulator` at the deployed public part and
view simulator, at `zkBoundEnd Qp fmtBudget εR`, given the prover's permutation budget `Qp` and
`ProverBridge` at the coins `decodeCoins ∘ eD`. -/
theorem zeroKnowledge_deployed_final (R : Renderer K E)
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
      (zkSimulator (fun _ ↦ deployedPub deployedRep)
        (fun stmt ↦ deployedSimV deployedRep P₀D (stmtWD stmt) F192.Y R inKD sigmaAtD)
        (fun stmt ↦ skelSetup (stmtBytes stmt) idW idσ idQ rowsW) fmt)
      rpmSimOracle (zkBoundEnd Qp fmtBudget εR) :=
  zeroKnowledge_deployed_end deployedRep P₀D F192.Y R inKD sigmaAtD stmtWD (fun _ w ↦ gKD w)
    (fun _ _ ↦ vanD) (fun _ w ↦ TWD w) (fun _ w ↦ TQD w) finrank_KE card_E card_K linIndep_Y hED hND
    (fun _ _ _ ↦ hvanD) (fun stmt w hw ↦ hsatD stmt w hw) (fun _ _ _ ↦ hvan0D) (fun _ _ _ ↦ hdegD)
    inKD_iff (fun _ ↦ rfl) (fun _ w _ ↦ hTWD w) (fun stmt w hw ↦ hTQD stmt w hw) stmtBytes idW idσ
    idQ rowsW hrows eD eD_bijective Qp εR s₀ hprover hbridge

end PcsQuotient.EndToEnd

/--
info: 'PcsQuotient.EndToEnd.zeroKnowledge_deployed_final' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_deployed_final
