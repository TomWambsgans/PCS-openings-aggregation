-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.Defs
import QuotientSecurity.DeployedConcrete

/-!
# The bridge facts knowledge soundness takes from the definitions' bridge

Three statements that the Statement's definitions (`formal/Statement`, `PcsQuotient`) are the
proof layers' (`formal/Compose`, `formal/QuotientSecurity`, `formal/WhirBridge`), each a
proposition about definitions only (no probability), at the constants `c` (`beta()`'s words and
`row_vanishing`'s `tau`, `Reduce.Consts`) and F1's instance `inst c h` (`beta()`'s basis, the
deployed wiring, `coordinate_weight`'s weights). The
definitions' bridge proves all three at the Statement's constants (`formal/EndToEnd/Bridge/Facts.lean`:
`Bridge.setupBridge_final`, `Bridge.verifierBridge_final`, `Bridge.readsSecret_final`), and the end
theorem (`Final.lean`) uses those proofs, so it has no hypothesis.

* **`SetupBridge`** (the circuit's commitment): the Statement's wiring table
  (`(membership 22).wiringTable`) is a stack of `2^24` words whose table's polynomial carries the
  deployed wiring on the cells (`Circuit.lean`'s `σ`-points in the novel basis): the hypothesis
  `hq₀` of `Compose`'s `wiringClaims_deployD`. With mumbai's `buildTreeM_eq_withHash`,
  `stackWordFast_eq`, it makes the Statement's setup (`setupTreeWith`) Compose's `stackSetup`.
* **`VerifierBridge`** (the verifier): on a proof whose two roots are digests, the Statement's
  verifier over `π` is Compose's chain and three openings with the Statement's early stops
  (`verifyES`), on the converted proof, over `π` (`keccakCallsOverQueryPermutation`); on another
  proof it rejects (`verifier_malformed`, proved here).
* **`ReadsSecret`** (the extractor's reading): a stack whose table, read as F1's first message
  (`readW`), holds a computation of the deployed circuit proving membership of the statement's
  `(y, root)` (`ProvesMembership`) spells a secret of the statement (`secretOfStack`: the table
  read back through the hidden layout, the cells' values by the additive transform, the input
  rows' `V` cells as bits).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge

variable (c : Consts) (h : IsCantor c.beta)

/-- F1's instance of the deployed protocol: `beta()`'s Cantor basis (`basisE`), the deployed wiring
(`membership.sigma`, the Rust's, `deployedSigma`), `coordinate_weight`'s weights as F0c states them
(`coordWeight F192.G F192.Y`, `rustCoordinateWeight_eq`; `Compose`'s `rustInstance` takes
`coordinate_weight`'s values below `8` and zero above, which F1's relation does not read). -/
noncomputable abbrev inst : Instance E :=
  ⟨basisE c h, deployedSigma, coordWeight Primitives.F192.G Primitives.F192.Y⟩

/-- **SETUP**: the Statement's wiring table is the stack `q₀` of `2^24` words, and `q₀`'s table's
polynomial carries the deployed wiring on the cells of `beta()`'s basis (`wiringClaims_deployD`'s
`hq₀`). -/
def SetupBridge : Prop :=
  ∃ q₀ : Column (wiringLayout 22).logN,
    q₀.values.toArray = (PcsQuotient.membership PcsQuotient.logRows).wiringTable ∧
      ∀ x, (tablePoly (wiringFn 22 (tabOf (wiringLayout 22) q₀))).eval
          ((inst c h).basis.point x) = (inst c h).basis.point ((inst c h).wiring x)

/-- **VERIFIER**: on a proof whose two roots' scalars are digests, the Statement's verifier over
`π` with the circuit commitment `ir` is the deployed verifier with early stops (`verifyES`, the
deployed wire's chain, `reduce`'s claims at `c`, the three openings) on the converted proof with
the commitment `ir`, Keccak-256 over `π` and Keccak-f `= π`. -/
def VerifierBridge : Prop :=
  ∀ (ir : Digest) (stmt : PcsQuotient.Statement) (proof : PcsQuotient.Proof) (r₁ r₂ : Digest),
    digestOfScalars proof.reduction.witnessRoot = some r₁ →
    digestOfScalars proof.reduction.quotientRoot = some r₂ →
    PcsQuotient.verifier Common.queryPermutation ir stmt proof =
      simulateQ keccakCallsOverQueryPermutation
        (verifyES (deployedWire (inst c h)) c (withIr (toB ir) (convP (stmt, proof))))

/-- **EXTRACTOR READING**: a witness stack `q` whose table, read as F1's first message (`readW`),
has cells (`cellsOf`) proving membership of the statement's `(y, root)` spells a secret of the
statement (`secretOfStack` of the membership circuit). -/
def ReadsSecret : Prop :=
  ∀ (stmt : PcsQuotient.Statement) (q : Column (witnessLayout 22).logN),
    ProvesMembership ((inst c h).cellsOf (readW (inst c h) (tabOf (witnessLayout 22) q)).1)
        (fun i => stmt.y.get i) (fun i => stmt.root.get i) →
      PcsQuotient.Relation stmt
        (PcsQuotient.secretOfStack (PcsQuotient.membership PcsQuotient.logRows) q.values)

end Soundness
