-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Assembly

/-!
# The skeleton with the setup

The statement's prover (`Prover.lean`, `proveWith`) computes the circuit's commitment over `π` (the
wiring table's tree, `commitWith F mv sigmaHat`) and labels the reduction's chain with its root; the
statement's `realExperiment` has no setup before it. `QuotientZk`'s deployed skeleton
(`Deployed.skel sh`) reads the circuit's commitment as a constant of its shape (`sh.st.indexRoot`). In
the random-permutation model the root is a random variable, so no constant shape makes the skeleton the
statement's prover: the skeleton of the statement's prover computes the wiring table's tree first
(public queries) and runs `Deployed.skel` at the shape whose commitment is that tree's root.

* `skelWith w shOf`: the tree of the public opening shape `w`, then `Deployed.skel (shOf lv)`;
* `skelSetup stmtBytes idW idσ idQ rowsW`: `skelWith` at the wiring table's shape, the deployed shape of
  root `rootOf lv` and the statement's bytes;
* `skelWith_queryBound`, `duplexDiscipline_skelWith`: its operations (the tree's, then at most the
  skeleton's) and its duplex discipline (the tree makes no permutation call: `Disc.silent_tree₀`,
  `Disc.ok_skel`).
-/

open OracleComp OracleSpec
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-- **A skeleton with a setup**: the tree of the public opening shape `w` (its rows hashed, its nodes:
public queries), then the skeleton at the shape `shOf` of the tree's levels. -/
def skelWith (w : QuotientZk.Deployed.OpenShape)
    (shOf : List (List QuotientRpm.Bytes32) → QuotientZk.Deployed.Shape) :
    OracleComp DSpec QuotientZk.Deployed.Proof := do
  let lv ← QuotientZk.Deployed.tree₀ w
  QuotientZk.Deployed.skel (shOf lv)

/-- **The skeleton of the statement's prover**: the wiring table's tree (the circuit's commitment, at
`2^22` rows: `2^19` leaves), then the deployed skeleton with that tree's root as the chain's index
root and the statement's bytes `stmtBytes`. -/
def skelSetup (stmtBytes : Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) : OracleComp DSpec QuotientZk.Deployed.Proof :=
  skelWith (QuotientZk.Deployed.wiringShape idσ rowsW) fun lv ↦
    QuotientZk.Deployed.deployedShape ⟨QuotientZk.Deployed.rootOf lv, stmtBytes⟩ idW idσ idQ rowsW

theorem skelWith_queryBound (w : QuotientZk.Deployed.OpenShape)
    (shOf : List (List QuotientRpm.Bytes32) → QuotientZk.Deployed.Shape) (n : ℕ)
    (hn : ∀ lv, QuotientZk.Deployed.skelBound (shOf lv) ≤ n) :
    IsTotalQueryBound (skelWith w shOf) (QuotientZk.Deployed.tree0Bound w + n) :=
  isTotalQueryBound_bind (QuotientZk.Deployed.qb_tree₀ w) fun lv ↦
    (QuotientZk.Deployed.skel_queryBound (shOf lv)).mono (hn lv)

theorem ok_skelWith (w : QuotientZk.Deployed.OpenShape)
    (shOf : List (List QuotientRpm.Bytes32) → QuotientZk.Deployed.Shape) :
    QuotientZk.Deployed.Disc.Ok (skelWith w shOf) :=
  (QuotientZk.Deployed.Disc.silent_tree₀ w).ok.bind fun _ ↦ QuotientZk.Deployed.Disc.ok_skel _

theorem duplexDiscipline_skelWith {S : Type} (P : QuotientZk.Proto S Inp Out Msg Tbl Pos)
    (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (w : QuotientZk.Deployed.OpenShape)
    (shOf : List (List QuotientRpm.Bytes32) → QuotientZk.Deployed.Shape) :
    QuotientZk.DRpm.DuplexDiscipline P (skelWith w shOf) :=
  QuotientZk.DRpm.duplexDiscipline_of_wp P hrow _ (ok_skelWith w shOf [] _ fun _ _ ↦ trivial)

/-- The wiring table's tree at `2^19` rows makes `20 · 2^19 ≤ 2^24` operations. -/
theorem tree0Bound_wiring (idσ : QuotientRpm.Bytes32) (rowsW : List (List UInt8))
    (hrows : rowsW.length = 2 ^ 19) :
    QuotientZk.Deployed.tree0Bound (QuotientZk.Deployed.wiringShape idσ rowsW) ≤ 2 ^ 24 := by
  simp only [QuotientZk.Deployed.tree0Bound, QuotientZk.Deployed.wiringShape, hrows]
  norm_num

/-- **The statement's prover's skeleton makes at most `2^24 + 2^70` operations.** -/
theorem skelSetup_queryBound (stmtBytes : Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19) :
    IsTotalQueryBound (skelSetup stmtBytes idW idσ idQ rowsW) (2 ^ 24 + 2 ^ 70) :=
  (skelWith_queryBound _ _ (2 ^ 70) fun _ ↦
    QuotientZk.Deployed.skelBound_deployed _ idW idσ idQ rowsW hrows).mono
    (Nat.add_le_add_right (tree0Bound_wiring idσ rowsW hrows) _)

theorem duplexDiscipline_skelSetup {S : Type} (P : QuotientZk.Proto S Inp Out Msg Tbl Pos)
    (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (stmtBytes : Vector UInt8 64)
    (idW idσ idQ : QuotientRpm.Bytes32) (rowsW : List (List UInt8)) :
    QuotientZk.DRpm.DuplexDiscipline P (skelSetup stmtBytes idW idσ idQ rowsW) :=
  duplexDiscipline_skelWith P hrow _ _

end PcsQuotient.EndToEnd
