-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The statement's prover (`commitWith`, the chain, `openingSpongeWith`) runs leanerVM's code (branch
-- `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Run.lean`, `Statement/Keccak.lean`,
-- `Statement/LeanVmVerifier.lean`), as `formal/Statement` adapts it.
import ZK.CoreRedClaims

/-!
# The reduction's part of the deployed core

`CoreD` (`ZK/CoreDefs.lean`) asks the skeleton against `G = Gof (kDet π) π gH gF`, rendered by WHIR's
honest prover, to reproduce the statement's honest proof. This file and `CoreRedChain.lean`,
`CoreRedClaims.lean` prove the reduction's part of it, for every permutation `π` and completions
`gH`, `gF`, nothing large evaluated:

1. **The chain** (`CoreRedChain.lean`): the skeleton's five chain answers (`chainOuts`, from the
   index root, the two roots, the statement's bytes and the five values' limbs) decode
   (`dH deployedRep.limbs`, equal to the renderer's `chainChal`: `dH_eq_chainChal`) to the
   statement's challenges: `reduceWith_skel` (`reduceWith` over `π` on the roots' halves and the
   values is the renderer's `chainClaims` at those answers, with the roots), `reduceWith_skel_claimsAt`
   (the same as `claimsAt` at the decoded answers), `chainClaims_chainOuts`; the statement prover's
   chain step by step (`startWith_label`, `squeeze_root`, `squeeze_plain`, `squeeze_vals`), and its
   `α, β` (`abDet_eq` below).
2. **The values** (`CoreRedClaims.lean`): `redMsgs_eq` (the joint model's five values are the
   statement prover's `rowValuesAt`, `nextAt`), `eOfLimbs_limbsOf`, `reductionOf_valsOf`,
   `takeScalars_valsOf`.
3. **The claims** (`CoreRedClaims.lean`): `chainClaims_model` (the joint model's claims at
   `chOf deployedRep.limbs h` are the renderer's whenever those exist), `pointW_eq`, `points_Q`, the
   IV bytes `claimMsg_witness`, `claimMsg_wiring'`, `claimMsg_quotient'`; at the skeleton's answers
   (`claims_skel` below).
4. **The seeds** (`CoreRedChain.lean`): `seed_rel`, `runDet_seed_rel`, with the deployed prefixes
   (`seed_witness`, `seed_wiring`, `seed_quotient` below).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Prover
open QuotientZk.Deployed (Inp Out Msg Item KSt DSpec Tbl Pos)
open QuotientZk.Instance
open QuotientRpm (Limbs)
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

open Render (limbsOf chainChal)

section Deployed

variable (π : Equiv.Perm Eager.St) (gH : List UInt8 → KSt) (gF : KSt → DigestBytes)

/-! ## The deployed seeds -/

/-- **The witness opening's seed** is the statement's sponge, up to `Duplex.Rel`. -/
theorem seed_witness (cls : List Claim) :
    Duplex.Rel ⟨π (QuotientZk.Deployed.seedInput
        (kDet π ((QuotientZk.Deployed.witnessShape idWD).ivPrefix ++ claimBytes cls))), []⟩
      (openingSpongeWith (permId π) (witnessLayout logRows) cls).run :=
  seed_rel π _ _ ivPrefix_witness cls

/-- **The wiring opening's seed** (any rows). -/
theorem seed_wiring (rows : List (List UInt8)) (cls : List Claim) :
    Duplex.Rel ⟨π (QuotientZk.Deployed.seedInput
        (kDet π ((QuotientZk.Deployed.wiringShape idσD rows).ivPrefix ++ claimBytes cls))), []⟩
      (openingSpongeWith (permId π) (wiringLayout logRows) cls).run :=
  seed_rel π _ _ (ivPrefix_wiring rows) cls

/-- **The quotient opening's seed.** -/
theorem seed_quotient (cls : List Claim) :
    Duplex.Rel ⟨π (QuotientZk.Deployed.seedInput
        (kDet π ((QuotientZk.Deployed.quotientShape idQD).ivPrefix ++ claimBytes cls))), []⟩
      (openingSpongeWith (permId π) (quotientLayout logRows) cls).run :=
  seed_rel π _ _ ivPrefix_quotient cls

/-! ## The claims at the skeleton's answers -/

/-- **The statement's reduction, the renderer and the joint model agree at the skeleton's answers**:
when `reduceWith` over `π` returns `r` on the roots `rW`, `rQ` and the values `a`, `next`, its roots
are `rW`, `rQ`, and for answers whose first five are the skeleton's chain's (`chainOuts`, any rest)
the renderer's claims are `r`'s, the joint model's opening points (`pointW`, `pointQ`, `pointS` at
`chOf deployedRep.limbs`) are `r`'s claims' points, and the claims' bytes the skeleton hashes into the
three IVs are `claimBytes [r.claims.witness]`, `claimBytes [r.claims.wiring]`,
`claimBytes [r.claims.quotient, r.claims.sum]`. -/
theorem claims_skel (ir rW rQ : Digest) (stmt : Statement) (a : Vector E 4) (next : E)
    (rest : List Out) (r : Reduced)
    (hr : (reduceWith (permId π) logRows ir stmt
      ⟨digestScalars rW, digestScalars rQ, a, next⟩).run = some r) :
    r.witnessRoot = rW ∧ r.quotientRoot = rQ ∧
      Render.chainClaims stmt
        (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next)) ++ rest)
        (a.get, next) = some r.claims ∧
      pointW (chOf deployedRep.limbs
        (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next)) ++ rest)) =
        r.claims.witness.point ∧
      [pointQ P₀D F192.Y (chOf deployedRep.limbs
          (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next)) ++ rest))
          (a.get, next), pointS F192.Y] = [r.claims.quotient.point, r.claims.sum.point] ∧
      claimMsg deployedRep P₀D (stmtWD stmt) F192.Y 5 (chOf deployedRep.limbs
          (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next)) ++ rest))
          (a.get, next) = [.bytes (claimBytes [r.claims.witness])] ∧
      claimMsg deployedRep P₀D (stmtWD stmt) F192.Y 128 (chOf deployedRep.limbs
          (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next)) ++ rest))
          (a.get, next) = [.bytes (claimBytes [r.claims.wiring])] ∧
      claimMsg deployedRep P₀D (stmtWD stmt) F192.Y 242 (chOf deployedRep.limbs
          (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next)) ++ rest))
          (a.get, next) = [.bytes (claimBytes [r.claims.quotient, r.claims.sum])] := by
  rw [reduceWith_skel π gH gF] at hr
  obtain ⟨cl, hcl, rfl⟩ := Option.map_eq_some_iff.mp hr
  have hcl' : Render.chainClaims stmt
      (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next)) ++ rest)
      (a.get, next) = some cl := by
    rw [← chainClaims_take, List.take_left' (length_chainOuts π gH gF _ _ _ _ _)]
    exact hcl
  exact ⟨rfl, rfl, hcl', pointW_eq _ _ _ _ hcl', points_Q _ _ _ _ hcl', claimMsg_witness _ _ _ _ hcl',
    claimMsg_wiring' _ _ _ _ hcl', claimMsg_quotient' _ _ _ _ hcl'⟩

/-! ## The statement prover's `α, β` -/

/-- **The statement prover's `α, β`** (`abDet`) are the decoded first two answers of the skeleton's
chain on the circuit's commitment and the witness table's root over `π` (any later roots and
values). -/
theorem abDet_eq (stmt : Statement) (w : Secret) (c : Masks × Padding × Padding) (rQ : Digest)
    (vals : List Limbs) :
    abDet π stmt w c =
      (chainChal ((chainOuts π gH gF
          (commitWith (permId π) (cellVars logRows) (membership logRows).wiringTable).run.root
          (commitWith (permId π) (cellVars logRows + 1) (wStackD w c)).run.root rQ (stmtBytesD stmt)
          vals).getD 0 default),
        chainChal ((chainOuts π gH gF
          (commitWith (permId π) (cellVars logRows) (membership logRows).wiringTable).run.root
          (commitWith (permId π) (cellVars logRows + 1) (wStackD w c)).run.root rQ (stmtBytesD stmt)
          vals).getD 1 default)) := by
  set ir := (commitWith (permId π) (cellVars logRows) (membership logRows).wiringTable).run.root
  set rW := (commitWith (permId π) (cellVars logRows + 1) (wStackD w c)).run.root
  have e1 := startWith_label π ir stmt
  have e2 := squeeze_root π gH gF
    (kDet π (QuotientZk.Deployed.kcTag ++ (Digest.toBytes ir).toList ++ (stmtBytesD stmt).toList)) rW
  calc abDet π stmt w c
      = (((((Transcript.Chain.startWith (permId π) (label ir stmt)).run.absorb
            (digestScalars rW).1).absorb (digestScalars rW).2).squeezeWith (permId π)).run.1,
          (((((Transcript.Chain.startWith (permId π) (label ir stmt)).run.absorb
            (digestScalars rW).1).absorb (digestScalars rW).2).squeezeWith (permId π)).run.2.squeezeWith
              (permId π)).run.1) := rfl
    _ = _ := by
      rw [e1, e2, squeeze_plain π gH gF]
      rfl

end Deployed

end PcsQuotient.EndToEnd.Core

/-- info: 'PcsQuotient.EndToEnd.Core.reduceWith_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.reduceWith_skel

/-- info: 'PcsQuotient.EndToEnd.Core.reduceWith_skel_claimsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.reduceWith_skel_claimsAt

/-- info: 'PcsQuotient.EndToEnd.Core.chainClaims_chainOuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.chainClaims_chainOuts

/-- info: 'PcsQuotient.EndToEnd.Core.dH_eq_chainChal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.dH_eq_chainChal

/-- info: 'PcsQuotient.EndToEnd.Core.startWith_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.startWith_label

/-- info: 'PcsQuotient.EndToEnd.Core.squeeze_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.squeeze_root

/-- info: 'PcsQuotient.EndToEnd.Core.squeeze_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.squeeze_plain

/-- info: 'PcsQuotient.EndToEnd.Core.squeeze_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.squeeze_vals

/-- info: 'PcsQuotient.EndToEnd.Core.abDet_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.abDet_eq

/-- info: 'PcsQuotient.EndToEnd.Core.redMsgs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.redMsgs_eq

/-- info: 'PcsQuotient.EndToEnd.Core.ofFn_redMsgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.ofFn_redMsgs

/-- info: 'PcsQuotient.EndToEnd.Core.eOfLimbs_limbsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.eOfLimbs_limbsOf

/-- info: 'PcsQuotient.EndToEnd.Core.reductionOf_valsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.reductionOf_valsOf

/-- info: 'PcsQuotient.EndToEnd.Core.takeScalars_valsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.takeScalars_valsOf

/-- info: 'PcsQuotient.EndToEnd.Core.claimsAt_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.claimsAt_some

/-- info: 'PcsQuotient.EndToEnd.Core.chainClaims_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.chainClaims_model

/-- info: 'PcsQuotient.EndToEnd.Core.pointW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.pointW_eq

/-- info: 'PcsQuotient.EndToEnd.Core.points_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.points_Q

/-- info: 'PcsQuotient.EndToEnd.Core.claimMsg_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.claimMsg_witness

/-- info: 'PcsQuotient.EndToEnd.Core.claimMsg_wiring'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.claimMsg_wiring'

/-- info: 'PcsQuotient.EndToEnd.Core.claimMsg_quotient'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.claimMsg_quotient'

/-- info: 'PcsQuotient.EndToEnd.Core.claims_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.claims_skel

/-- info: 'PcsQuotient.EndToEnd.Core.seed_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.seed_rel

/-- info: 'PcsQuotient.EndToEnd.Core.runDet_seed_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.runDet_seed_rel

/-- info: 'PcsQuotient.EndToEnd.Core.seed_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.seed_witness

/-- info: 'PcsQuotient.EndToEnd.Core.seed_wiring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.seed_wiring

/-- info: 'PcsQuotient.EndToEnd.Core.seed_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.seed_quotient
