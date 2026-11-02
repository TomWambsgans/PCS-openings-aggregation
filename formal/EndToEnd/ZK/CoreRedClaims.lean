-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The fields `K`, `E`, `y` and the bytes of a claim (`kBytes`) are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0), as `formal/Statement` uses them.
import ZK.CoreRedChain
import ZK.CoreTablesQuot
import Bridge.Claims
import E2ECompleteness.ProverValues
import E2ECompleteness.ProverClaims
import E2ECompleteness.ProverStatement

/-!
# The skeleton's values and claims are the statement's

* **The values** (**`redMsgs_eq`**): the joint model's reduction messages (`redMsgs` of the deployed
  first message `gKD w`, `vanD` and the masks) are the statement's prover's values at `t`: the four
  row values `rowValuesAt` of its witness table (`wHatD w`, the mask entries) and the wiring value
  `nextAt` of the circuit's wiring table (`E2ECompleteness.rowValuesAt_eq`, `nextAt_eq` on the
  deployed tables, `entry_W`, `wiring_table`).
* **The claims** (**`chainClaims_model`**): whenever the renderer's claims at the answers `h` and the
  values `v` exist (`chainClaims stmt h v = some cl`, the statement's `claimsAt` at the decoded
  answers), the joint model's claims at the challenges `chOf deployedRep.limbs h` (`modelWitness`,
  `modelWiring`, `modelQuotient`, `modelSum`, points then values) are the statement's claims
  (`claimsAt_some`, through `Bridge.claimsAt_eq_reduce` and Compose's `reduce`, any values, the
  target of any statement `target_stmtWD`). Hence the opening points (`pointW_eq`, `pointQ_eq`,
  `pointS_eq`) and the claims' bytes the skeleton hashes into each IV (`claimMsg_witness`,
  `claimMsg_wiring'`, `claimMsg_quotient'`: `claimBytes [cl.witness]`, `claimBytes [cl.wiring]`,
  `claimBytes [cl.quotient, cl.sum]`).
-/

open Polynomial QuotientSecurity
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open PcsQuotient.Domain
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Out Item)
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

open Render (limbsOf chainChal)

/-! ## The values -/

/-- **The statement's row values are the joint model's**: `rowValuesAt` of the witness table is F1's
value of the masked first message's row polynomials. -/
theorem rowValuesAt_eq_opened (w : Secret) (m : Masks) (t : E) (j : Fin 4) :
    (E2ECompleteness.rowValuesAt logRows (wHatD w) (maskEntries m) t).get j =
      Params.opened (committed (E := E) (gKD w) vanD m) t j := by
  rw [committed_eq]
  exact E2ECompleteness.rowValuesAt_eq (witTableD w m) (wHatD w) (maskEntries m)
    (by simp [maskEntries]) (fun i ↦ entry_W w m i) t j

/-- **The statement's wiring value is the joint model's**: `nextAt` of the circuit's wiring table is
F1's wiring polynomial at `t`. -/
theorem nextAt_eq_sigma (t : E) :
    E2ECompleteness.nextAt logRows (membership logRows).wiringTable t = P₀D.sigmaPoly.eval t := by
  have hσ : ∀ i, (membership logRows).wiringTable.getD i 0 =
      Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma) i := by
    rw [wiringTable_eq]
    exact (E2ECompleteness.ProverTables.wiring_table E2ECompleteness.constants
      (membership logRows).sigma E2ECompleteness.circuitMatch.sigmaSize
      E2ECompleteness.circuitMatch.sigma).2
  have hsp : P₀D.sigmaPoly = tablePoly fun b ↦
      algebraMap K E (Completeness.wiringTableK deployedBasis deployedSigma b) :=
    Completeness.sigmaPoly_eq_wiringTableK (algebraMap K E) Completeness.deployedInstanceE
      deployedBasis (fun _ ↦ rfl)
  rw [hsp]
  exact E2ECompleteness.nextAt_eq _ _ hσ t

/-- `redMsgs`, unfolded (generic: no deployed object is reduced). -/
theorem redMsgs_def {K' E' : Type} [Field K'] [Field E'] [Algebra K' E'] [DecidableEq E'] [CharP E' 2]
    [Fintype E'] (P : Params E') (gK : Fin 4 → K'[X]) (van : K'[X]) (t : E') (m : Fin 4 → Fin 3 → K') :
    redMsgs P gK van t m = (Params.opened (committed (E := E') gK van m) t, P.sigmaPoly.eval t) := rfl

/-- **The joint model's reduction messages are the statement's prover's values** at `t`: the four
row values and the wiring value, for every masks. -/
theorem redMsgs_eq (w : Secret) (t : E) (m : Masks) :
    redMsgs P₀D (gKD w) vanD t m =
      ((E2ECompleteness.rowValuesAt logRows (wHatD w) (maskEntries m) t).get,
        E2ECompleteness.nextAt logRows (membership logRows).wiringTable t) := by
  rw [redMsgs_def, nextAt_eq_sigma, Prod.mk.injEq]
  exact ⟨funext fun j ↦ (rowValuesAt_eq_opened w m t j).symm, rfl⟩

/-- The same, as the statement's reduction proof reads them (`Vector.ofFn`). -/
theorem ofFn_redMsgs (w : Secret) (t : E) (m : Masks) :
    Vector.ofFn (redMsgs P₀D (gKD w) vanD t m).1 =
      E2ECompleteness.rowValuesAt logRows (wHatD w) (maskEntries m) t := by
  rw [redMsgs_eq]
  exact ofFn_get_vec _

/-! ## The target -/

/-- **The reduction's target is F1's**, on the statement's words of any statement (`target_stmt`
without the witness). -/
theorem target_stmtWD (stmt : Statement) (γ : E) :
    P₀D.target (stmtWD stmt) γ =
      Compose.Reduce.target (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) γ := by
  show Completeness.deployedInstanceE.params.target _ γ = _
  unfold stmtWD
  rw [QuotientSecurity.statementWords_eq]
  have ht := QuotientSecurity.membership_target Completeness.deployedInstanceE.basis
    QuotientSecurity.le24 Completeness.deployedInstanceE.wiring
    (QuotientSecurity.invSeq Completeness.deployedInstanceE.basis.β) Completeness.deployedInstanceE.c
    (QuotientSecurity.invSeq_zero _)
    (fun d hd _ ↦ QuotientSecurity.invSeq_sum Completeness.deployedInstanceE.basis.β
      Completeness.deployedInstanceE.basis.zero d hd)
    (QuotientSecurity.halves Primitives.F192.G Primitives.F192.Y (fun i ↦ stmt.y[i])
      (fun i ↦ stmt.root[i])) γ
  refine ht.trans ?_
  simp only [QuotientSecurity.halves, Compose.Reduce.target, Compose.Reduce.stmtHalves,
    E2ECompleteness.yOf_append, E2ECompleteness.rootOf_append, E2ECompleteness.half_eq_stmtHalf,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

/-! ## The claims -/

theorem Y_eq_y : (F192.Y : E) = y := Primitives.F192.Y_eq_gen

/-- **The statement's claims are the joint model's**, at any challenges and values: whenever
`claimsAt` returns claims, their points then values are `modelWitness`, `modelWiring`,
`modelQuotient`, `modelSum` (the deployed parameters, `Y`, the statement's words). -/
theorem claimsAt_some (stmt : Statement) (α β γ t ρ : E) (a : Fin 4 → E) (next : E) (cl : Claims)
    (h : claimsAt logRows stmt α β γ t ρ (Vector.ofFn a) next = some cl) :
    Implementation.modelWitness t ρ a = cl.witness.point ++ [cl.witness.value] ∧
      Implementation.modelWiring t next = cl.wiring.point ++ [cl.wiring.value] ∧
      Implementation.modelQuotient P₀D α β γ t ρ next F192.Y a =
        cl.quotient.point ++ [cl.quotient.value] ∧
      Implementation.modelSum P₀D (stmtWD stmt) γ F192.Y = cl.sum.point ++ [cl.sum.value] := by
  have hred := Bridge.claimsAt_eq_reduce stmt α β γ t ρ (Vector.ofFn a) next
  have hfa : (fun i : Fin 4 ↦ (Vector.ofFn a).get i) = a := funext fun i ↦ Vector.get_ofFn _ _
  rw [hfa] at hred
  have h' : claimsAt 22 stmt α β γ t ρ (Vector.ofFn a) next = some cl := h
  rw [hred] at h'
  obtain ⟨r, hr, hcl⟩ := Option.map_eq_some_iff.mp h'
  obtain ⟨-, rfl⟩ := Compose.Reduce.reduce_eq_some hr
  subst hcl
  set S := Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)
  set C := Bridge.statementConsts
  -- The deployed instance's formulas at the statement's constants (`claimsAt_honest`).
  have hM := E2ECompleteness.matches_deployed E2ECompleteness.constants
  have hx : ∀ i, Compose.Reduce.rowCells C t a i = Completeness.deployedInstanceE.params.cellAt a t i :=
    Compose.Reduce.rowCells_eq C _ hM.theta t a
  have hvc : Completeness.deployedInstanceE.params.vCells.eval t = sq^[22 + 2] t := by
    rw [hM.vCells, digitPoly_eval]
  have hden : Completeness.deployedInstanceE.params.claimDen α β t a next =
      Compose.Reduce.product C α β t a next + sq^[22 + 2] t := by
    rw [Params.claimDen, hvc, Compose.Reduce.product, hx 0]
  have hval : Completeness.deployedInstanceE.params.claimValue α β γ t ρ a next =
      Compose.Reduce.identities C (22 + 2) α β t a next γ ρ /
        (Compose.Reduce.product C α β t a next + sq^[22 + 2] t) /
          Compose.Reduce.rows C (22 + 2) t := by
    rw [Params.claimValue, hden, hM.pub, hM.rows, Compose.Reduce.identities,
      Compose.Reduce.product, Compose.Reduce.gate4, ← hx 0, ← hx 1, ← hx 2, ← hx 3, div_div]
    rfl
  -- The points.
  have hWp : (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).witness.point =
      List.ofFn (Fin.cons ρ (Fin.cons (ρ ^ 2) (claimPoint 2 (22 + 1) t)) :
        Fin (22 + 1 + 1 + 1) → E) :=
    E2ECompleteness.list_eq_ofFn _ (by rw [Compose.Reduce.witness_point_eq]; simp) _
      (Compose.Reduce.witness_point C 22 S α β γ t a next ρ)
  have hσp : (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).wiring.point =
      List.ofFn (claimPoint 0 (22 + 2) t) :=
    E2ECompleteness.list_eq_ofFn _ (by rw [Compose.Reduce.wiring_point_eq]; simp) _
      (Compose.Reduce.wiring_point C 22 S α β γ t a next ρ)
  have hQp : (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).quotient.point =
      List.ofFn (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) t)
        (Completeness.deployedInstanceE.params.vCells.eval t /
          Completeness.deployedInstanceE.params.claimDen α β t a next)) ρ) (y / (1 + y)))
        (y ^ 2 / (1 + y ^ 2)) : Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → E) := by
    have hp := Compose.Reduce.quotient_point C 22 S α β γ t a next ρ
    rw [← hden, ← hvc] at hp
    exact E2ECompleteness.list_eq_ofFn _ (by rw [Compose.Reduce.quotient_point_eq]; simp) _ hp
  have hSp : (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).sum.point =
      List.ofFn (QuotientSecurity.sumPoint (22 + 2) y) :=
    E2ECompleteness.list_eq_ofFn _ (by
        rw [Compose.Reduce.sum_point_eq, Compose.Reduce.sumPoint]; simp) _
      (Compose.Reduce.sum_point C 22 S α β γ t a next ρ)
  -- The values.
  have hWv := Compose.Reduce.witness_value C 22 S α β γ t a next ρ (by norm_num)
  have hσv := Compose.Reduce.wiring_value C 22 S α β γ t a next ρ (by norm_num)
  have hQv : (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).quotient.value =
      Completeness.deployedInstanceE.params.claimValue α β γ t ρ a next / ((1 + y) * (1 + y ^ 2)) /
        claimScale 0 (22 + 2 + 1 + 1) t := by
    rw [Compose.Reduce.quotient_value C 22 S α β γ t a next ρ (by norm_num), hval]
  have hSv : (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).sum.value =
      P₀D.target (stmtWD stmt) γ / ((1 + y) * (1 + y ^ 2)) := by
    rw [Compose.Reduce.sum_value C 22 S α β γ t a next ρ, target_stmtWD]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show _ = (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).witness.point ++
      [(Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).witness.value]
    rw [hWp, hWv]
    rfl
  · show _ = (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).wiring.point ++
      [(Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).wiring.value]
    rw [hσp, hσv]
    rfl
  · show _ = (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).quotient.point ++
      [(Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).quotient.value]
    rw [hQp, hQv, ← Y_eq_y]
    rfl
  · show _ = (Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).sum.point ++
      [(Compose.Reduce.claimsOf C 24 S α β γ t a next ρ).sum.value]
    rw [hSp, hSv, ← Y_eq_y]
    rfl

/-- **The renderer's claims are the joint model's**, at the challenges the answers `h` decode to
(`chOf deployedRep.limbs h`, whose chain challenges are `chainChal` of the first five answers,
`dH_eq_chainChal`), for any answers and values. -/
theorem chainClaims_model (stmt : Statement) (h : List Out) (v : Vals E) (cl : Claims)
    (hcl : Render.chainClaims stmt h v = some cl) :
    Implementation.modelWitness (chOf deployedRep.limbs h).1.1.2 (chOf deployedRep.limbs h).1.2 v.1 =
        cl.witness.point ++ [cl.witness.value] ∧
      Implementation.modelWiring (chOf deployedRep.limbs h).1.1.2 v.2 =
        cl.wiring.point ++ [cl.wiring.value] ∧
      Implementation.modelQuotient P₀D (chOf deployedRep.limbs h).1.1.1.1
          (chOf deployedRep.limbs h).1.1.1.2.1 (chOf deployedRep.limbs h).1.1.1.2.2
          (chOf deployedRep.limbs h).1.1.2 (chOf deployedRep.limbs h).1.2 v.2 F192.Y v.1 =
        cl.quotient.point ++ [cl.quotient.value] ∧
      Implementation.modelSum P₀D (stmtWD stmt) (chOf deployedRep.limbs h).1.1.1.2.2 F192.Y =
        cl.sum.point ++ [cl.sum.value] := by
  simp only [chOf_fst, dH_eq_chainChal]
  exact claimsAt_some stmt _ _ _ _ _ v.1 v.2 cl hcl

/-! ## The opening points -/

theorem left_of_append_singleton {l l' : List E} {x x' : E} (h : l ++ [x] = l' ++ [x']) : l = l' :=
  (List.append_inj' h rfl).1

theorem pointW_eq (stmt : Statement) (h : List Out) (v : Vals E) (cl : Claims)
    (hcl : Render.chainClaims stmt h v = some cl) :
    pointW (chOf deployedRep.limbs h) = cl.witness.point := by
  have e := (chainClaims_model stmt h v cl hcl).1
  rw [modelWitness_eq] at e
  exact left_of_append_singleton e

theorem pointQ_eq (stmt : Statement) (h : List Out) (v : Vals E) (cl : Claims)
    (hcl : Render.chainClaims stmt h v = some cl) :
    pointQ P₀D F192.Y (chOf deployedRep.limbs h) v = cl.quotient.point := by
  have e := (chainClaims_model stmt h v cl hcl).2.2.1
  rw [modelQuotient_eq] at e
  exact left_of_append_singleton e

theorem pointS_eq (stmt : Statement) (h : List Out) (v : Vals E) (cl : Claims)
    (hcl : Render.chainClaims stmt h v = some cl) :
    pointS F192.Y = cl.sum.point := by
  have e := (chainClaims_model stmt h v cl hcl).2.2.2
  rw [modelSum_eq P₀D (stmtWD stmt) F192.Y (chOf deployedRep.limbs h)] at e
  exact left_of_append_singleton e

/-- **The quotient opening's points**, as a list. -/
theorem points_Q (stmt : Statement) (h : List Out) (v : Vals E) (cl : Claims)
    (hcl : Render.chainClaims stmt h v = some cl) :
    [pointQ P₀D F192.Y (chOf deployedRep.limbs h) v, pointS F192.Y] =
      [cl.quotient.point, cl.sum.point] := by
  rw [pointQ_eq stmt h v cl hcl, pointS_eq stmt h v cl hcl]

/-! ## The claims' bytes -/

/-- A list's bytes in the deployed prover's IV are the statement's (`eBytes`). -/
theorem scalarsLE_eq (l : List E) : scalarsLE deployedRep l = l.flatMap eBytes := rfl

theorem claimBytes_one (c : Claim) : claimBytes [c] = scalarsLE deployedRep (c.point ++ [c.value]) := by
  rw [scalarsLE_eq]
  simp only [claimBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem claimBytes_two (c d : Claim) :
    claimBytes [c, d] = scalarsLE deployedRep ((c.point ++ [c.value]) ++ (d.point ++ [d.value])) := by
  rw [scalarsLE_eq]
  simp only [claimBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_append]

/-- **The witness opening's claims' bytes** (the skeleton's IV input at step `5`) are
`claimBytes [cl.witness]`. -/
theorem claimMsg_witness (stmt : Statement) (h : List Out) (v : Vals E) (cl : Claims)
    (hcl : Render.chainClaims stmt h v = some cl) :
    claimMsg deployedRep P₀D (stmtWD stmt) F192.Y 5 (chOf deployedRep.limbs h) v =
      [.bytes (claimBytes [cl.witness])] := by
  refine (claimMsg_five ..).trans ?_
  rw [(chainClaims_model stmt h v cl hcl).1, claimBytes_one]

/-- **The wiring opening's** (step `128`): `claimBytes [cl.wiring]`. -/
theorem claimMsg_wiring' (stmt : Statement) (h : List Out) (v : Vals E) (cl : Claims)
    (hcl : Render.chainClaims stmt h v = some cl) :
    claimMsg deployedRep P₀D (stmtWD stmt) F192.Y 128 (chOf deployedRep.limbs h) v =
      [.bytes (claimBytes [cl.wiring])] := by
  refine (claimMsg_wiring ..).trans ?_
  rw [(chainClaims_model stmt h v cl hcl).2.1, claimBytes_one]

/-- **The quotient opening's** (step `242`): `claimBytes [cl.quotient, cl.sum]`. -/
theorem claimMsg_quotient' (stmt : Statement) (h : List Out) (v : Vals E) (cl : Claims)
    (hcl : Render.chainClaims stmt h v = some cl) :
    claimMsg deployedRep P₀D (stmtWD stmt) F192.Y 242 (chOf deployedRep.limbs h) v =
      [.bytes (claimBytes [cl.quotient, cl.sum])] := by
  refine (claimMsg_quotient ..).trans ?_
  rw [(chainClaims_model stmt h v cl hcl).2.2.1, (chainClaims_model stmt h v cl hcl).2.2.2,
    claimBytes_two]

/-- **The causality of the claims**: the renderer's claims read only the first five answers. -/
theorem chainClaims_take (stmt : Statement) (h : List Out) (v : Vals E) :
    Render.chainClaims stmt (h.take 5) v = Render.chainClaims stmt h v := by
  unfold Render.chainClaims
  rw [getD_take_of_lt h default (show 0 < 5 by norm_num),
    getD_take_of_lt h default (show 1 < 5 by norm_num),
    getD_take_of_lt h default (show 2 < 5 by norm_num),
    getD_take_of_lt h default (show 3 < 5 by norm_num),
    getD_take_of_lt h default (show 4 < 5 by norm_num)]

end PcsQuotient.EndToEnd.Core
