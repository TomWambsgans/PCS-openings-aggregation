-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- `ClaimsMatchH` restates Bridge-Defs' `Bridge.ClaimsMatch` (formal/EndToEnd/Bridge/Verifier.lean at
-- worktree-agent-a9857ef0660456f3e, 96e3755). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.ProverConstants

/-!
# The Statement's claims on the honest values are `formal/Completeness`'s

The Statement's reduction computes its four claims by `claimsAt` (`Reduction.lean`, the Rust's
`reduce`); `formal/Completeness` states F1's completeness for its own claims (`witnessClaim`,
`wiringClaim`, `quotientClaim`, `sumClaim`, `Deployed.lean`). Through Compose's transcription of
`reduce` (`Compose.Reduce.reduce`, whose claims are F1's formulas, `witness_point` …):

* `ClaimsMatchH c`: the Statement's claims are `Compose.Reduce.reduce`'s at the constants `c`
  (Bridge-Defs' `Bridge.ClaimsMatch`, which its `Bridge/Claims.lean` is to prove at the Statement's
  constants; taken here as a hypothesis);
* **`claimsAt_honest`**: at a non-degenerate `t` (`¬ Degenerate`, the Rust's own check on the honest
  values), on the honest values `Params.opened g t` and the wiring polynomial at `t`, `claimsAt`
  returns claims whose points and values are Completeness's four claims, for a statement whose
  target is F1's.
-/

open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain Finset Polynomial
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness

/-- A claim of the Statement as F2's. -/
def claimTrH (c : PcsQuotient.Claim) : WhirBridge.Claim := ⟨c.point, c.value⟩

/-- The Statement's four claims as Compose's `reduce` outputs them. -/
def claimsTrH (cl : PcsQuotient.Claims) : Compose.Reduce.Reduced :=
  ⟨claimTrH cl.witness, claimTrH cl.wiring, claimTrH cl.quotient, claimTrH cl.sum⟩

/-- **The Statement's claims are `reduce`'s at the constants `c`** (Bridge-Defs' `Bridge.ClaimsMatch`,
the same proposition). -/
def ClaimsMatchH (c : Compose.Reduce.Consts) : Prop :=
  ∀ (stmt : PcsQuotient.Statement) (α β γ t ρ : E) (a : Vector E 4) (next : E),
    (PcsQuotient.claimsAt 22 stmt α β γ t ρ a next).map claimsTrH =
      Compose.Reduce.reduce c 24 (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t
        (fun i ↦ a.get i) next ρ

/-- A list of length `n` whose entries are `f`'s is `List.ofFn f`. -/
theorem list_eq_ofFn {n : ℕ} (l : List E) (hl : l.length = n) (f : Fin n → E)
    (h : (fun k : Fin n ↦ l.getD k 0) = f) : l = List.ofFn f := by
  subst h
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  rw [List.getElem_ofFn]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem claim_eq {c : WhirBridge.Claim} {p : List E} {v : E} (hp : c.point = p)
    (hv : c.value = v) : c = ⟨p, v⟩ := by
  cases c
  cases hp
  cases hv
  rfl

/-- The instance. -/
local notation "I" => Completeness.deployedInstanceE

/-- **The Statement's claims on the honest values are Completeness's**: at a `t` where the honest
values pass the Rust's check (`¬ Degenerate`), `claimsAt` returns claims whose points and values are
`witnessClaim`, `wiringClaim`, `quotientClaim` and `sumClaim`, for a statement whose target at `γ`
is F1's target of the words `stmtW`. -/
theorem claimsAt_honest (hK : Constants) (hcl : ClaimsMatchH stmtConsts)
    (stmt : PcsQuotient.Statement) (stmtW : Fin 8 → E) (g : Fin 4 → E[X]) (α β γ t ρ : E)
    (htarget : (I).params.target stmtW γ =
      Compose.Reduce.target (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) γ)
    (ht : ¬ Completeness.Reduction.Degenerate I g α β t) :
    ∃ cl, PcsQuotient.claimsAt 22 stmt α β γ t ρ (Vector.ofFn (Params.opened g t))
        ((I).params.sigmaPoly.eval t) = some cl ∧
      claimTrH cl.witness = Completeness.witnessClaim t ρ (Params.opened g t) ∧
      claimTrH cl.wiring = Completeness.wiringClaim t ((I).params.sigmaPoly.eval t) ∧
      claimTrH cl.quotient =
        Completeness.quotientClaim I α β γ t ρ (Params.opened g t) ((I).params.sigmaPoly.eval t) ∧
      claimTrH cl.sum = Completeness.sumClaim I stmtW γ := by
  set a := Params.opened g t with ha
  set next := (I).params.sigmaPoly.eval t with hnext
  have hM := matches_deployed hK
  have hx : ∀ i, Compose.Reduce.rowCells stmtConsts t a i = (I).params.cellAt a t i :=
    Compose.Reduce.rowCells_eq stmtConsts (I).params hM.theta t a
  have hvc : (I).params.vCells.eval t = sq^[22 + 2] t := by rw [hM.vCells, digitPoly_eval]
  have hden : (I).params.claimDen α β t a next =
      Compose.Reduce.product stmtConsts α β t a next + sq^[22 + 2] t := by
    rw [Params.claimDen, hvc, Compose.Reduce.product, hx 0]
  have hval : (I).params.claimValue α β γ t ρ a next =
      Compose.Reduce.identities stmtConsts (22 + 2) α β t a next γ ρ /
        (Compose.Reduce.product stmtConsts α β t a next + sq^[22 + 2] t) /
          Compose.Reduce.rows stmtConsts (22 + 2) t := by
    rw [Params.claimValue, hden, hM.pub, hM.rows, Compose.Reduce.identities,
      Compose.Reduce.product, Compose.Reduce.gate4, ← hx 0, ← hx 1, ← hx 2, ← hx 3, div_div]
    rfl
  -- The Rust's check on the honest values.
  have hrc := (Completeness.Reduction.rustCheck_honest I g α β t).mpr ht
  obtain ⟨hw, hcd⟩ := hrc
  have hcd' : (I).params.claimDen α β t a next * (I).params.vRows.eval t ≠ 0 := hcd
  have hnz : (Compose.Reduce.denominators stmtConsts (22 + 2) α β t a next).prod ≠ 0 := by
    refine List.prod_ne_zero fun h0 ↦ ?_
    rw [Compose.Reduce.denominators, List.mem_append, List.mem_map] at h0
    rcases h0 with ⟨k, hk, hk0⟩ | h0
    · rw [Compose.Reduce.wChain_eq] at hk0
      exact hw ⟨k, List.mem_range.mp hk⟩ hk0
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h0
      rcases h0 with h0 | h0
      · rw [Compose.Reduce.wChain_eq, ← hden] at h0
        exact hcd' (by rw [← h0, zero_mul])
      · rw [← hM.rows] at h0
        exact hcd' (by rw [← h0, mul_zero])
  -- The Statement's claims are `reduce`'s, which returns `claimsOf`.
  have hred := hcl stmt α β γ t ρ (Vector.ofFn a) next
  have hfa : (fun i : Fin 4 ↦ (Vector.ofFn a).get i) = a := funext fun i ↦ Vector.get_ofFn _ _
  rw [hfa] at hred
  unfold Compose.Reduce.reduce at hred
  rw [if_neg hnz] at hred
  rcases hcs : PcsQuotient.claimsAt 22 stmt α β γ t ρ (Vector.ofFn a) next with _ | cl
  · rw [hcs] at hred; exact absurd hred (by simp)
  rw [hcs, Option.map_some, Option.some.injEq] at hred
  have hW : claimTrH cl.witness = _ := congrArg Compose.Reduce.Reduced.witness hred
  have hσ : claimTrH cl.wiring = _ := congrArg Compose.Reduce.Reduced.wiring hred
  have hQ : claimTrH cl.quotient = _ := congrArg Compose.Reduce.Reduced.quotient hred
  have hS : claimTrH cl.sum = _ := congrArg Compose.Reduce.Reduced.sum hred
  set st := Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)
  refine ⟨cl, rfl, ?_, ?_, ?_, ?_⟩
  · -- The witness claim.
    rw [hW]
    exact claim_eq (list_eq_ofFn _ (by rw [Compose.Reduce.witness_point_eq]; simp) _
      (Compose.Reduce.witness_point stmtConsts 22 st α β γ t a next ρ))
      (Compose.Reduce.witness_value stmtConsts 22 st α β γ t a next ρ (by norm_num))
  · -- The wiring claim.
    rw [hσ]
    exact claim_eq (list_eq_ofFn _ (by rw [Compose.Reduce.wiring_point_eq]; simp) _
      (Compose.Reduce.wiring_point stmtConsts 22 st α β γ t a next ρ))
      (Compose.Reduce.wiring_value stmtConsts 22 st α β γ t a next ρ (by norm_num))
  · -- The quotient claim.
    rw [hQ]
    have hp := Compose.Reduce.quotient_point stmtConsts 22 st α β γ t a next ρ
    rw [← hden, ← hvc] at hp
    refine claim_eq (list_eq_ofFn _ (by rw [Compose.Reduce.quotient_point_eq]; simp) _ hp) ?_
    rw [Compose.Reduce.quotient_value stmtConsts 22 st α β γ t a next ρ (by norm_num), hval]
  · -- The sum claim.
    rw [hS]
    refine claim_eq (list_eq_ofFn _ (by
        rw [Compose.Reduce.sum_point_eq, Compose.Reduce.sumPoint]; simp) _
      (Compose.Reduce.sum_point stmtConsts 22 st α β γ t a next ρ)) ?_
    rw [Compose.Reduce.sum_value stmtConsts 22 st α β γ t a next ρ, htarget]

end E2ECompleteness

/-- info: 'E2ECompleteness.claimsAt_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.claimsAt_honest
