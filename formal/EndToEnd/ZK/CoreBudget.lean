-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The functions costed are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/Keccak.lean`'s `keccak256With`; `Statement/LeanVmVerifier.lean`'s `verifyStackedOpening`)
-- and `formal/Statement`'s (`setupWith`, `reduceWith`, `claimsAt`, `openingSpongeWith`); the program's
-- cost bound is `lean_vm/LeanVM/Protocol/Verifier/Cost.lean`'s (`costs_verifyStackedOpening`,
-- `ladder_cost`, `costHeight = 26`, `whirBound = 40475`).
import ZK.CoreBudgetCalc

/-!
# The formatting stays within its budget

`fmt stmt pf = budgeted fmtBudget (fmtCore stmt pf)` (`ZK/Format.lean`, `fmtBudget = 2^23`): past `2^23`
calls of `π`, no proof. On the proofs the skeleton makes the budget is never reached:

* **`FmtSmall pf`**: every opening of the skeleton's proof has at most `8` pruned multiproofs, each of
  at most `2^10` positions and rows of at most `2^10` words: generous bounds, the skeleton opening at
  most `225` positions per query phase in at most `6` phases, rows of `64` to `192` words.
* **`qb_fmtCore`**: then every path of `fmtCore stmt pf` makes at most
  `fmtCalls = 5 · 2^19 + 7 + 3 · openBudget = 4 881 047 < 2^23` calls of `π`, whatever `π` answers:
  the circuit's commitment `5 · 2^19` (`2^19` leaves of `512` bytes, four blocks each, and fewer than
  `2^19` nodes), the reduction's chain `7` (six hashes, the last of `192` bytes), and per opening
  `openBudget = 753 200`: the opening's sponge `13` (an IV of at most `76 + 1488` bytes), the root's two
  scalars, the verifier's program `40 481` quarters of a query (mumbai's `costs_verifyStackedOpening`
  over every admissible ladder, commitments of height at most `26`), and at most `8` multiproofs of at
  most `2^10 · (61 + 26)` calls each.
* **`budgeted_eq_self`**: a computation of at most `n` calls on every path is its own `budgeted n`
  (`budgetImpl` never runs out, so the run stays `ok`).

**`fmtDet_eq_core`**: for every permutation `π`, `fmtDet π stmt pf` is `fmtCore`'s run against `π`.
-/

open OracleComp OracleSpec
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## The budget never reached -/

theorem budget_run {α : Type} (X : OracleComp PermSpec α) :
    ∀ (b : ℕ) (ok : Bool), IsTotalQueryBound X b →
      ((simulateQ budgetImpl X).run (b, ok) >>= fun z ↦ pure (z.1, z.2.2)) =
        (X >>= fun a ↦ pure (a, ok)) := by
  induction X using OracleComp.inductionOn with
  | pure a => intro b ok _; simp [simulateQ_pure, StateT.run_pure]
  | query_bind q k ih =>
    intro b ok h
    rw [isTotalQueryBound_query_bind_iff] at h
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    change (((fun a ↦ (a, (b, ok))) <$>
      (liftM (PermSpec.query q) : OracleComp PermSpec _)) >>= _) >>= _ = _
    rw [bind_map_left, bind_assoc, bind_assoc]
    refine bind_congr fun u ↦ ?_
    simpa using ih u b ok (by simpa using h.2 u)

/-- **A computation of at most `n` calls on every path is its own `budgeted n`.** -/
theorem budgeted_eq_self {α : Type} (n : ℕ) (X : OracleComp PermSpec (Option α))
    (h : IsTotalQueryBound X n) : budgeted n X = X := by
  unfold budgeted
  have e := budget_run X n true h
  calc ((simulateQ budgetImpl X).run (n, true) >>= fun z ↦ pure (if z.2.2 then z.1 else none))
      = (((simulateQ budgetImpl X).run (n, true) >>= fun z ↦ pure (z.1, z.2.2)) >>=
          fun z ↦ pure (if z.2 then z.1 else none)) := by
        rw [bind_assoc]; simp only [pure_bind]
    _ = X := by rw [e, bind_assoc]; simp

/-! ## The circuit's commitment -/

/-- **The circuit's commitment**: a tree of `2^19` rows of `64` words, at most `5 · 2^19` calls. -/
theorem qb_setupWith : QB (setupWith permF) (2 ^ 19 * 5) fun _ ↦ True := by
  unfold setupWith Circuit.indexRootWith commitWith
  have hμ : (membership logRows).logRows = 22 := rfl
  refine (qb_buildTreeM _ _ fun p ↦ (len_stackWordFast _ _ _ p).le).bind_le
    (fun _ _ ↦ qb_ret _ 0) ?_
  rw [hμ]
  norm_num

/-! ## The reduction's chain -/

theorem len_scalarBytes (x : E) : (Transcript.scalarBytes x).length = 32 := by
  simp [Transcript.scalarBytes, Transcript.beBytes, len_wordBytes]

theorem len_label (ir : Digest) (stmt : Statement) : (label ir stmt).length = 112 := by
  simp only [label, List.length_append, len_digestBytes, Vector.length_toList]
  have h16 : "pcs-quotient-kc1".toUTF8.toList.length = 16 := by decide +kernel
  omega

theorem qb_startWith (lbl : List UInt8) (h : lbl.length < 136) :
    QB (Transcript.Chain.startWith permF lbl) 1 fun c ↦ c.pending = [] := by
  unfold Transcript.Chain.startWith
  exact (qb_keccak256With_le (k := 1) (by omega)).bind_le (fun _ _ ↦ (qb_pure _ 0 _).2 rfl) le_rfl

theorem qb_squeezeWith (c : Transcript.Chain) {k : ℕ} (h : 32 + 32 * c.pending.length < 136 * k) :
    QB (c.squeezeWith permF) k fun r ↦ r.2.pending = [] := by
  unfold Transcript.Chain.squeezeWith
  refine (qb_keccak256With_le ?_).bind_le (fun _ _ ↦ (qb_pure _ 0 _).2 rfl) le_rfl
  rw [List.length_append, len_digestBytes, List.length_flatMap]
  simp only [len_scalarBytes, List.map_const', List.sum_replicate, smul_eq_mul]
  omega

theorem pending_absorb (c : Transcript.Chain) (x : E) : (c.absorb x).pending = c.pending ++ [x] :=
  rfl

theorem pending_foldl_absorb : ∀ (l : List E) (c : Transcript.Chain),
    (l.foldl Transcript.Chain.absorb c).pending = c.pending ++ l
  | [], c => by simp
  | x :: l, c => by rw [List.foldl_cons, pending_foldl_absorb l, pending_absorb]; simp

/-- **Claims whose points have at most `cellVars lr + 6` coordinates.** -/
def ClaimsSmall (lr : ℕ) (cl : Claims) : Prop :=
  cl.witness.point.length ≤ cellVars lr + 6 ∧ cl.wiring.point.length ≤ cellVars lr + 6 ∧
    cl.quotient.point.length ≤ cellVars lr + 6 ∧ cl.sum.point.length ≤ cellVars lr + 6

/-- The claims the reduction computes have points of at most `cellVars lr + 6` coordinates. -/
theorem claimsSmall_claimsAt (lr : ℕ) (stmt : Statement) (α β γ t ρ : E) (a : Vector E 4)
    (next : E) (cl : Claims) (h : claimsAt lr stmt α β γ t ρ a next = some cl) :
    ClaimsSmall lr cl := by
  unfold claimsAt at h
  dsimp only at h
  rw [Option.ite_none_left_eq_some] at h
  obtain ⟨-, h⟩ := h
  have h' := Option.some.inj h
  subst h'
  simp only [ClaimsSmall, List.length_append, List.length_take, List.length_drop,
    List.length_map, List.length_range, List.length_cons, List.length_nil, sumPoint,
    List.length_replicate]
  omega

/-- The reduction's result: none, or claims with small points. -/
def RedSmall (lr : ℕ) : Option Reduced → Prop
  | none => True
  | some r => ClaimsSmall lr r.claims

/-- **The reduction's chain**: six hashes, seven calls. -/
theorem qb_reduceWith (lr : ℕ) (ir : Digest) (stmt : Statement) (p : ReductionProof) :
    QB (reduceWith permF lr ir stmt p) 7 (RedSmall lr) := by
  unfold reduceWith
  split
  · exact (qb_pure _ _ _).2 trivial
  · refine (qb_startWith _ (by rw [len_label]; omega)).bind_le (b := 6) (fun c hc ↦ ?_) le_rfl
    dsimp only
    split
    · exact (qb_pure _ _ _).2 trivial
    · refine (qb_squeezeWith _ (k := 1) ?_).bind_le (b := 5) (fun x hx ↦ ?_) le_rfl
      · simp [pending_absorb, hc]
      obtain ⟨α, c⟩ := x
      dsimp only at hx ⊢
      refine (qb_squeezeWith _ (k := 1) (by simp [hx])).bind_le (b := 4) (fun x hx ↦ ?_) le_rfl
      obtain ⟨β, c⟩ := x
      dsimp only at hx ⊢
      refine (qb_squeezeWith _ (k := 1) (by simp [hx])).bind_le (b := 3) (fun x hx ↦ ?_) le_rfl
      obtain ⟨γ, c⟩ := x
      dsimp only at hx ⊢
      split
      · exact (qb_pure _ _ _).2 trivial
      · refine (qb_squeezeWith _ (k := 1) ?_).bind_le (b := 2) (fun x hx ↦ ?_) le_rfl
        · simp [pending_absorb, hx]
        obtain ⟨t, c⟩ := x
        dsimp only at hx ⊢
        refine (qb_squeezeWith _ (k := 2) ?_).bind_le (b := 0) (fun x _ ↦ ?_) le_rfl
        · rw [pending_absorb, pending_foldl_absorb, hx]
          simp
        obtain ⟨ρ, c⟩ := x
        dsimp only
        refine (qb_pure _ _ _).2 ?_
        cases hcl : claimsAt lr stmt α β γ t ρ p.values p.next with
        | none => trivial
        | some cl => exact claimsSmall_claimsAt lr stmt α β γ t ρ p.values p.next cl hcl

/-! ## The openings -/

theorem len_flatMap_eBytes (l : List E) : (l.flatMap eBytes).length = 24 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [eBytes, kBytes, List.length_append, len_wordBytes]
    ring

theorem len_claimBytes_cons (c : Claim) (cs : List Claim) :
    (claimBytes (c :: cs)).length = 24 * (c.point.length + 1) + (claimBytes cs).length := by
  simp only [claimBytes, List.flatMap_cons, List.length_append, len_flatMap_eBytes,
    List.length_cons, List.length_nil]

theorem len_claimBytes_nil : (claimBytes []).length = 0 := rfl

theorem len_openingLabel : openingLabel.length = 20 := by decide +kernel

/-- **The opening's sponge**: the IV's hash and one permutation. -/
theorem qb_openingSpongeWith (L : Layout) (claims : List Claim) {k : ℕ}
    (h : 76 + (claimBytes claims).length < 136 * k) :
    QB (openingSpongeWith permF L claims) (k + 1) fun _ ↦ True := by
  unfold openingSpongeWith
  refine (qb_keccak256With_le ?_).bind_le (fun _ _ ↦
    (qb_permF _).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl) le_rfl
  simp only [List.length_append, len_openingLabel, len_digestBytes, u64Bytes, len_wordBytes]
  omega

/-- The calls of one multiproof's expansion, at most. -/
def multiBudget : ℕ := 2 ^ 10 * 61 + costHeight * 2 ^ 10

/-- The calls of one opening's formatting, at most: its sponge, the root's scalars, the verifier's
program, eight multiproofs. -/
def openBudget : ℕ := 13 + 2 + (4 + (2 + whirBound)) + 8 * multiBudget

theorem qb_expandMulti_le (mp : Multi) (hmp : MultiSmall mp) (h : ℕ) (hh : h ≤ costHeight)
    (ps : List ℕ) : QB (expandMulti mp h ps) multiBudget fun _ ↦ True :=
  (qb_expandMulti mp h ps hmp).mono (Nat.add_le_add (Nat.mul_le_mul_right 61 hmp.1)
    (Nat.mul_le_mul hh hmp.1)) fun _ h ↦ h

/-- **The verifier's program of an opening, run by `fmt`**: its `40 481` quarters, and one
expansion per multiproof. -/
theorem qb_fillRun_opening (L : Layout) (claims : List Claim) (sp : Sponge) (rest : List E)
    (root : Digest) (multis : List Multi) (hL : L.logN - laneFold + logInvRate ≤ costHeight)
    (hm : ∀ mp ∈ multis, MultiSmall mp) :
    QB (fillRun (verifyStackedOpening L.logN logInvRate (stackClaims L claims))
        ⟨sp, rest, multis, [(root, L.logN - laneFold + logInvRate, 2 ^ laneFold)], []⟩)
      ((4 + (2 + whirBound)) + multis.length * multiBudget) fun _ ↦ True :=
  qb_fillRun costHeight multiBudget (fun mp hmp h hh ps ↦ qb_expandMulti_le mp hmp h hh ps) _ _ _
    (costs_verifyStackedOpening (height := costHeight) L.logN logInvRate (stackClaims L claims)
      whirBound fun levels h ↦ ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2.1,
        (ladder_cost _ _ levels h).2.2.2⟩)
    (fun r hr ↦ by rw [List.mem_singleton] at hr; subst hr; exact hL) hm

/-- **An opening's formatting**: at most `openBudget` calls, for claims of at most `1488` bytes, a
layout whose tree has height at most `26` and at most eight small multiproofs. -/
theorem qb_fillOpening (L : Layout) (root : Digest) (claims : List Claim)
    (o : List QuotientRpm.Limbs × List Multi) (hcl : 76 + (claimBytes claims).length < 136 * 12)
    (hL : L.logN - laneFold + logInvRate ≤ costHeight) (ho : o.2.length ≤ 8)
    (hm : ∀ mp ∈ o.2, MultiSmall mp) :
    QB (fillOpening L root claims o) openBudget fun _ ↦ True := by
  unfold fillOpening
  split
  · next x0 x1 rest _ =>
    refine (qb_openingSpongeWith L claims hcl).bind_le
      (b := 2 + ((4 + (2 + whirBound)) + o.2.length * multiBudget)) (fun sp _ ↦
        (qb_absorb _ _ _).bind_le (b := 1 + ((4 + (2 + whirBound)) + o.2.length * multiBudget))
          (fun sp _ ↦ (qb_absorb _ _ _).bind_le
            (b := (4 + (2 + whirBound)) + o.2.length * multiBudget) (fun sp _ ↦
              (qb_fillRun_opening L claims sp rest root o.2 hL hm).bind_le
                (fun _ _ ↦ qb_ret _ 0) le_rfl) le_rfl) (by omega)) ?_
    unfold openBudget
    have := Nat.mul_le_mul_right multiBudget ho
    omega
  · exact qb_ret _ _

/-! ## The formatting -/

/-- **The skeleton's proof is small**: every opening has at most `8` pruned multiproofs, each of at
most `2^10` positions and rows of at most `2^10` words. -/
def FmtSmall (pf : QuotientZk.Deployed.Proof) : Prop :=
  ∀ o ∈ pf.openings, o.2.length ≤ 8 ∧
    ∀ mp ∈ o.2, mp.1.length ≤ 2 ^ 10 ∧ ∀ r ∈ mp.2.1, r.length ≤ 2 ^ 10

/-- The formatting's calls of `π`, at most: the circuit's commitment, the chain, three openings. -/
def fmtCalls : ℕ := 2 ^ 19 * 5 + 7 + 3 * openBudget

/-- `4 881 047 ≤ 2^23`. -/
theorem fmtCalls_le : fmtCalls ≤ fmtBudget := by
  unfold fmtCalls openBudget multiBudget fmtBudget costHeight whirBound
  norm_num

theorem logN_witnessLayout : (witnessLayout logRows).logN = 25 := rfl

theorem logN_wiringLayout : (wiringLayout logRows).logN = 24 := rfl

theorem logN_quotientLayout : (quotientLayout logRows).logN = 28 := rfl

/-- **`fmtCore` of a small proof makes at most `fmtCalls` calls of `π`**, on every path. -/
theorem qb_fmtCore (stmt : Statement) (pf : QuotientZk.Deployed.Proof) (h : FmtSmall pf) :
    QB (fmtCore stmt pf) fmtCalls fun _ ↦ True := by
  unfold fmtCore
  refine qb_setupWith.bind_le (b := 7 + 3 * openBudget) (fun ir _ ↦
    (qb_reduceWith _ ir stmt _).bind_le (b := 3 * openBudget) (fun r hr ↦ ?_) le_rfl) le_rfl
  cases r with
  | none => exact qb_ret _ _
  | some r =>
    obtain ⟨hw, hσ, hq, hs⟩ := hr
    have hcv : cellVars logRows = 24 := rfl
    rw [hcv] at hw hσ hq hs
    dsimp only
    split
    · next oW oσ oQ heq =>
      have hoW := h oW (by rw [heq]; simp)
      have hoσ := h oσ (by rw [heq]; simp)
      have hoQ := h oQ (by rw [heq]; simp)
      refine (qb_fillOpening _ _ _ oW ?_ ?_ hoW.1 hoW.2).bind_le (b := 2 * openBudget) (fun _ _ ↦
        (qb_fillOpening _ _ _ oσ ?_ ?_ hoσ.1 hoσ.2).bind_le (b := openBudget) (fun _ _ ↦
          (qb_fillOpening _ _ _ oQ ?_ ?_ hoQ.1 hoQ.2).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl)
          (by omega)) (by omega)
      · rw [len_claimBytes_cons, len_claimBytes_nil]; omega
      · rw [logN_witnessLayout]; decide
      · rw [len_claimBytes_cons, len_claimBytes_nil]; omega
      · rw [logN_wiringLayout]; decide
      · rw [len_claimBytes_cons, len_claimBytes_cons, len_claimBytes_nil]; omega
      · rw [logN_quotientLayout]; decide
    · exact qb_ret _ _

/-- **On a small proof the budget is never reached**: `fmt` is `fmtCore`. -/
theorem fmt_eq_core (stmt : Statement) (pf : QuotientZk.Deployed.Proof) (h : FmtSmall pf) :
    fmt stmt pf = fmtCore stmt pf :=
  budgeted_eq_self _ _ ((qb_fmtCore stmt pf h).total.mono fmtCalls_le)

/-- **`fmt` against `π` on a small proof is `fmtCore`'s run against `π`.** -/
theorem fmtDet_eq_core (π : Equiv.Perm Eager.St) (stmt : Statement)
    (pf : QuotientZk.Deployed.Proof) (h : FmtSmall pf) :
    fmtDet π stmt pf = (simulateQ (permOnly π) (fmtCore stmt pf)).run := by
  rw [fmtDet, fmt_eq_core stmt pf h]

end PcsQuotient.EndToEnd.Core

/--
info: 'PcsQuotient.EndToEnd.Core.fmtDet_eq_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.fmtDet_eq_core
