-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Completeness.Final

/-!
# The hidden openings, proven

With F2's transcription of the redesigned hidden layout (`WhirBridge`: `Layout.hidden`,
`Layout.readHidden` = `Table::read`, the gadget as the stacking's extra stack claim of value zero,
`Layout.holds_iff`, `Layout.extra_holds_iff`), the witness and quotient openings are complete:

* the layouts are `HiddenFill.lean`'s (`witnessLayout_eq`, `quotientLayout_eq`: F2's
  `witnessLayout 22`, `quotientLayout 22` are `witnessLayoutNew 22`, `quotientLayoutNew 22`, decided)
  and F2's `Table::read` is `HiddenFill.lean`'s (`readHidden_eq`);
* a table vanishing off its chunks is read back whole from the honest stack (`witness_read`,
  `quotient_read`), so its true table claims are true stack claims (`Layout.holds_iff`);
* the honest stack cancels the gadget (`gadget_cancel`), so the gadget's stack claim holds
  (`Layout.extra_holds_iff`);
* mumbai's completeness of the opening (`openingVerify_honest`).

`witnessOpening`, `quotientOpening` are the `HiddenOpening`s; **`completeness_end`** is
`completeness_hidden` with them, and **`completeness_end_bad_set`** the version outside the
degenerate challenges: no hypothesis on the openings remains.
-/

set_option linter.unusedSectionVars false

open Finset
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Semantics
open scoped ENNReal

namespace Completeness

open QuotientSecurity

theorem witnessLayout_eq :
    WhirBridge.witnessLayout WhirBridge.logRows = witnessLayoutNew WhirBridge.logRows := by
  decide +kernel

theorem quotientLayout_eq :
    WhirBridge.quotientLayout WhirBridge.logRows = quotientLayoutNew WhirBridge.logRows := by
  decide +kernel

/-- F2's `Table::read` is `HiddenFill.lean`'s. -/
theorem readHidden_eq (L : WhirBridge.Layout) (s : ℕ) (q : Column L.logN) (t : ℕ) :
    L.readHidden s q t = L.readNew s q t := rfl

/-- F2's gadget value of the honest stack is zero. -/
theorem gadgetValue_fillNew {L : WhirBridge.Layout} {s : ℕ} (hL : NewHiddenOK L s) (T : ℕ → K)
    (pad : ℕ → ℕ → K) : L.gadgetValue s (L.fillNew s T pad) = 0 := by
  unfold WhirBridge.Layout.gadgetValue
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hg3 := List.mem_range.mp hg
  have hi3 := List.mem_range.mp hi
  have hc := gadget_cancel hL T pad hg3 hi3
  have hlanes : WhirBridge.gadgetLanes g = gadgetLanesN g := by
    interval_cases g <;> rfl
  have hentry : WhirBridge.gadgetEntry s g i = gadgetEntryN s g i := rfl
  rw [hlanes, hentry]
  change WhirBridge.gadgetBeta i * ((gadgetLanesN g).map fun l ↦
    ofK (laneWord (L.fillNew s T pad) L.logLane l (gadgetEntryN s g i))).sum = 0
  rw [hc, mul_zero]

/-- **A hidden layout's honest opening is complete**: for a layout of the shape (`NewHiddenOK`,
F2's `Valid`, admissible), a table whose read-back from any honest stack is itself, true claims,
whatever the padding. -/
theorem hidden_complete (L : WhirBridge.Layout) (s : ℕ) (hL : NewHiddenOK L s) (hval : L.Valid)
    (hw : Whir.Admissible L.logN WhirBridge.logInvRate) (Held : ℕ → Prop)
    (hread : ∀ T : ℕ → K, (∀ t, ¬ Held t → T t = 0) →
      ∀ pad t, L.readNew s (L.fillNew s T pad) t = T t)
    (H : Bytes → Digest) (F : KeccakState → KeccakState) (T : ℕ → K) (pad : ℕ → ℕ → K)
    (cs : List WhirBridge.Claim) (fuel : ℕ) (π : Proof) (hne : cs.isEmpty = false)
    (hT : ∀ t, ¬ Held t → T t = 0)
    (hcs : ∀ c ∈ cs, c.point.length = L.vars ∧ tableEvalN L.vars T c.point = c.value)
    (hπ : honestOpen H F L.stacking WhirBridge.logInvRate
      (WhirBridge.openingPrefix L WhirBridge.logInvRate) (L.fillNew s T pad) cs fuel = some π) :
    WhirBridge.openingVerifyWithHash (m := Id) H F L WhirBridge.logInvRate
      (honestRoot H L.stacking WhirBridge.logInvRate (L.fillNew s T pad)) cs π = true := by
  refine openingVerify_honest H F L hw (L.fillNew s T pad) cs hne (fun c hc => (hcs c hc).1)
    (fun c hc => ?_) ?_ fuel hπ
  · rw [L.holds_iff hval c (hcs c hc).1]
    refine Eq.trans ?_ (hcs c hc).2
    unfold WhirBridge.Layout.tableEval tableEvalN WhirBridge.Layout.table
    rw [hL.piece]
    exact Finset.sum_congr rfl fun t _ => by
      show ofK (L.readHidden s (L.fillNew s T pad) t) * _ = _
      rw [readHidden_eq, hread T hT pad t]
  · rw [L.extra_holds_iff hval]
    unfold WhirBridge.Layout.GadgetHolds
    rw [hL.piece]
    exact gadgetValue_fillNew hL T pad

theorem witness_shape :
    NewHiddenOK (witnessLayoutNew WhirBridge.logRows) 8 ∧
      (witnessLayoutNew WhirBridge.logRows).Valid ∧
      Whir.Admissible (witnessLayoutNew WhirBridge.logRows).logN WhirBridge.logInvRate := by
  have hok := WhirBridge.layouts_ok WhirBridge.logRows (by decide) (by decide)
  have hval := WhirBridge.layouts_valid WhirBridge.logRows (by decide) (by decide)
  rw [← witnessLayout_eq]
  refine ⟨?_, hval.1, hok.1⟩
  rw [witnessLayout_eq]
  exact deployed_newHiddenOK.1

theorem quotient_shape :
    NewHiddenOK (quotientLayoutNew WhirBridge.logRows) 8 ∧
      (quotientLayoutNew WhirBridge.logRows).Valid ∧
      Whir.Admissible (quotientLayoutNew WhirBridge.logRows).logN WhirBridge.logInvRate := by
  have hok := WhirBridge.layouts_ok WhirBridge.logRows (by decide) (by decide)
  have hval := WhirBridge.layouts_valid WhirBridge.logRows (by decide) (by decide)
  rw [← quotientLayout_eq]
  refine ⟨?_, hval.2.2, hok.2.2⟩
  rw [quotientLayout_eq]
  exact deployed_newHiddenOK.2

/-- **The witness table's opening**, proven (`witness_layout(22)`, hidden). -/
noncomputable def witnessOpening :
    HiddenOpening (witnessLayoutNew WhirBridge.logRows) 8 witnessHeld where
  root H q := honestRoot H (witnessLayoutNew WhirBridge.logRows).stacking WhirBridge.logInvRate q
  prove H F q cs fuel := honestOpen H F (witnessLayoutNew WhirBridge.logRows).stacking
    WhirBridge.logInvRate
    (WhirBridge.openingPrefix (witnessLayoutNew WhirBridge.logRows) WhirBridge.logInvRate) q cs fuel
  verify H F r cs π := WhirBridge.openingVerifyWithHash (m := Id) H F
    (witnessLayoutNew WhirBridge.logRows) WhirBridge.logInvRate r cs π
  complete H F T pad cs fuel π hne hT hcs hπ :=
    hidden_complete _ 8 witness_shape.1 witness_shape.2.1 witness_shape.2.2 witnessHeld
      (fun T hT pad t => witness_read T hT pad t) H F T pad cs fuel π hne hT hcs hπ

/-- **The quotient table's opening**, proven (`quotient_layout(22)`, hidden, two claims). -/
noncomputable def quotientOpening :
    HiddenOpening (quotientLayoutNew WhirBridge.logRows) 8 quotientHeld where
  root H q := honestRoot H (quotientLayoutNew WhirBridge.logRows).stacking WhirBridge.logInvRate q
  prove H F q cs fuel := honestOpen H F (quotientLayoutNew WhirBridge.logRows).stacking
    WhirBridge.logInvRate
    (WhirBridge.openingPrefix (quotientLayoutNew WhirBridge.logRows) WhirBridge.logInvRate) q cs fuel
  verify H F r cs π := WhirBridge.openingVerifyWithHash (m := Id) H F
    (quotientLayoutNew WhirBridge.logRows) WhirBridge.logInvRate r cs π
  complete H F T pad cs fuel π hne hT hcs hπ :=
    hidden_complete _ 8 quotient_shape.1 quotient_shape.2.1 quotient_shape.2.2 quotientHeld
      (fun T hT pad t => quotient_read T hT pad t) H F T pad cs fuel π hne hT hcs hπ

/-- **End-to-end completeness, every opening proven.** For every hash function `H` and
permutation `F` (the deployed Keccak-256 and Keccak-f[1600] included), transcript, secret and
prover randomness: if the honest prover returns a proof and its challenges `(α, β, t)` are not
degenerate, the deployed verifier, with its three openings `opening::verify` on the deployed
layouts, accepts it for the statement the secret proves. Hypotheses: F0b's circuit `M` (Keccak
correctness forward), laid as the wiring, the deployed weights and a basis in `K`. -/
theorem completeness_end (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) (M : MembershipCircuit) {x Y : E}
    (hc : I.c = coordWeight x Y) (hw : I.wiring = wiringOf M.C) (tr : Transcript)
    (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) (s : Secret)
    (m : Fin 4 → Fin 3 → K) (padW padQ : ℕ → ℕ → K) (π : DeployedProof)
    (hπ : honestProve I x Y BK M tr witnessOpening.toSystem quotientOpening.toSystem H F fuel s m
      padW padQ = some π)
    (hab : ¬ Reduction.BadAB I
      (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).g
      (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).α
      (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).β)
    (ht : ¬ Reduction.Degenerate I
      (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).g
      (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).α
      (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).β
      (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).t) :
    deployedVerify I x Y tr wiringOpening witnessOpening.toSystem quotientOpening.toSystem H F
      (wiringOpening.root H (wiringStack I BK)) s.statement π :=
  completeness_hidden I BK hB M hc hw tr witnessOpening quotientOpening H F fuel s m padW padQ π
    hπ hab ht

open Classical in
/-- **End-to-end completeness outside one set of challenges, every opening proven**: for each
witness one set `Bad` of triples `(α, β, t)`, at most a `(17 · 2^24 + 8) / 2^192 < 2^-163`
fraction, such that for every hash function, permutation, transcript and padding the honest proof,
when the openings' proofs of work succeed, is accepted unless the run's `(α, β, t)` is in `Bad`. -/
theorem completeness_end_bad_set (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) (M : MembershipCircuit) {x Y : E}
    (hc : I.c = coordWeight x Y) (hw : I.wiring = wiringOf M.C) (s : Secret)
    (m : Fin 4 → Fin 3 → K) :
    ∃ Bad : Finset (E × E × E),
      (Bad.card : ℝ≥0∞) / (Fintype.card (E × E × E) : ℝ≥0∞) ≤ (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 ∧
      ∀ (tr : Transcript) (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
        (padW padQ : ℕ → ℕ → K) (π : DeployedProof),
        honestProve I x Y BK M tr witnessOpening.toSystem quotientOpening.toSystem H F fuel s m
          padW padQ = some π →
        ((honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).α,
          (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).β,
          (honestRun I BK M tr witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).t)
          ∉ Bad →
        deployedVerify I x Y tr wiringOpening witnessOpening.toSystem quotientOpening.toSystem H F
          (wiringOpening.root H (wiringStack I BK)) s.statement π := by
  obtain ⟨Bad, hcard, hall⟩ := completeness_bad_set I BK hB M hc hw s m
  exact ⟨Bad, hcard, fun tr H F fuel padW padQ π hπ hnot =>
    hall tr witnessOpening quotientOpening H F fuel padW padQ π hπ hnot⟩

end Completeness
