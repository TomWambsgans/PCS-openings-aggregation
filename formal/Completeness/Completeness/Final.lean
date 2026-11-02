-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Completeness.Deployed

/-!
# The end theorems

* **`HiddenOpening`**: what F2's update to the redesigned hidden layout (`cbb527d`, in progress in
  `formal/WhirBridge`) is to give for the witness and quotient tables: `opening::verify` with the
  gadget, the honest root and opening, and completeness for the honest stack `Layout.fillNew`
  (`HiddenFill.lean`) of a table vanishing off its chunks whose claims are true. Discharging it
  takes three proven pieces and one to come: the table read back from the honest stack is the table
  (`witness_read`, `quotient_read`) and the honest stack cancels the gadget
  (`gadgetWeight_sum_zero`), both here; mumbai's completeness of the opening for any stacking whose
  stack claims hold (`honestOpen_accepts`, `Opening.lean`); and **to come from F2's update**, the
  meaning of the redesigned layout's claims (the new `Layout.holds_iff`: a stack claim holds iff the
  table `Table::read` reads back satisfies the table claim) and the gadget as a stack claim of the
  opening's program.
* **`completeness_hidden`**: `completeness_deployed` with those openings.
* **`completeness_bad_set`**: the degenerate challenges depend only on the witness (the secret and
  the masks), not on the hash, the transcript or the padding: **for each witness there is one set
  `Bad` of triples `(α, β, t)`, at most a `(17 · 2^24 + 8) / 2^192 < 2^-163` fraction of all, such
  that for every hash function, permutation, transcript and padding, the honest proof (if the
  openings' proofs of work succeed) is accepted unless the run's `(α, β, t)` falls in `Bad`.**
  With the challenges uniform (the random-oracle model's fresh answers, `transcript.rs`), the
  honest proof is rejected with probability at most `(17 · 2^24 + 8) / 2^192` plus the openings'
  proof-of-work failures (`romComplete_ours`: at most `2^-277` per opening at a fuel of `2^25`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Semantics
open scoped ENNReal

namespace Completeness

open QuotientSecurity

/-- **The opening of a redesigned hidden layout** `L` (pieces of `2^s`, table entries `Held`): what
F2's update is to give. -/
structure HiddenOpening (L : WhirBridge.Layout) (s : ℕ) (Held : ℕ → Prop) where
  root : (Bytes → Digest) → Column L.logN → Digest
  prove : (Bytes → Digest) → (KeccakState → KeccakState) → Column L.logN → List WhirBridge.Claim →
    ℕ → Option Proof
  verify : (Bytes → Digest) → (KeccakState → KeccakState) → Digest → List WhirBridge.Claim →
    Proof → Bool
  /-- **Completeness** for the honest stack `fillNew` (`Table::hidden`) of a table vanishing off
  `Held`, whatever the padding. -/
  complete : ∀ (H : Bytes → Digest) (F : KeccakState → KeccakState) (T : ℕ → K)
    (pad : ℕ → ℕ → K) (cs : List WhirBridge.Claim) (fuel : ℕ) (π : Proof),
    cs.isEmpty = false → (∀ t, ¬ Held t → T t = 0) →
    (∀ c ∈ cs, c.point.length = L.vars ∧ tableEvalN L.vars T c.point = c.value) →
    prove H F (L.fillNew s T pad) cs fuel = some π →
      verify H F (root H (L.fillNew s T pad)) cs π = true

/-- A hidden layout's opening as an `OpeningSystem`. -/
def HiddenOpening.toSystem {L : WhirBridge.Layout} {s : ℕ} {Held : ℕ → Prop}
    (O : HiddenOpening L s Held) : OpeningSystem where
  vars := L.vars
  logN := L.logN
  Held := Held
  stack := L.fillNew s
  root := O.root
  prove := O.prove
  verify := O.verify
  complete := O.complete

/-- The witness table's chunks (`witness_layout`: the cells, then sixteen entries for the masks). -/
def witnessHeld : ℕ → Prop :=
  InChunks (WhirBridge.cellVars WhirBridge.logRows)
    [(0, 2 ^ WhirBridge.cellVars WhirBridge.logRows), (1, 16)]

/-- The quotient table's chunks (`quotient_chunks(24, Q_SPILL, 64)`). -/
def quotientHeld : ℕ → Prop := InChunks (WhirBridge.cellVars WhirBridge.logRows) qChunks

theorem witnessLayoutNew_vars : (witnessLayoutNew WhirBridge.logRows).vars = 25 := rfl
theorem quotientLayoutNew_vars : (quotientLayoutNew WhirBridge.logRows).vars = 30 := rfl

/-- **End-to-end completeness with the redesigned hidden layouts**: `completeness_deployed` with
the witness and quotient openings of `witnessLayoutNew 22` and `quotientLayoutNew 22` (pieces of
`2^8`), whose honest stacks `HiddenFill.lean` builds. -/
theorem completeness_hidden (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) (M : MembershipCircuit) {x Y : E}
    (hc : I.c = coordWeight x Y) (hw : I.wiring = wiringOf M.C) (tr : Transcript)
    (OW : HiddenOpening (witnessLayoutNew WhirBridge.logRows) 8 witnessHeld)
    (OQ : HiddenOpening (quotientLayoutNew WhirBridge.logRows) 8 quotientHeld)
    (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) (s : Secret)
    (m : Fin 4 → Fin 3 → K) (padW padQ : ℕ → ℕ → K) (π : DeployedProof)
    (hπ : honestProve I x Y BK M tr OW.toSystem OQ.toSystem H F fuel s m padW padQ = some π)
    (hab : ¬ Reduction.BadAB I (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).g
      (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).α
      (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).β)
    (ht : ¬ Reduction.Degenerate I (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).g
      (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).α
      (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).β
      (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).t) :
    deployedVerify I x Y tr wiringOpening OW.toSystem OQ.toSystem H F
      (wiringOpening.root H (wiringStack I BK)) s.statement π :=
  completeness_deployed I BK hB M hc hw tr OW.toSystem OQ.toSystem witnessLayoutNew_vars
    quotientLayoutNew_vars (fun _ h => h) (fun _ h => h) H F fuel s m padW padQ π hπ hab ht

/-- The honest first message of a witness: it does not depend on the hash, the transcript or the
padding. -/
noncomputable def honestG (BK : CantorBasis K (22 + 2)) (M : MembershipCircuit) (s : Secret)
    (m : Fin 4 → Fin 3 → K) : Fin 4 → E[X] :=
  witnessOfTable fun b => algebraMap K E (witnessTable BK (cellBitsK M s) m b)

open Classical in
/-- **Completeness outside one small set of challenges.** For each witness (secret and masks)
there is a set `Bad` of triples `(α, β, t)`, at most a `(17 · 2^24 + 8) / 2^192` fraction of them,
such that for every hash function, permutation, transcript and padding, the honest prover's proof,
when it returns one, is accepted by the deployed verifier unless the run's `(α, β, t)` is in
`Bad`. -/
theorem completeness_bad_set (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) (M : MembershipCircuit) {x Y : E}
    (hc : I.c = coordWeight x Y) (hw : I.wiring = wiringOf M.C) (s : Secret)
    (m : Fin 4 → Fin 3 → K) :
    ∃ Bad : Finset (E × E × E),
      (Bad.card : ℝ≥0∞) / (Fintype.card (E × E × E) : ℝ≥0∞) ≤ (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 ∧
      ∀ (tr : Transcript) (OW : HiddenOpening (witnessLayoutNew WhirBridge.logRows) 8 witnessHeld)
        (OQ : HiddenOpening (quotientLayoutNew WhirBridge.logRows) 8 quotientHeld)
        (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
        (padW padQ : ℕ → ℕ → K) (π : DeployedProof),
        honestProve I x Y BK M tr OW.toSystem OQ.toSystem H F fuel s m padW padQ = some π →
        ((honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).α,
          (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).β,
          (honestRun I BK M tr OW.toSystem OQ.toSystem H s m padW padQ).t) ∉ Bad →
        deployedVerify I x Y tr wiringOpening OW.toSystem OQ.toSystem H F
          (wiringOpening.root H (wiringStack I BK)) s.statement π := by
  refine ⟨univ.filter fun z : E × E × E => Reduction.BadAB I (honestG BK M s m) z.1 z.2.1 ∨
    Reduction.Degenerate I (honestG BK M s m) z.1 z.2.1 z.2.2, ?_, ?_⟩
  · refine Reduction.bad_fraction_le I card_E (honestG BK M s m) fun j => ?_
    exact (natDegree_witnessOfTable_le (algebraMap K E) BK (cellBitsK M s) m j).trans
      (by norm_num)
  · intro tr OW OQ H F fuel padW padQ π hπ hnot
    have hnot' := fun h => hnot (mem_filter.mpr ⟨mem_univ _, h⟩)
    exact completeness_hidden I BK hB M hc hw tr OW OQ H F fuel s m padW padQ π hπ
      (fun h => hnot' (Or.inl h)) (fun h => hnot' (Or.inr h))

end Completeness
