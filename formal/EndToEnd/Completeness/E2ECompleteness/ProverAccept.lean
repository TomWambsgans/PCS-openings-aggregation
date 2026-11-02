-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the runners with a hash, Merkle trees, `StackClaim.Holds`, `IsMultilinearFn`.
import E2ECompleteness.ProverRun
import E2ECompleteness.ProverValues
import E2ECompleteness.ProverClaims
import E2ECompleteness.ProverStatement
import E2ECompleteness.ProverStack
import E2ECompleteness.Staging
import Bridge.Verifier

/-!
# The prover bridge: the Statement's honest proof is accepted

**`verifyWithH_proverWithH`**: at every hash function `H` and permutation `F` (pure, the `Id` monad),
for a witness `w` of `stmt`, masks and paddings: if the Statement's honest prover with Keccak-256
explicit (`proverWithH`, `WithHash.lean`) returns a proof `π`, and the run's challenges `(α, β, t)`
(`chainChallenges`, the staged run's) avoid `badSet w masks`, then the Statement's verifier with
Keccak-256 explicit (`verifyWithH`), on the setup's root, accepts `π`.

The proof: the prover is its run (`ProverRun.lean`); the verifier re-runs the reduction on the
prover's own reduction proof, so it reads the prover's own claims (`reduceWithH_id`); on the honest
values (`ProverValues.lean`) these are Completeness's claims (`claimsAt_honest`), true of the tables
(`Completeness.honest_claims`, at a transcript giving the run's challenges) when the challenges avoid
`badSet`; the prover's tables are Completeness's (`TablesMatch`); its stacks make the stack claims true
(`ProverStack.lean`); each honest opening of true stack claims is accepted (`OpeningAccepts`).

What it takes, until the bridges land:

* `Constants`: the Statement's computed constants' properties (`ProverDefs.lean`);
* `Bridge.ClaimsMatch stmtConsts`: the Statement's claims are Compose's `reduce`'s (Bridge-Defs);
* `CircuitMatch`: the membership circuit's cells and wiring are F0b's (Bridge-Defs' `Bridge/Circuit`);
* `TablesMatch`: the prover's NTT tables are Completeness's (the tables helper, `ProverTables*.lean`);
* `OpeningAccepts`: the honest WHIR opening is accepted (the opening helper, `ProverOpening.lean`).
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover LeanVM.Protocol.EndToEnd
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness

/-! ## What the bridges give -/

/-- **The membership circuit's cells and wiring are F0b's** (Bridge-Defs' `Bridge/Circuit`): the
Statement's cells of a witness are `formal/Completeness`'s honest cells (`cellBitsK` of F0b's
deployed circuit on the secret), and its wiring's points are the deployed σ's. -/
structure CircuitMatch : Prop where
  cells : ∀ (w : PcsQuotient.Secret) (b : Fin (22 + 2) → Bool),
    (cellsOf w).getD (Completeness.idx b) 0 =
      Completeness.cellBitsK Completeness.deployedMembership (secretOf w) b
  sigma : ∀ b : Fin (22 + 2) → Bool,
    point ((membership logRows).sigma.getD (Completeness.idx b) 0) =
      deployedBasis.point (deployedSigma b)
  sigmaSize : (membership logRows).sigma.size = 2 ^ 24

/-- The instance. -/
local notation "I" => Completeness.deployedInstanceE

/-- **The prover's NTT tables are Completeness's** (the tables helper's three statements): the
witness table, the wiring table and, at challenges where the honest sum exists, the quotient table
on what its stack reads. -/
structure TablesMatch : Prop where
  witness : ∀ (f : (Fin (22 + 2) → Bool) → K) (cells : Array K), cells.size = 2 ^ 24 →
    (∀ b, cells.getD (Completeness.idx b) 0 = f b) → ∀ (masks : Masks) (i : ℕ),
      witnessEntry (2 ^ 24) (coefficients 24 0 cells) (maskEntries masks) i =
        Completeness.natTable (Completeness.witnessTable deployedBasis f masks) i
  wiring : ∀ sigma : Array ℕ, sigma.size = 2 ^ 24 →
    (∀ b, point (sigma.getD (Completeness.idx b) 0) = deployedBasis.point (deployedSigma b)) →
      ∀ i, (coefficients 24 0 (sigma.map point)).getD i 0 =
        Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma) i
  quotient : ∀ (f : (Fin (22 + 2) → Bool) → K) (cells : Array K), cells.size = 2 ^ 24 →
    (∀ b, cells.getD (Completeness.idx b) 0 = f b) → ∀ sigma : Array ℕ, sigma.size = 2 ^ 24 →
    (∀ b, point (sigma.getD (Completeness.idx b) 0) = deployedBasis.point (deployedSigma b)) →
    ∀ (masks : Masks) (α β γ : E),
      ¬ Completeness.Reduction.BadAB I
        (witnessOfTable fun b ↦ algebraMap K E (Completeness.witnessTable deployedBasis f masks b))
        α β →
      ∀ i, (Completeness.quotientHeld i ∨ PastChunks 24 8 (quotientChunks 24) i) →
        quotientEntry 22 (coefficients 24 0 (hValues 22 cells sigma α β γ))
          (coefficients 26 (betaAt 26)
            (qValuesOf 22 (wValuesOf 22 (coefficients 24 0 cells) (maskEntries masks))
              (sigmaValuesOf 22 (coefficients 24 0 (sigma.map point)))
              (q0Of 22 (coefficients 24 0 (hValues 22 cells sigma α β γ))) (blocksOf 22 γ) α β))
          (coefficients 26 (betaAt 26)
            (qGateValuesOf 22 (wValuesOf 22 (coefficients 24 0 cells) (maskEntries masks))
              (blocksOf 22 γ))) i =
        Completeness.natTable (Completeness.quotientTable Completeness.limbE (22 + 2 + 1 + 1)
          (Params.honest (I).params
            (witnessOfTable fun b ↦ algebraMap K E (Completeness.witnessTable deployedBasis f masks b))
            α β γ)
          (Completeness.qGateKOf (Params.honest (I).params
            (witnessOfTable fun b ↦ algebraMap K E (Completeness.witnessTable deployedBasis f masks b))
            α β γ))) i

/-- **The honest WHIR opening of true stack claims is accepted** (the opening helper's statement), at
the three layouts. -/
def OpeningAccepts : Prop :=
  ∀ (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) (L : PcsQuotient.Layout),
    (L = witnessLayout 22 ∨ L = wiringLayout 22 ∨ L = quotientLayout 22) →
    ∀ (stack : Array K) (claims : List PcsQuotient.Claim), claims ≠ [] →
    (∀ c ∈ claims, c.point.length = L.vars) →
    (∀ sc ∈ stackClaims L claims, StackClaim.Holds L.logN sc (colOf L.logN stack)) →
    (∀ sc ∈ stackClaims L claims, IsMultilinearFn L.logN sc.1) →
    ∀ π : Compile.Proof,
      proveOpeningWithH (m := Id) H F fuel L (commitWithH (m := Id) H L.logN stack) stack claims =
        some π →
      openingWithH (m := Id) H F L (commitWithH (m := Id) H L.logN stack).root claims π = true

/-! ## The claims of an honest run are true -/

/-- A transcript giving fixed challenges. -/
def constTranscript (α β γ t ρ : E) : Completeness.Transcript :=
  ⟨fun _ _ ↦ (α, β, γ), fun _ _ _ ↦ t, fun _ _ _ _ _ ↦ ρ⟩

/-- **Completeness's four claims at given challenges are true of its honest tables** (its
`honest_claims` at a transcript giving them), when the honest sum exists and `t` is not degenerate. -/
theorem honest_claims_at (H : Bytes → Digest) (w : PcsQuotient.Secret) (masks : Masks)
    (α β γ t ρ : E) (hab : ¬ Completeness.Reduction.BadAB I (honestMsg w masks) α β)
    (ht : ¬ Completeness.Reduction.Degenerate I (honestMsg w masks) α β t) :
    let cW := Completeness.witnessTable deployedBasis
      (Completeness.cellBitsK Completeness.deployedMembership (secretOf w)) masks
    let R := Params.honest (I).params (honestMsg w masks) α β γ
    let cQ := Completeness.quotientTable Completeness.limbE (22 + 2 + 1 + 1) R
      (Completeness.qGateKOf R)
    let stmtW := statementWords Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y
      (secretOf w).statement.root
    let a := Params.opened (honestMsg w masks) t
    let sv := (I).params.sigmaPoly.eval t
    Completeness.tableEvalN 25 (Completeness.natTable cW) (Completeness.witnessClaim t ρ a).point =
        (Completeness.witnessClaim t ρ a).value ∧
      Completeness.tableEvalN 24 (Completeness.natTable
          (Completeness.wiringTableK deployedBasis deployedSigma)) (Completeness.wiringClaim t sv).point =
        (Completeness.wiringClaim t sv).value ∧
      Completeness.tableEvalN 30 (Completeness.natTable cQ)
          (Completeness.quotientClaim I α β γ t ρ a sv).point =
        (Completeness.quotientClaim I α β γ t ρ a sv).value ∧
      Completeness.tableEvalN 30 (Completeness.natTable cQ) (Completeness.sumClaim I stmtW γ).point =
        (Completeness.sumClaim I stmtW γ).value :=
  Completeness.honest_claims I deployedBasis (fun _ ↦ rfl) Completeness.deployedMembership rfl
    Completeness.deployedSigma_keeps (constTranscript α β γ t ρ) Completeness.witnessOpening.toSystem
    Completeness.quotientOpening.toSystem H (secretOf w) masks (fun _ _ ↦ 0) (fun _ _ ↦ 0) hab ht

/-! ## Small facts -/

theorem cells_size (c : Circuit) (inputs : List Bool) : (c.cells inputs).size = 4 * c.rows.size := by
  simp [Circuit.cells]

/-- **The Statement's cells of a witness are `2^24`** (the membership circuit has `2^22` rows). -/
theorem cellsOf_size (w : PcsQuotient.Secret) : (cellsOf w).size = 2 ^ 24 := by
  rw [cellsOf, cells_size]
  have h : (membership logRows).rows.size = 2 ^ logRows := by
    show (finish logRows _ _).rows.size = _
    simp [finish]
  rw [h]
  rfl

/-- The entries past a chunk's end in its last piece are in no chunk, for chunks of distinct
indices whose last pieces end within `2^24`. -/
theorem not_inChunks_of_pastChunks {chunks : List (ℕ × ℕ)}
    (hlen : ∀ c ∈ chunks, (c.2 + 2 ^ 8 - 1) / 2 ^ 8 * 2 ^ 8 ≤ 2 ^ 24)
    (hnd : (chunks.map Prod.fst).Nodup) {i : ℕ} (h : PastChunks 24 8 chunks i) :
    ¬ Completeness.InChunks 24 chunks i := by
  rintro ⟨c', hc', j', hj', rfl⟩
  obtain ⟨c, hc, j, hj1, hj2, he⟩ := h
  have h1 := hlen c hc
  have h2 := hlen c' hc'
  have hj'' : j' < 2 ^ 24 := by
    have : c'.2 ≤ (c'.2 + 2 ^ 8 - 1) / 2 ^ 8 * 2 ^ 8 := by
      have := Nat.div_add_mod (c'.2 + 2 ^ 8 - 1) (2 ^ 8)
      have := Nat.mod_lt (c'.2 + 2 ^ 8 - 1) (show 0 < 2 ^ 8 by norm_num)
      omega
    omega
  have hc1 : c'.1 = c.1 := by omega
  have hcc : c' = c := List.inj_on_of_nodup_map hnd hc' hc hc1
  subst hcc
  omega

theorem pastChunks_not_quotientHeld {i : ℕ} (h : PastChunks 24 8 (quotientChunks 24) i) :
    ¬ Completeness.quotientHeld i :=
  not_inChunks_of_pastChunks (by decide +kernel) (by decide +kernel) h

/-! ## The verifier at a function -/

/-- **The verifier at a function accepts** when the reduction returns claims and the three openings
accept. -/
theorem verifyWithH_id (H : Bytes → Digest) (F : KeccakState → KeccakState) (lr : ℕ) (ir : Digest)
    (stmt : Statement) (π : PcsQuotient.Proof) (red : Reduced)
    (hred : reduceWithH (m := Id) H lr ir stmt π.reduction = some red)
    (h1 : openingWithH (m := Id) H F (witnessLayout lr) red.witnessRoot [red.claims.witness]
      π.witness = true)
    (h2 : openingWithH (m := Id) H F (wiringLayout lr) ir [red.claims.wiring] π.wiring = true)
    (h3 : openingWithH (m := Id) H F (quotientLayout lr) red.quotientRoot
      [red.claims.quotient, red.claims.sum] π.quotient = true) :
    verifyWithH (m := Id) H F lr ir stmt π = true := by
  simp only [verifyWithH, id_bind, id_pure, hred, h1, h2, h3]
  rfl

/-! ## The prover bridge -/

section Main

attribute [local irreducible] commitWithH proveOpeningWithH openingWithH witnessStack quotientStack
  Domain.coefficients Domain.values hValues qValuesOf qGateValuesOf

/-- **The prover bridge**, from the bridges' statements: at every hash function and permutation, the
Statement's honest proof of a witness is accepted when the run's challenges avoid `badSet`. -/
theorem verifyWithH_proverWithH_of (hK : Constants) (hcl : Bridge.ClaimsMatch stmtConsts)
    (hcirc : CircuitMatch) (hT : TablesMatch) (hO : OpeningAccepts)
    (H : Bytes → Digest) (F : KeccakState → KeccakState) (stmt : Statement) (w : PcsQuotient.Secret)
    (hrel : Relation stmt w) (masks : Masks) (witnessPad quotientPad : Padding)
    (π : PcsQuotient.Proof)
    (hπ : proverWithH (m := Id) H F nonceFuel stmt w masks witnessPad quotientPad = some π)
    (hgood : chainChallenges H (setupWithH (m := Id) H) stmt π.reduction ∉ badSet w masks) :
    verifyWithH (m := Id) H F logRows (setupWithH (m := Id) H) stmt π = true := by
  -- The prover is its run, then its end.
  have hπ' : proveWithH (m := Id) H F nonceFuel (membership logRows) stmt (cellsOf w) masks
      witnessPad quotientPad = some π := hπ
  rw [proveWithH_eq_spec, proveSpec_id] at hπ'
  obtain ⟨red, hred, hoW, hoσ, hoQ, hpr⟩ := finishSpec_id_some H F hπ'
  have hroots := runOf_roots H (membership logRows) stmt (cellsOf w) masks witnessPad quotientPad
  have hch := runOf_chain H (membership logRows) stmt (cellsOf w) masks witnessPad quotientPad
  set r := runOf H (membership logRows) stmt (cellsOf w) masks witnessPad quotientPad with hr
  have hlr : (membership logRows).logRows = 22 := rfl
  have hsetup : setupWithH (m := Id) H = r.indexTree.root := rfl
  rw [hlr, reduceWithH_id H _ stmt _ hroots.1 hroots.2, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2]
    at hred
  rw [hlr] at hoW hoσ hoQ
  -- The challenges avoid the bad set.
  rw [hsetup, hpr, chainChallenges_eq, hch.1, hch.2.1, hch.2.2.2] at hgood
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hgood
  obtain ⟨hab, hdeg⟩ := hgood
  set g := honestMsg w masks with hg
  set ρ := (chainH H r.indexTree.root stmt r.proof).2.2.2.2 with hρ
  -- The tables.
  set f := Completeness.cellBitsK Completeness.deployedMembership (secretOf w) with hf
  set cW := Completeness.witnessTable deployedBasis f masks with hcW
  have hW : ∀ i, witnessEntry (2 ^ 24) r.wHat r.mask i = Completeness.natTable cW i :=
    hT.witness f (cellsOf w) (cellsOf_size w) (hcirc.cells w) masks
  have hσ : ∀ i, r.sigmaHat.getD i 0 =
      Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma) i :=
    hT.wiring (membership logRows).sigma hcirc.sigmaSize hcirc.sigma
  set R := Params.honest (I).params g r.α r.β r.γ with hR
  set cQ := Completeness.quotientTable Completeness.limbE (22 + 2 + 1 + 1) R
    (Completeness.qGateKOf R) with hcQ
  have hQ : ∀ i, (Completeness.quotientHeld i ∨ PastChunks 24 8 (quotientChunks 24) i) →
      quotientEntry 22 r.hHat r.qHat r.qGateHat i = Completeness.natTable cQ i :=
    hT.quotient f (cellsOf w) (cellsOf_size w) (hcirc.cells w) (membership logRows).sigma
      hcirc.sigmaSize hcirc.sigma masks r.α r.β r.γ hab
  -- The values.
  have hvals : r.proof.values = Vector.ofFn (Params.opened g r.t) := by
    have h := rowValuesAt_eq cW r.wHat r.mask (by simp [r, runOf, maskEntries]) hW r.t
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_ofFn]
    exact h ⟨j, hj⟩
  have hnext : r.proof.next = (I).params.sigmaPoly.eval r.t := by
    rw [Completeness.sigmaPoly_eq_wiringTableK (algebraMap K E) I deployedBasis (fun _ ↦ rfl)]
    exact nextAt_eq _ r.sigmaHat hσ r.t
  -- The claims are Completeness's.
  obtain ⟨cl, hcls, cWl, cσl, cQl, cSl⟩ := claimsAt_honest hK hcl stmt
    (statementWords Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y
      (secretOf w).statement.root) g r.α r.β r.γ r.t ρ (target_stmt w stmt hrel r.γ) hdeg
  rw [hvals, hnext, hcls, Option.map_some, Option.some.injEq] at hred
  subst hred
  -- They are true.
  obtain ⟨tW, tσ, tQ, tS⟩ := honest_claims_at H w masks r.α r.β r.γ r.t ρ hab hdeg
  have pt : ∀ {c : PcsQuotient.Claim} {c' : WhirBridge.Claim}, claimTrH c = c' →
      c.point = c'.point ∧ c.value = c'.value := fun h ↦ by subst h; exact ⟨rfl, rfl⟩
  refine verifyWithH_id H F 22 _ stmt π _ (by rw [hpr]; exact hred) ?_ ?_ ?_
  · -- The witness opening.
    obtain ⟨p1, p2⟩ := pt cWl
    refine hO H F nonceFuel _ (Or.inl rfl) r.wStack [cl.witness] (List.cons_ne_nil _ _)
      (fun c hc ↦ ?_) ?_ (stackClaims_multilinear _ (Or.inl rfl) _ fun c hc ↦ ?_) π.witness hoW
    · rw [List.mem_singleton.mp hc, p1]; simp [Completeness.witnessClaim]; rfl
    · refine witness_stackClaims_hold (witnessEntry (2 ^ 24) r.wHat r.mask)
        (Completeness.natTable cW)
        (fun i hi ↦ Completeness.witness_inChunks deployedBasis f masks i hi)
        (fun i _ ↦ hW i) (fun i hi ↦ ?_) witnessPad [cl.witness] (fun c hc ↦ ?_)
      · obtain ⟨c, hc, j, hj1, hj2, rfl⟩ := hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · simp at hj1 hj2; omega
        · simp only at hj1 hj2
          simp only [witnessEntry, r, runOf]
          rw [if_neg (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
            simp [maskEntries]; omega)]
          rfl
      · rw [List.mem_singleton.mp hc, p1, p2]
        exact ⟨by simp [Completeness.witnessClaim], tW⟩
    · rw [List.mem_singleton.mp hc, p1]; simp [Completeness.witnessClaim]; rfl
  · -- The wiring opening.
    obtain ⟨p1, p2⟩ := pt cσl
    have hsz : r.sigmaHat.size = 2 ^ 24 := by
      show (coefficients _ 0 _).size = _
      rw [Bridge.Ntt.coefficients_size, Array.size_map, hcirc.sigmaSize]
    refine hO H F nonceFuel _ (Or.inr (Or.inl rfl)) r.sigmaHat [cl.wiring] (List.cons_ne_nil _ _)
      (fun c hc ↦ ?_) ?_ (stackClaims_multilinear _ (Or.inr (Or.inl rfl)) _ fun c hc ↦ ?_)
      π.wiring hoσ
    · rw [List.mem_singleton.mp hc, p1]; simp [Completeness.wiringClaim]; rfl
    · refine wiring_stackClaims_hold r.sigmaHat hsz [cl.wiring] fun c hc ↦ ?_
      rw [List.mem_singleton.mp hc, p1, p2]
      refine ⟨by simp [Completeness.wiringClaim], ?_⟩
      rw [show (fun i ↦ r.sigmaHat.getD i 0) =
        Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma) from funext hσ]
      exact tσ
    · rw [List.mem_singleton.mp hc, p1]; simp [Completeness.wiringClaim]; rfl
  · -- The quotient opening.
    obtain ⟨q1, q2⟩ := pt cQl
    obtain ⟨s1, s2⟩ := pt cSl
    have hlen : ∀ c ∈ [cl.quotient, cl.sum], c.point.length = 30 := by
      intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · rw [q1]; simp [Completeness.quotientClaim]
      · rw [s1]; simp [Completeness.sumClaim]
    refine hO H F nonceFuel _ (Or.inr (Or.inr rfl)) r.qStack [cl.quotient, cl.sum]
      (List.cons_ne_nil _ _) hlen ?_ (stackClaims_multilinear _ (Or.inr (Or.inr rfl)) _ hlen)
      π.quotient hoQ
    refine quotient_stackClaims_hold (quotientEntry 22 r.hHat r.qHat r.qGateHat)
      (Completeness.natTable cQ)
      (fun i hi ↦ Completeness.quotient_inChunks R (Completeness.qGateKOf R) i hi)
      (fun i hi ↦ hQ i (Or.inl hi))
      (fun i hi ↦ (hQ i (Or.inr hi)).trans
        (Completeness.quotient_inChunks R (Completeness.qGateKOf R) i
          (pastChunks_not_quotientHeld hi)))
      quotientPad [cl.quotient, cl.sum] fun c hc ↦ ⟨hlen c hc, ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · rw [q1, q2]; exact tQ
    · rw [s1, s2]; exact tS

end Main

end E2ECompleteness

/-- info: 'E2ECompleteness.honest_claims_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.honest_claims_at
