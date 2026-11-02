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
    ∀ (masks : Masks),
    (∀ y : Fin 22 → Bool, gate (ofK (f (cellBits (y, 0)))) (ofK (f (cellBits (y, 1))))
      (ofK (f (cellBits (y, 2)))) (ofK (f (cellBits (y, 3)))) = 0) → ∀ (α β γ : E),
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

/-- **The honest cells satisfy the gates** (the relation's first conjunct, `honest_relation`). -/
theorem gate_honest (w : PcsQuotient.Secret) (y : Fin 22 → Bool) :
    gate (ofK (Completeness.cellBitsK Completeness.deployedMembership (secretOf w) (cellBits (y, 0))))
      (ofK (Completeness.cellBitsK Completeness.deployedMembership (secretOf w) (cellBits (y, 1))))
      (ofK (Completeness.cellBitsK Completeness.deployedMembership (secretOf w) (cellBits (y, 2))))
      (ofK (Completeness.cellBitsK Completeness.deployedMembership (secretOf w) (cellBits (y, 3)))) =
      0 := by
  have h := (Completeness.honest_relation Completeness.deployedMembership I
    (x := Primitives.F192.G) (Y := Primitives.F192.Y) rfl Completeness.deployedSigma_keeps
    (secretOf w)).1 y
  have e : ∀ z, ofK (Completeness.cellBitsK Completeness.deployedMembership (secretOf w) z) =
      Completeness.deployedMembership.C.cellsOfBits (Completeness.deployedMembership.assign (secretOf w))
        z := fun z ↦ Completeness.algebraMap_bitF _
  rw [e, e, e, e]
  exact h

/-! ## The honest tail, at a function -/

section Tail

variable (H : Bytes → Digest)

/-- The wiring table of the wiring `sigma`. -/
def sigmaHatOf (sigma : Array ℕ) : Array K := coefficients 24 0 (sigma.map point)

/-- The cells' coefficients. -/
def wHatOf (cells : Array K) : Array K := coefficients 24 0 cells

/-- The witness stack. -/
def wStackOf (cells : Array K) (masks : Masks) (wp : Padding) : Array K :=
  (witnessLayout 22).stackOf (witnessEntry (2 ^ 24) (wHatOf cells) (maskEntries masks)) wp

/-- The sum's polynomial's coefficients. -/
def hHatOf (cells : Array K) (sigma : Array ℕ) (α β γ : E) : Array E :=
  coefficients 24 0 (hValues 22 cells sigma α β γ)

/-- The copy quotient's coefficients. -/
def qHatOf (cells : Array K) (sigma : Array ℕ) (masks : Masks) (α β γ : E) : Array E :=
  coefficients 26 (betaAt 26) (qValuesOf 22 (wValuesOf 22 (wHatOf cells) (maskEntries masks))
    (sigmaValuesOf 22 (sigmaHatOf sigma)) (q0Of 22 (hHatOf cells sigma α β γ)) (blocksOf 22 γ) α β)

/-- The gate quotient's coefficients. -/
def qGateHatOf (cells : Array K) (masks : Masks) (γ : E) : Array K :=
  coefficients 26 (betaAt 26) (qGateValuesOf 22 (wValuesOf 22 (wHatOf cells) (maskEntries masks))
    (blocksOf 22 γ))

/-- The quotient stack. -/
def qStackOf (cells : Array K) (sigma : Array ℕ) (masks : Masks) (qp : Padding) (α β γ : E) :
    Array K :=
  (quotientLayout 22).stackOf (quotientEntry 22 (hHatOf cells sigma α β γ)
    (qHatOf cells sigma masks α β γ) (qGateHatOf cells masks γ)) qp

/-- **The honest reduction proof** at `H`: the two roots, the values at `t`. -/
def proofOf (cells : Array K) (sigma : Array ℕ) (masks : Masks) (wp qp : Padding) (α β γ t : E) :
    ReductionProof :=
  ⟨digestScalars (commitWithH (m := Id) H 25 (wStackOf cells masks wp)).root,
    digestScalars (commitWithH (m := Id) H 28 (qStackOf cells sigma masks qp α β γ)).root,
    rowValuesAt 22 (wHatOf cells) (maskEntries masks) t, nextAt 22 (sigmaHatOf sigma) t⟩

end Tail

/-! ## The prover bridge -/

section Main

attribute [local irreducible] commitWithH proveOpeningWithH openingWithH witnessStack quotientStack
  Domain.coefficients Domain.values hValues qValuesOf qGateValuesOf nextAt rowValuesAt novelEval
  Layout.stackOf deployedSigma

variable (hK : Constants) (hcl : Bridge.ClaimsMatch stmtConsts) (hT : TablesMatch)
  (H : Bytes → Digest) (stmt : Statement) (w : PcsQuotient.Secret) (hrel : Relation stmt w)
  (masks : Masks) (wp qp : Padding) (cells : Array K) (sigma : Array ℕ)
  (hcs : cells.size = 2 ^ 24)
  (hcells : ∀ b, cells.getD (Completeness.idx b) 0 =
    Completeness.cellBitsK Completeness.deployedMembership (secretOf w) b)
  (hss : sigma.size = 2 ^ 24)
  (hsig : ∀ b, point (sigma.getD (Completeness.idx b) 0) = deployedBasis.point (deployedSigma b))
  (α β γ t : E)
  (hα : (chainH H (commitWithH (m := Id) H 24 (sigmaHatOf sigma)).root stmt
    (proofOf H cells sigma masks wp qp α β γ t)).1 = α)
  (hβ : (chainH H (commitWithH (m := Id) H 24 (sigmaHatOf sigma)).root stmt
    (proofOf H cells sigma masks wp qp α β γ t)).2.1 = β)
  (hγ : (chainH H (commitWithH (m := Id) H 24 (sigmaHatOf sigma)).root stmt
    (proofOf H cells sigma masks wp qp α β γ t)).2.2.1 = γ)
  (ht : (chainH H (commitWithH (m := Id) H 24 (sigmaHatOf sigma)).root stmt
    (proofOf H cells sigma masks wp qp α β γ t)).2.2.2.1 = t)
  (hgood : (α, β, t) ∉ badSet w masks)

include hK hcl hT hrel hcs hcells hss hsig hα hβ hγ ht hgood in
/-- **The reduction on the honest proof returns Completeness's claims**, true of the honest tables,
when the chain's challenges avoid `badSet`. -/
theorem reduce_honest :
    ∃ cl : Claims,
      reduceWithH (m := Id) H 22 (commitWithH (m := Id) H 24 (sigmaHatOf sigma)).root stmt
          (proofOf H cells sigma masks wp qp α β γ t) =
        some ⟨(commitWithH (m := Id) H 25 (wStackOf cells masks wp)).root,
          (commitWithH (m := Id) H 28 (qStackOf cells sigma masks qp α β γ)).root, cl⟩ ∧
      (cl.witness.point.length = 25 ∧
        Completeness.tableEvalN 25 (fun i ↦ witnessEntry (2 ^ 24) (wHatOf cells) (maskEntries masks) i)
          cl.witness.point = cl.witness.value) ∧
      (cl.wiring.point.length = 24 ∧
        Completeness.tableEvalN 24 (fun i ↦ (sigmaHatOf sigma).getD i 0) cl.wiring.point =
          cl.wiring.value) ∧
      (∀ c ∈ [cl.quotient, cl.sum], c.point.length = 30 ∧
        Completeness.tableEvalN 30 (Completeness.natTable (Completeness.quotientTable
          Completeness.limbE (22 + 2 + 1 + 1) (Params.honest (I).params (honestMsg w masks) α β γ)
          (Completeness.qGateKOf (Params.honest (I).params (honestMsg w masks) α β γ))))
          c.point = c.value) := by
  have h₁ : digestOfScalars (proofOf H cells sigma masks wp qp α β γ t).witnessRoot =
      some (commitWithH (m := Id) H 25 (wStackOf cells masks wp)).root :=
    digestOfScalars_digestScalars _
  have h₂ : digestOfScalars (proofOf H cells sigma masks wp qp α β γ t).quotientRoot =
      some (commitWithH (m := Id) H 28 (qStackOf cells sigma masks qp α β γ)).root :=
    digestOfScalars_digestScalars _
  rw [reduceWithH_id H _ stmt _ h₁ h₂, hα, hβ, hγ, ht]
  -- The challenges avoid the bad set.
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hgood
  obtain ⟨hab, hdeg⟩ := hgood
  set ρ := (chainH H (commitWithH (m := Id) H 24 (sigmaHatOf sigma)).root stmt
    (proofOf H cells sigma masks wp qp α β γ t)).2.2.2.2
  -- The tables.
  set f := Completeness.cellBitsK Completeness.deployedMembership (secretOf w) with hf
  set cW := Completeness.witnessTable deployedBasis f masks with hcW
  have hW : ∀ i, witnessEntry (2 ^ 24) (wHatOf cells) (maskEntries masks) i =
      Completeness.natTable cW i := hT.witness f cells hcs hcells masks
  have hσ : ∀ i, (sigmaHatOf sigma).getD i 0 =
      Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma) i :=
    hT.wiring sigma hss hsig
  -- The values.
  have hvals : (proofOf H cells sigma masks wp qp α β γ t).values =
      Vector.ofFn (Params.opened (honestMsg w masks) t) := by
    have h := rowValuesAt_eq cW (wHatOf cells) (maskEntries masks) (by simp [maskEntries]) hW t
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_ofFn]
    exact h ⟨j, hj⟩
  have hsp : (I).params.sigmaPoly = tablePoly fun b ↦
      algebraMap K E (Completeness.wiringTableK deployedBasis deployedSigma b) :=
    Completeness.sigmaPoly_eq_wiringTableK (algebraMap K E) I deployedBasis (fun _ ↦ rfl)
  have hnext : (proofOf H cells sigma masks wp qp α β γ t).next = (I).params.sigmaPoly.eval t := by
    rw [hsp]
    exact nextAt_eq _ (sigmaHatOf sigma) hσ t
  -- The claims are Completeness's.
  obtain ⟨cl, hcls, cWl, cσl, cQl, cSl⟩ := claimsAt_honest hK hcl stmt
    (statementWords Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y
      (secretOf w).statement.root) (honestMsg w masks) α β γ t ρ (target_stmt w stmt hrel γ) hdeg
  rw [hvals, hnext, hcls]
  refine ⟨cl, rfl, ?_⟩
  -- They are true.
  obtain ⟨tW, tσ, tQ, tS⟩ := honest_claims_at H w masks α β γ t ρ hab hdeg
  have pt : ∀ {c : PcsQuotient.Claim} {c' : WhirBridge.Claim}, claimTrH c = c' →
      c.point = c'.point ∧ c.value = c'.value := fun h ↦ by subst h; exact ⟨rfl, rfl⟩
  obtain ⟨p1, p2⟩ := pt cWl
  obtain ⟨σ1, σ2⟩ := pt cσl
  obtain ⟨q1, q2⟩ := pt cQl
  obtain ⟨s1, s2⟩ := pt cSl
  refine ⟨⟨by rw [p1]; simp [Completeness.witnessClaim], ?_⟩,
    ⟨by rw [σ1]; simp [Completeness.wiringClaim], ?_⟩, fun c hc ↦ ?_⟩
  · rw [show (fun i ↦ witnessEntry (2 ^ 24) (wHatOf cells) (maskEntries masks) i) =
      Completeness.natTable cW from funext hW, p1, p2]
    exact tW
  · rw [show (fun i ↦ (sigmaHatOf sigma).getD i 0) =
      Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma) from funext hσ,
      σ1, σ2]
    exact tσ
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨by rw [q1]; simp [Completeness.quotientClaim], by rw [q1, q2]; exact tQ⟩
    · exact ⟨by rw [s1]; simp [Completeness.sumClaim], by rw [s1, s2]; exact tS⟩

include hK hcl hT hrel hcs hcells hss hsig hα hβ hγ ht hgood in
/-- **The honest proof is accepted** (the core of the prover bridge): when the chain's challenges
avoid `badSet` and each honest opening of the reduction's claims returned a proof, the verifier
accepts the honest proof. -/
theorem accept_core (hO : OpeningAccepts) (F : KeccakState → KeccakState) (fuel : ℕ)
    (πW πσ πQ : Compile.Proof)
    (hoW : ∀ red : Reduced, reduceWithH (m := Id) H 22
        (commitWithH (m := Id) H 24 (sigmaHatOf sigma)).root stmt
        (proofOf H cells sigma masks wp qp α β γ t) = some red →
      proveOpeningWithH (m := Id) H F fuel (witnessLayout 22)
        (commitWithH (m := Id) H 25 (wStackOf cells masks wp)) (wStackOf cells masks wp)
        [red.claims.witness] = some πW ∧
      proveOpeningWithH (m := Id) H F fuel (wiringLayout 22)
        (commitWithH (m := Id) H 24 (sigmaHatOf sigma)) (sigmaHatOf sigma)
        [red.claims.wiring] = some πσ ∧
      proveOpeningWithH (m := Id) H F fuel (quotientLayout 22)
        (commitWithH (m := Id) H 28 (qStackOf cells sigma masks qp α β γ))
        (qStackOf cells sigma masks qp α β γ) [red.claims.quotient, red.claims.sum] = some πQ) :
    verifyWithH (m := Id) H F 22 (commitWithH (m := Id) H 24 (sigmaHatOf sigma)).root stmt
      ⟨proofOf H cells sigma masks wp qp α β γ t, πW, πσ, πQ⟩ = true := by
  obtain ⟨cl, hred, ⟨wl, wt⟩, ⟨σl, σt⟩, hq⟩ := reduce_honest hK hcl hT H stmt w hrel masks wp qp
    cells sigma hcs hcells hss hsig α β γ t hα hβ hγ ht hgood
  obtain ⟨hoW', hoσ', hoQ'⟩ := hoW _ hred
  refine verifyWithH_id H F 22 _ stmt _ _ hred ?_ ?_ ?_
  · -- The witness opening.
    refine hO H F fuel _ (Or.inl rfl) (wStackOf cells masks wp) [cl.witness] (List.cons_ne_nil _ _)
      (fun c hc ↦ by rw [List.mem_singleton.mp hc]; exact wl) ?_
      (stackClaims_multilinear _ (Or.inl rfl) _ fun c hc ↦ by rw [List.mem_singleton.mp hc]; exact wl)
      πW hoW'
    set f := Completeness.cellBitsK Completeness.deployedMembership (secretOf w) with hf
    have hW : ∀ i, witnessEntry (2 ^ 24) (wHatOf cells) (maskEntries masks) i =
        Completeness.natTable (Completeness.witnessTable deployedBasis f masks) i :=
      hT.witness f cells hcs hcells masks
    refine witness_stackClaims_hold (witnessEntry (2 ^ 24) (wHatOf cells) (maskEntries masks))
      (Completeness.natTable (Completeness.witnessTable deployedBasis f masks))
      (fun i hi ↦ Completeness.witness_inChunks deployedBasis f masks i hi)
      (fun i _ ↦ hW i) (fun i hi ↦ ?_) wp [cl.witness] (fun c hc ↦ ?_)
    · obtain ⟨c, hc, j, hj1, hj2, rfl⟩ := hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · simp at hj1 hj2; omega
      · simp only at hj1 hj2
        unfold witnessEntry
        rw [if_neg (by omega), Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
          simp [maskEntries]; omega)]
        rfl
    · rw [List.mem_singleton.mp hc]
      refine ⟨wl, ?_⟩
      rw [← wt, show (fun i ↦ witnessEntry (2 ^ 24) (wHatOf cells) (maskEntries masks) i) =
        Completeness.natTable (Completeness.witnessTable deployedBasis f masks) from funext hW]
  · -- The wiring opening.
    have hsz : (sigmaHatOf sigma).size = 2 ^ 24 := by
      rw [sigmaHatOf, Bridge.Ntt.coefficients_size, Array.size_map, hss]
    refine hO H F fuel _ (Or.inr (Or.inl rfl)) (sigmaHatOf sigma) [cl.wiring]
      (List.cons_ne_nil _ _) (fun c hc ↦ by rw [List.mem_singleton.mp hc]; exact σl)
      (wiring_stackClaims_hold (sigmaHatOf sigma) hsz [cl.wiring]
        fun c hc ↦ by rw [List.mem_singleton.mp hc]; exact ⟨σl, σt⟩)
      (stackClaims_multilinear _ (Or.inr (Or.inl rfl)) _
        fun c hc ↦ by rw [List.mem_singleton.mp hc]; exact σl)
      πσ hoσ'
  · -- The quotient opening.
    set R := Params.honest (I).params (honestMsg w masks) α β γ with hR
    have hab : ¬ Completeness.Reduction.BadAB I (honestMsg w masks) α β := by
      have hg := hgood
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hg
      exact hg.1
    have hQ := hT.quotient _ cells hcs hcells sigma hss hsig masks (gate_honest w) α β γ hab
    refine hO H F fuel _ (Or.inr (Or.inr rfl)) (qStackOf cells sigma masks qp α β γ)
      [cl.quotient, cl.sum] (List.cons_ne_nil _ _) (fun c hc ↦ (hq c hc).1) ?_
      (stackClaims_multilinear _ (Or.inr (Or.inr rfl)) _ fun c hc ↦ (hq c hc).1) πQ hoQ'
    exact quotient_stackClaims_hold _ (Completeness.natTable (Completeness.quotientTable
        Completeness.limbE (22 + 2 + 1 + 1) R (Completeness.qGateKOf R)))
      (fun i hi ↦ Completeness.quotient_inChunks R (Completeness.qGateKOf R) i hi)
      (fun i hi ↦ hQ i (Or.inl hi))
      (fun i hi ↦ (hQ i (Or.inr hi)).trans
        (Completeness.quotient_inChunks R (Completeness.qGateKOf R) i
          (pastChunks_not_quotientHeld hi)))
      qp [cl.quotient, cl.sum] hq

end Main

end E2ECompleteness

/-- info: 'E2ECompleteness.honest_claims_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.honest_claims_at

/-- info: 'E2ECompleteness.reduce_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.reduce_honest

/-- info: 'E2ECompleteness.accept_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.accept_core
