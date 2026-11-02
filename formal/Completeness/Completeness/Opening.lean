-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0,
-- MIT OR Apache-2.0): its honest WHIR prover and the completeness of its compilation.
import WhirBridge
import LeanVM.Protocol.Whir.Complete.Opening
import LeanVM.Protocol.Compile.Rom.Complete

/-!
# Completeness of the WHIR opening

`opening::verify` (`WhirBridge.openingVerifyWithHash`) accepts the honest prover's proof. The honest
prover is mumbai's: its interactive prover of the opening (`Whir.Complete.openingProver`: commit the
stack's word, then the honest WHIR opening of the batched stack claims), compiled through the
Fiat-Shamir sponge by mumbai's `prove` (Merkle roots and openings, proof-of-work search with a
`fuel` of nonces).

## Generic in the stacking

Everything up to `opening::verify` is stated for any `WhirBridge.Stacking S` (the table's `vars`,
the stack's `logN`, a multiaffine weight per claim) and any list of claims whose stack claims hold:

* `isMultilinearFn_of_isMultiaffine`: a multiaffine weight is the multilinear extension of its
  values on the cube (`IsMultilinearFn`), the converse of mumbai's
  `isMultiaffine_of_isMultilinearFn`; mumbai's completeness asks for it of every stack claim.
* `honestRoot H S R q`: the Merkle root of the stack's word at level `0`'s height;
  `honestSeed H F pre claims = F(H(pre ‖ claims) ‖ 0)`, the transcript's start `opening::verify`
  computes; `honestOpen H F S R pre q claims fuel`: mumbai's `prove` of `variantProg S R claims`
  with the honest prover from that seed.
* `honestOpen_accepts`: at an admissible shape, for claims of the table's length whose stack claims
  `(S.weight c, c.value)` hold of the stack `q` (`StackClaim.Holds`), every proof the honest prover
  produces starts with the honest root and is accepted by the compiled program, **for every hash
  function and permutation**. After the length check `variantProg` is mumbai's `openingProgram`
  (`variantProg_eq_openingProgram`), whose interactive completeness is `runI_openingProgram`; the
  compilation is `runProof_prove`.
* The proofs of work: every one of the program has `17` bits (`grind_bits_variantProg`); the prover
  produces a proof when the `17`-bit search finds a nonce below `fuel` from every sponge
  (`honestOpen_ne_none`), and fails only at a sponge where every nonce below `fuel` fails
  (`exists_failed_pow`).

## `opening::verify`

`openingVerify_honest`: for a layout `L` at an admissible shape and claims of the table's length
with `StackClaim.Holds L.logN (L.claimWeight c, c.value) q`, `opening::verify` with the honest root
accepts the honest proof from the layout's prefix `openingPrefix L R`. `ours_complete`: for the
witness, wiring and quotient layouts at every supported size `17 ≤ log_rows ≤ 22`
(`layouts_ok`), at rate `1/2`; `ours_complete_22` at `log_rows = 22`.

## Against the random oracles

`romComplete_opening` (mumbai's `Compile.Rom.romComplete`, with the program's cost
`costLE_variant`): run against the random oracles from the statement's seeding `famSeed pre x`, the
honest prover makes the seeded verifier reject with probability at most

  `openingError fuel = (2 + 40483 · (2^27 + 2·fuel + 2) + 10122) · (1 - 2^-17)^fuel`,

which is below `2^-277` at `fuel = 2^25` (`openingError_le`). `romComplete_ours`: the same for
`opening::verify` itself (`WhirBridge.ourVerifier`, the verifier of `opening_sound`) given the root
the proof announces; `ours_romComplete`: for our three layouts at every supported size, below
`2^-277` at `fuel = 2^25`.
-/

namespace Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open WhirBridge (Stacking Claim variantProg rootOf rootHeight openingVerifyWithHash openingPrefix
  claimsBytes publicDigest)
open Finset

/-! ## Multiaffine weights are multilinear -/

/-- **A multiaffine function is the multilinear extension of its values on the cube**, the
converse of mumbai's `isMultiaffine_of_isMultilinearFn`. -/
theorem isMultilinearFn_of_isMultiaffine {n : ℕ} {Φ : List E → E} (hΦ : IsMultiaffine n Φ) :
    IsMultilinearFn n Φ := by
  induction n generalizing Φ with
  | zero =>
    rw [Whir.Complete.isMultilinearFn_iff]
    intro p hp
    obtain rfl := List.eq_nil_of_length_eq_zero hp
    simp [boolPoint, eqEval]
  | succ n ih =>
    have hb : ∀ b : E, IsMultiaffine n fun r ↦ Φ (b :: r) := fun b l hl k hk X ↦ by
      simpa using hΦ (b :: l) (by simp [hl]) (k + 1) (by omega) X
    rw [Whir.Complete.isMultilinearFn_iff]
    intro p hp
    obtain ⟨c, p, rfl⟩ := List.exists_cons_of_length_eq_add_one hp
    have hp' : p.length = n := by simpa using hp
    have h0 := (Whir.Complete.isMultilinearFn_iff n _).mp (ih (hb 0)) p hp'
    have h1 := (Whir.Complete.isMultilinearFn_iff n _).mp (ih (hb 1)) p hp'
    rw [pow_succ, mul_comm (2 ^ n) 2, Whir.Complete.sum_range_two_mul, hΦ.head p hp' c, h0, h1,
      mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    simp only [Whir.Complete.boolPoint_two_mul, Whir.Complete.boolPoint_two_mul_add_one,
      Whir.Complete.eqEval_cons]
    linear_combination (-(c * Φ (0 :: boolPoint n x) * eqEval (boolPoint n x) p) -
      Φ (1 :: boolPoint n x) * eqEval (boolPoint n x) p) * Whir.Complete.two_eq_zero_E

/-! ## The honest prover of a stacking's opening -/

section Generic

variable (H : Bytes → Digest) (F : KeccakState → KeccakState)

/-- **The honest root**: the Merkle root of the stack's word (mumbai's `stackWord`, the word
`stackCommit` commits) at level `0`'s height `log_n − 6 + R`. -/
def honestRoot (S : Stacking) (R : ℕ) (q : Column S.logN) : Digest :=
  treeRoot H (rootHeight S.logN R) (Whir.Complete.stackWord S.logN q)

/-- **The transcript's start** `opening::verify` computes from the prefix `pre` and the claims:
`F(H(pre ‖ claims) ‖ 0)`. -/
def honestSeed (pre : Bytes) (claims : List Claim) : KeccakState :=
  F (seedInput (H (pre ++ claimsBytes claims)) publicDigest)

/-- **The honest interactive prover** of a stacking's opening: mumbai's `openingProver` of the
stack `q` and the claims' stack claims (commit the stack's word, then the honest WHIR opening). -/
def honestProver (S : Stacking) (R : ℕ) (q : Column S.logN) (claims : List Claim) : Strategy :=
  Whir.Complete.openingProver S.logN R q (S.claims claims)

/-- **The honest compiled prover** of a stacking's opening (mumbai's `prove`) from the
transcript's start of the prefix `pre`; `none` when a proof-of-work search finds no nonce below
`fuel`. -/
def honestOpen (S : Stacking) (R : ℕ) (pre : Bytes) (q : Column S.logN) (claims : List Claim)
    (fuel : ℕ) : Option Proof :=
  prove H F (variantProg S R claims) (honestProver S R q claims) (honestSeed H F pre claims) fuel

end Generic

/-- After the length check, the program is mumbai's `openingProgram` of the claims' stack
claims. -/
theorem variantProg_eq_openingProgram (S : Stacking) (R : ℕ) (claims : List Claim)
    (hlen : ∀ c ∈ claims, c.point.length = S.vars) :
    variantProg S R claims = Whir.Complete.openingProgram S.logN R (S.claims claims) := by
  unfold variantProg Whir.Complete.openingProgram
  rw [Stacking.check_eq_ite, ite_eq_left hlen]

/-- **The honest prover wins every interactive run** of the program, with well-shaped words, when
the claims have the table's length and hold of the stack. -/
theorem runI_variantProg {S : Stacking} {R : ℕ} (hw : Whir.Admissible S.logN R)
    (q : Column S.logN) (claims : List Claim) (hlen : ∀ c ∈ claims, c.point.length = S.vars)
    (hholds : ∀ c ∈ claims, StackClaim.Holds S.logN (S.weight c, c.value) q)
    (hextra : ∀ sc ∈ S.extra, StackClaim.Holds S.logN sc q)
    (chal : List Ev → E) :
    runI (variantProg S R claims) (honestProver S R q claims) chal = some true ∧
      shapedI (variantProg S R claims) (honestProver S R q claims) chal := by
  rw [variantProg_eq_openingProgram S R claims hlen]
  refine Whir.Complete.runI_openingProgram hw q (S.claims claims) (fun c hc ↦ ?_)
    (fun c hc ↦ isMultilinearFn_of_isMultiaffine (S.isMultiaffine_claims claims c hc)) chal
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact hholds c' hc'
  · exact hextra c hc

/-- The word the honest prover commits first: the stack's. -/
theorem honestProver_word_nil (S : Stacking) (R : ℕ) (q : Column S.logN) (claims : List Claim) :
    (honestProver S R q claims).word [] = Whir.Complete.stackWord S.logN q := rfl

/-- A compiled proof of a program that starts with a commitment starts with the root of the word
the strategy commits. -/
theorem rootOf_prove_commit (H : Bytes → Digest) (F : KeccakState → KeccakState) {ht w : ℕ}
    {k : Prog Bool} {S : Strategy} {seed : KeccakState} {fuel : ℕ} {π : Proof}
    (h : prove H F (Prog.commit ht w k) S seed fuel = some π) :
    rootOf π = some (treeRoot H ht (S.word [])) := by
  simp only [prove, proveFrom, Option.map_map] at h
  obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact digestOfScalars_digestScalars _

/-- **Completeness of a stacking's opening, for every hash function and permutation.** At an
admissible shape, for claims of the table's length that hold of the stack `q`, every proof the
honest prover produces starts with the honest root, and the program accepts it from the
transcript's start. -/
theorem honestOpen_accepts (H : Bytes → Digest) (F : KeccakState → KeccakState) {S : Stacking}
    {R : ℕ} (hw : Whir.Admissible S.logN R) (pre : Bytes) (q : Column S.logN)
    (claims : List Claim) (hlen : ∀ c ∈ claims, c.point.length = S.vars)
    (hholds : ∀ c ∈ claims, StackClaim.Holds S.logN (S.weight c, c.value) q)
    (hextra : ∀ sc ∈ S.extra, StackClaim.Holds S.logN sc q) (fuel : ℕ)
    {π : Proof} (hπ : honestOpen H F S R pre q claims fuel = some π) :
    rootOf π = some (honestRoot H S R q) ∧
      runProofWithHash (m := Id) H F (variantProg S R claims) (honestSeed H F pre claims) π =
        true := by
  refine ⟨?_, runProof_prove H F _ _ _ fuel
    (fun chal ↦ (runI_variantProg hw q claims hlen hholds hextra chal).1)
    (fun chal ↦ (runI_variantProg hw q claims hlen hholds hextra chal).2) hπ⟩
  unfold honestOpen at hπ
  rw [WhirBridge.variantProg_eq hw] at hπ
  exact rootOf_prove_commit H F hπ

/-! ## The proofs of work -/

/-- The program's proofs of work: WHIR's, of `Whir.queryGrindingBits = 17` bits. -/
theorem movesOK_variantProg (S : Stacking) (R : ℕ) (claims : List Claim) :
    EndToEnd.Sound.MovesOK (· = Whir.queryGrindingBits) True (variantProg S R claims) := by
  refine EndToEnd.Sound.MovesOK.seq
    ((EndToEnd.Sound.movesOK_commitStack _ _).mono (fun _ h ↦ h.elim) id) fun _ ↦
      EndToEnd.Sound.MovesOK.seq ?_ fun _ ↦ EndToEnd.Sound.MovesOK.pure _
  exact EndToEnd.Sound.MovesOK.seq (EndToEnd.Sound.MovesOK.require _) fun _ ↦
    EndToEnd.Sound.movesOK_verifyStackedOpening _ _ _

/-- **Every proof of work of the program has `17` bits**, along any history. -/
theorem grind_bits_variantProg {S : Stacking} {R : ℕ} {claims : List Claim} {h : List Ev}
    {bits : ℕ} {k : Prog Bool} (hg : (variantProg S R claims).after h = some (.grind bits k)) :
    bits = Whir.queryGrindingBits :=
  ((movesOK_variantProg S R claims).after hg).1

section Pow

variable (H : Bytes → Digest) (F : KeccakState → KeccakState) (S : Stacking) (R : ℕ)
  (pre : Bytes) (q : Column S.logN) (claims : List Claim) (fuel : ℕ)

/-- **The honest prover produces a proof** when every proof-of-work search along the program finds
a nonce below `fuel` (mumbai's `prove_ne_none`). -/
theorem honestOpen_ne_none_of
    (hg : ∀ h bits k sp, (variantProg S R claims).after h = some (.grind bits k) →
      findNonce F bits sp fuel ≠ none) :
    honestOpen H F S R pre q claims fuel ≠ none :=
  prove_ne_none H F _ _ _ fuel hg

/-- **The honest prover produces a proof** when the `17`-bit proof-of-work search finds a nonce
below `fuel` from every sponge. -/
theorem honestOpen_ne_none (hpow : ∀ sp, findNonce F Whir.queryGrindingBits sp fuel ≠ none) :
    honestOpen H F S R pre q claims fuel ≠ none :=
  honestOpen_ne_none_of H F S R pre q claims fuel fun _ _ _ sp hg ↦ by
    rw [grind_bits_variantProg hg]
    exact hpow sp

/-- **The honest prover fails only at a proof of work**: if it produces no proof, the program
reaches a `17`-bit proof of work at a sponge where every nonce below `fuel` fails. -/
theorem exists_failed_pow (h : honestOpen H F S R pre q claims fuel = none) :
    ∃ hist k sp, (variantProg S R claims).after hist = some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel,
        powOk Whir.queryGrindingBits (nonceOf n) (powStep F sp (nonceOf n)).1 = false := by
  by_contra hne
  refine honestOpen_ne_none_of H F S R pre q claims fuel (fun hist bits k sp hg hn ↦ hne ?_) h
  obtain rfl := grind_bits_variantProg hg
  exact ⟨hist, k, sp, hg, ((findNonce_eq_none_iff F _ sp fuel).1 hn).2⟩

end Pow

/-- **Completeness of a stacking's opening, conditioned on the proofs of work**: when the
`17`-bit search finds a nonce below `fuel` from every sponge, the honest prover produces a proof,
it starts with the honest root, and the program accepts it. -/
theorem exists_honestOpen_accepts (H : Bytes → Digest) (F : KeccakState → KeccakState)
    {S : Stacking} {R : ℕ} (hw : Whir.Admissible S.logN R) (pre : Bytes) (q : Column S.logN)
    (claims : List Claim) (hlen : ∀ c ∈ claims, c.point.length = S.vars)
    (hholds : ∀ c ∈ claims, StackClaim.Holds S.logN (S.weight c, c.value) q)
    (hextra : ∀ sc ∈ S.extra, StackClaim.Holds S.logN sc q) (fuel : ℕ)
    (hpow : ∀ sp, findNonce F Whir.queryGrindingBits sp fuel ≠ none) :
    ∃ π, honestOpen H F S R pre q claims fuel = some π ∧
      rootOf π = some (honestRoot H S R q) ∧
      runProofWithHash (m := Id) H F (variantProg S R claims) (honestSeed H F pre claims) π =
        true := by
  obtain ⟨π, hπ⟩ := Option.ne_none_iff_exists'.mp
    (honestOpen_ne_none H F S R pre q claims fuel hpow)
  exact ⟨π, hπ, honestOpen_accepts H F hw pre q claims hlen hholds hextra fuel hπ⟩

/-! ## `opening::verify` -/

/-- **Completeness of `opening::verify`, for every hash function and permutation.** For a layout
at an admissible shape, claims of the table's length that hold of the stack `q` (each claim's
weight `Layout.claimWeight` paired with the stack is its value), the verifier accepts every proof
the honest prover produces, from the layout's prefix, against the honest root. -/
theorem openingVerify_honest (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (L : WhirBridge.Layout) {R : ℕ} (hw : Whir.Admissible L.logN R) (q : Column L.logN)
    (claims : List Claim) (hne : claims.isEmpty = false)
    (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (hholds : ∀ c ∈ claims, StackClaim.Holds L.logN (L.claimWeight c, c.value) q)
    (hextra : ∀ sc ∈ L.extra, StackClaim.Holds L.logN sc q) (fuel : ℕ)
    {π : Proof}
    (hπ : honestOpen H F L.stacking R (openingPrefix L R) q claims fuel = some π) :
    openingVerifyWithHash (m := Id) H F L R (honestRoot H L.stacking R q) claims π = true := by
  obtain ⟨hroot, hacc⟩ :=
    honestOpen_accepts H F (S := L.stacking) hw (openingPrefix L R) q claims hlen hholds hextra fuel hπ
  unfold openingVerifyWithHash
  rw [ite_eq_left ⟨hne, hlen⟩]
  show (if rootOf π = some (honestRoot H L.stacking R q) then
    runProofWithHash (m := Id) H F (WhirBridge.ourProg L R claims)
      (honestSeed H F (openingPrefix L R) claims) π else pure false) = true
  rw [ite_eq_left hroot, WhirBridge.ourProg_eq]
  exact hacc

/-- **Completeness of `opening::verify`, conditioned on the proofs of work**: when the `17`-bit
search finds a nonce below `fuel` from every sponge, the honest prover produces a proof and the
verifier accepts it against the honest root. -/
theorem exists_openingVerify_honest (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (L : WhirBridge.Layout) {R : ℕ} (hw : Whir.Admissible L.logN R) (q : Column L.logN)
    (claims : List Claim) (hne : claims.isEmpty = false)
    (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (hholds : ∀ c ∈ claims, StackClaim.Holds L.logN (L.claimWeight c, c.value) q)
    (hextra : ∀ sc ∈ L.extra, StackClaim.Holds L.logN sc q) (fuel : ℕ)
    (hpow : ∀ sp, findNonce F Whir.queryGrindingBits sp fuel ≠ none) :
    ∃ π, honestOpen H F L.stacking R (openingPrefix L R) q claims fuel = some π ∧
      openingVerifyWithHash (m := Id) H F L R (honestRoot H L.stacking R q) claims π = true := by
  obtain ⟨π, hπ⟩ := Option.ne_none_iff_exists'.mp
    (honestOpen_ne_none H F L.stacking R (openingPrefix L R) q claims fuel hpow)
  exact ⟨π, hπ, openingVerify_honest H F L hw q claims hne hlen hholds hextra fuel hπ⟩

/-- **Completeness of the protocol's three openings**, for every supported size
`17 ≤ log_rows ≤ 22`, at rate `1/2`: the witness, wiring and quotient layouts. -/
theorem ours_complete (H : Bytes → Digest) (F : KeccakState → KeccakState) (r : ℕ)
    (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows) (L : WhirBridge.Layout)
    (hLr : L = WhirBridge.witnessLayout r ∨ L = WhirBridge.wiringLayout r ∨
      L = WhirBridge.quotientLayout r)
    (q : Column L.logN) (claims : List Claim) (hne : claims.isEmpty = false)
    (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (hholds : ∀ c ∈ claims, StackClaim.Holds L.logN (L.claimWeight c, c.value) q)
    (hextra : ∀ sc ∈ L.extra, StackClaim.Holds L.logN sc q) (fuel : ℕ)
    {π : Proof}
    (hπ : honestOpen H F L.stacking WhirBridge.logInvRate (openingPrefix L WhirBridge.logInvRate)
      q claims fuel = some π) :
    openingVerifyWithHash (m := Id) H F L WhirBridge.logInvRate
      (honestRoot H L.stacking WhirBridge.logInvRate q) claims π = true := by
  have hok := WhirBridge.layouts_ok r h1 h2
  have hw : Whir.Admissible L.logN WhirBridge.logInvRate := by
    rcases hLr with rfl | rfl | rfl
    exacts [hok.1, hok.2.1, hok.2.2]
  exact openingVerify_honest H F L hw q claims hne hlen hholds hextra fuel hπ

/-- **The deployed size**, `log_rows = 22`. -/
theorem ours_complete_22 (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (L : WhirBridge.Layout)
    (hLr : L = WhirBridge.witnessLayout 22 ∨ L = WhirBridge.wiringLayout 22 ∨
      L = WhirBridge.quotientLayout 22)
    (q : Column L.logN) (claims : List Claim) (hne : claims.isEmpty = false)
    (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (hholds : ∀ c ∈ claims, StackClaim.Holds L.logN (L.claimWeight c, c.value) q)
    (hextra : ∀ sc ∈ L.extra, StackClaim.Holds L.logN sc q) (fuel : ℕ)
    {π : Proof}
    (hπ : honestOpen H F L.stacking WhirBridge.logInvRate (openingPrefix L WhirBridge.logInvRate)
      q claims fuel = some π) :
    openingVerifyWithHash (m := Id) H F L WhirBridge.logInvRate
      (honestRoot H L.stacking WhirBridge.logInvRate q) claims π = true :=
  ours_complete H F 22 (by decide) (by decide) L hLr q claims hne hlen hholds hextra fuel hπ

/-! ## Against the random oracles -/

section Rom

open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-- **The queries** of the honest prover and the verifier together, at a fuel of `fuel` nonces
per proof of work: the seed's hash and permutation, the program's cost (`costLE_variant`,
`40483` quarter-queries) at the prover's factor `proverFactor costHeight fuel = 2^27 + 2·fuel + 2`,
and the verifier's bound `variantQueries = 10122`. -/
def openingQueries (fuel : ℕ) : ℕ :=
  1 + 1 + (2 + (4 + (2 + whirBound))) * proverFactor costHeight fuel + WhirBridge.variantQueries

/-- **The completeness error** at a fuel of `fuel`: every query may complete a proof of work whose
nonces all failed, each with probability `1 - 2^-17`. -/
noncomputable def openingError (fuel : ℕ) : ℝ≥0∞ :=
  (openingQueries fuel : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ fuel

/-- **Completeness of a stacking's opening in the random-oracle model** (mumbai's
`Compile.Rom.romComplete`). For a statement `x` whose claims hold of the stack `q`, at an
admissible shape and a fuel of at most `2^64` nonces: the honest prover, run against the random
oracles from the statement's seeding `famSeed pre x` (the transcript's start of `opening::verify`
with prefix `pre`), makes the seeded verifier reject with probability at most
`openingError fuel`. -/
theorem romComplete_opening {S : Stacking} {R : ℕ} (hw : Whir.Admissible S.logN R)
    (pre : Bytes) (x : WhirBridge.Stmt S) (q : Column S.logN)
    (hholds : ∀ c ∈ x.claims, StackClaim.Holds S.logN (S.weight c, c.value) q)
    (hextra : ∀ sc ∈ S.extra, StackClaim.Holds S.logN sc q) {fuel : ℕ}
    (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment
        (honestComp (WhirBridge.famSeed pre x) (variantProg S R x.claims)
          (honestProver S R q x.claims) fuel)
        (verifierComp (WhirBridge.famSeed pre x) (variantProg S R x.claims))}[z.1.2 = false] ≤
      openingError fuel := by
  have h := romComplete (variantProg S R x.claims) (honestProver S R q x.claims)
    (WhirBridge.famSeed pre x) (bits := Whir.queryGrindingBits) (by decide) (by decide) hfuel
    (fun _ _ _ hg ↦ grind_bits_variantProg hg)
    (fun chal ↦ (runI_variantProg hw q x.claims x.wide hholds hextra chal).1)
    (fun chal ↦ (runI_variantProg hw q x.claims x.wide hholds hextra chal).2)
    (WhirBridge.costLE_variant S R x.claims)
  exact h.trans (le_of_eq rfl)

/-- **The layout's opening in the random-oracle model**: `romComplete_opening` at the layout's
stacking and prefix. -/
theorem romComplete_layout (L : WhirBridge.Layout) {R : ℕ} (hw : Whir.Admissible L.logN R)
    (x : WhirBridge.Stmt L.stacking) (q : Column L.logN)
    (hholds : ∀ c ∈ x.claims, StackClaim.Holds L.logN (L.claimWeight c, c.value) q)
    (hextra : ∀ sc ∈ L.extra, StackClaim.Holds L.logN sc q) {fuel : ℕ}
    (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment
        (honestComp (WhirBridge.famSeed (openingPrefix L R) x) (variantProg L.stacking R x.claims)
          (honestProver L.stacking R q x.claims) fuel)
        (verifierComp (WhirBridge.famSeed (openingPrefix L R) x)
          (variantProg L.stacking R x.claims))}[z.1.2 = false] ≤
      openingError fuel :=
  romComplete_opening (S := L.stacking) hw (openingPrefix L R) x q hholds hextra hfuel

/-- **The numbers**: at a fuel of `2^25` nonces per proof of work, the completeness error is
below `2^-277`: at most `2^43` queries, each missing with probability
`(1 - 2^-17)^(2^25) ≤ 2^-320` (`missProb_pow_four_le`). -/
theorem openingError_le : openingError (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 277 := by
  have hQ : openingQueries (2 ^ 25) ≤ 2 ^ 43 := by decide
  have hmiss :
      missProb Whir.queryGrindingBits ^ (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ (43 + 277) := by
    have := missProb_pow_four_le Whir.queryGrindingBits 64
    rwa [show 2 ^ Whir.queryGrindingBits * 4 * 64 = 2 ^ 25 by decide] at this
  unfold openingError
  calc (openingQueries (2 ^ 25) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ 2 ^ 25
      ≤ (2 : ℝ≥0∞) ^ 43 * (2 : ℝ≥0∞)⁻¹ ^ (43 + 277) := by
        gcongr
        exact_mod_cast hQ
    _ = (2 : ℝ≥0∞)⁻¹ ^ 277 := by
        rw [pow_add, ← mul_assoc, ← mul_pow,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

/-- A program that starts with a commitment rejects, in any lawful monad, a proof whose first two
scalars encode no root: its first two absorptions fill no block, so they make no query. -/
theorem runProofWithHash_commit_of_rootOf_none {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : Bytes → m Digest) (F : KeccakState → m KeccakState) {ht w : ℕ} {k : Prog Bool}
    (seed : KeccakState) {π : Proof} (h : rootOf π = none) :
    runProofWithHash H F (Prog.commit ht w k) seed π = pure false := by
  rcases π with ⟨stream, openings⟩
  unfold rootOf at h
  rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
  · simp [runProofWithHash, runWithHash]
  · simp [runProofWithHash, runWithHash]
  · simp only at h
    simp [runProofWithHash, runWithHash, Compile.absorb, h, Compile.rateScalars]

/-- **`opening::verify` on the root the proof announces is the seeded verifier**: given the root
the proof's first two scalars encode (any root if they encode none), `opening::verify` as an
oracle computation is the verifier of `romComplete_opening` from the layout's seeding. -/
theorem ourVerifier_rootOf (L : WhirBridge.Layout) {R : ℕ} (hw : Whir.Admissible L.logN R)
    (x : WhirBridge.Stmt L.stacking) (hne : x.claims.isEmpty = false) (π : Proof) :
    WhirBridge.ourVerifier L R (((rootOf π).getD default, x), π) =
      verifierComp (WhirBridge.famSeed (openingPrefix L R) x)
        (variantProg L.stacking R x.claims) π := by
  rw [← WhirBridge.verifierFam_fam (openingPrefix L R) (x, π),
    WhirBridge.verifierFam_eq L R (((rootOf π).getD default, x), π), WhirBridge.ourVerifier_eq]
  rw [if_pos hne]
  refine bind_congr fun seed ↦ ?_
  rcases hr : rootOf π with _ | r
  · rw [ite_eq_right (by simp), WhirBridge.variantProg_eq hw,
      runProofWithHash_commit_of_rootOf_none _ _ _ hr]
  · simp

/-- **The honest prover of `opening::verify` against the random oracles**: the honest proof from
the statement's seeding, output with the statement and the root its first two scalars encode, the
root of the honest commitment (its first message; any root if a proof-of-work search failed and
the proof is empty). -/
noncomputable def honestOurs (L : WhirBridge.Layout) (R : ℕ) (x : WhirBridge.Stmt L.stacking)
    (q : Column L.logN) (fuel : ℕ) :
    OracleComp KeccakCalls ((Digest × WhirBridge.Stmt L.stacking) × Proof) :=
  (fun π ↦ (((rootOf π).getD default, x), π)) <$>
    honestComp (WhirBridge.famSeed (openingPrefix L R) x) (variantProg L.stacking R x.claims)
      (honestProver L.stacking R q x.claims) fuel

/-- **Completeness of `opening::verify` in the random-oracle model.** For a layout at an
admissible shape, a statement whose claims hold of the stack `q` and a fuel of at most `2^64`
nonces: in the experiment of `opening_sound` with the honest prover as the adversary,
`opening::verify` rejects with probability at most `openingError fuel`. -/
theorem romComplete_ours (L : WhirBridge.Layout) {R : ℕ} (hw : Whir.Admissible L.logN R)
    (x : WhirBridge.Stmt L.stacking) (q : Column L.logN) (hne : x.claims.isEmpty = false)
    (hholds : ∀ c ∈ x.claims, StackClaim.Holds L.logN (L.claimWeight c, c.value) q)
    (hextra : ∀ sc ∈ L.extra, StackClaim.Holds L.logN sc q) {fuel : ℕ}
    (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← romExperiment (honestOurs L R x q fuel) (WhirBridge.ourVerifier L R)}[
        z.1.2 = false] ≤ openingError fuel := by
  unfold honestOurs
  rw [romExperiment_map, prEvent_map]
  have hV : (fun π ↦ WhirBridge.ourVerifier L R (((rootOf π).getD default, x), π)) =
      verifierComp (WhirBridge.famSeed (openingPrefix L R) x)
        (variantProg L.stacking R x.claims) :=
    funext fun π ↦ ourVerifier_rootOf L hw x hne π
  rw [hV]
  exact romComplete_layout L hw x q hholds hextra hfuel

/-- **The protocol's three openings in the random-oracle model**, for every supported size
`17 ≤ log_rows ≤ 22` at rate `1/2`: at a fuel of `2^25` nonces, `opening::verify` rejects the
honest prover with probability below `2^-277`. -/
theorem ours_romComplete (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows) (L : WhirBridge.Layout)
    (hLr : L = WhirBridge.witnessLayout r ∨ L = WhirBridge.wiringLayout r ∨
      L = WhirBridge.quotientLayout r)
    (x : WhirBridge.Stmt L.stacking) (q : Column L.logN) (hne : x.claims.isEmpty = false)
    (hholds : ∀ c ∈ x.claims, StackClaim.Holds L.logN (L.claimWeight c, c.value) q)
    (hextra : ∀ sc ∈ L.extra, StackClaim.Holds L.logN sc q) :
    Pr{let z ← romExperiment (honestOurs L WhirBridge.logInvRate x q (2 ^ 25))
        (WhirBridge.ourVerifier L WhirBridge.logInvRate)}[z.1.2 = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 277 := by
  have hok := WhirBridge.layouts_ok r h1 h2
  have hw : Whir.Admissible L.logN WhirBridge.logInvRate := by
    rcases hLr with rfl | rfl | rfl
    exacts [hok.1, hok.2.1, hok.2.2]
  exact (romComplete_ours L hw x q hne hholds hextra (by norm_num)).trans openingError_le

end Rom

/-! ## Axioms -/

/--
info: 'Completeness.isMultilinearFn_of_isMultiaffine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms isMultilinearFn_of_isMultiaffine

/--
info: 'Completeness.honestOpen_accepts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms honestOpen_accepts

/--
info: 'Completeness.exists_honestOpen_accepts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms exists_honestOpen_accepts

/--
info: 'Completeness.exists_failed_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms exists_failed_pow

/--
info: 'Completeness.openingVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms openingVerify_honest

/--
info: 'Completeness.exists_openingVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms exists_openingVerify_honest

/--
info: 'Completeness.ours_complete_22' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ours_complete_22

/--
info: 'Completeness.romComplete_opening' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms romComplete_opening

/--
info: 'Completeness.romComplete_ours' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms romComplete_ours

/--
info: 'Completeness.openingError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms openingError_le

/--
info: 'Completeness.ours_romComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ours_romComplete

end Completeness
