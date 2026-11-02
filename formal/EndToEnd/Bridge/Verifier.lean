-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Opening
import Bridge.Chain
import Soundness.Hypotheses

/-!
# The statement's verifier is F4's composed verifier

`PcsQuotient.verifyWith` (the reduction, then the three openings, each run only if the ones before
accepted) against F4's deployed verifier (`Compose.chainWith`, then `ourVerifier` on
`Compose.deployD c 22`'s three inputs, `Soundness.verifyES`'s shape), on a proof whose two roots'
scalars name digests:

* **`verifyWith_eq_verifyES`**: for every monad and permutation `F`, given that the statement's claims
  are `Compose.Reduce.reduce`'s at the constants `c` (`ClaimsMatch c`), the statement's verifier over
  `F` is `Soundness.verifyES` (F4's chain and the three openings with the statement's early stops,
  each opening `ourVerifierEarly`: rejected before any query when its stream has fewer than two
  scalars) on the converted proof, its two calls answered over `F` (`keccakCallsWith F`);
* **`verifierBridge_of_claims`**: over `π` (mumbai's `keccakCallsOverQueryPermutation`), that is
  `Soundness.VerifierBridge c h`.
-/

namespace Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile QuotientRpm QuotientSecurity OracleComp

/-! ## The claims -/

/-- The statement's four claims as F4's `reduce` outputs them. -/
def claimsTr (cl : PcsQuotient.Claims) : Compose.Reduce.Reduced :=
  ⟨claimTr cl.witness, claimTr cl.wiring, claimTr cl.quotient, claimTr cl.sum⟩

/-- **The statement's claims are `reduce`'s at the constants `c`** (`Bridge/Claims.lean` proves it at
the statement's constants). -/
def ClaimsMatch (c : Compose.Reduce.Consts) : Prop :=
  ∀ (stmt : PcsQuotient.Statement) (α β γ t ρ : E) (a : Vector E 4) (next : E),
    (PcsQuotient.claimsAt 22 stmt α β γ t ρ a next).map claimsTr =
      Compose.Reduce.reduce c 24 (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t
        (fun i => a.get i) next ρ

/-! ## F4's verifier with the statement's early stops -/

/-- The early-stop opening of `Bridge/Opening.lean` is `Soundness.verifyES`'s. -/
theorem ourVerifierEarly_eq : @ourVerifierEarly = @Soundness.ourVerifierEarly := rfl

/-- F4's chain, its hash answered by any implementation of the two calls. -/
theorem simulateQ_chainWith {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl LeanVM.KeccakCalls r) {P : Params E} {B : P.Bounds} (W : Wire P B)
    (π : Compose.RootProof E) :
    simulateQ impl (Compose.chainWith W Compose.hash256 π) =
      Compose.chainWith W (fun x => Compose.toB <$> Rom.implH impl x) π := by
  simp [Compose.chainWith, Compose.hash256, Rom.simulateQ_queryH, map_eq_bind_pure_comp]

/-! ## The three openings -/

/-- `openingWith_eq_ourVerifier` at a layout given up to `layoutTr`. -/
theorem openingWith_eq_ourVerifier' {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (L : PcsQuotient.Layout) (L' : WhirBridge.Layout)
    (hLL : layoutTr L = L') (hL : LayoutOK L) (hw : Whir.Admissible L.logN WhirBridge.logInvRate)
    (root : Digest) (x : WhirBridge.Stmt L'.stacking) (claims : List PcsQuotient.Claim)
    (hx : x.claims = claims.map claimTr) (proof : Proof) :
    PcsQuotient.openingWith F L root claims proof =
      simulateQ (keccakCallsWith F)
        (Soundness.ourVerifierEarly L' WhirBridge.logInvRate ((root, x), proof)) := by
  subst hLL
  exact openingWith_eq_ourVerifier F L hL hw root x claims hx proof

theorem toStmt_claims_of {L : WhirBridge.Layout} {cs : List WhirBridge.Claim}
    (hshort : cs.length ≤ 2) (hwide : ∀ c ∈ cs, c.point.length = L.vars) :
    (Compose.toStmt L cs).claims = cs := by
  have he := Compose.extra_length_le L
  unfold Compose.toStmt
  rw [dif_pos ⟨by simp only [WhirBridge.Layout.stacking]; omega, hwide⟩]

theorem ofB_toB (d : Digest) : Compose.ofB (Compose.toB d) = d :=
  LeanVM.Rpm.digestOfRpm_toRpm d

theorem reduce_lengths {c : Compose.Reduce.Consts} {st : Fin 4 → E} {α β γ t : E} {a : Fin 4 → E}
    {next ρ : E} {r : Compose.Reduce.Reduced}
    (h : Compose.Reduce.reduce c 24 st α β γ t a next ρ = some r) :
    r.witness.point.length = 25 ∧ r.wiring.point.length = 24 ∧ r.quotient.point.length = 30 ∧
      r.sum.point.length = 30 := by
  obtain ⟨-, rfl⟩ := Compose.Reduce.reduce_eq_some h
  simp [Compose.Reduce.witness_point_eq, Compose.Reduce.wiring_point_eq,
    Compose.Reduce.quotient_point_eq, Compose.Reduce.sum_point_eq, Compose.Reduce.sumPoint]

/-! ## The verifier -/

/-- **The statement's verifier is F4's with the statement's early stops** (`Soundness.verifyES`), for
every monad and permutation `F`, on a proof whose roots' scalars name digests, given the claims
(`ClaimsMatch c`), for any wire with the limbs `eLimbs`. -/
theorem verifyWith_eq_verifyES {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (c : Compose.Reduce.Consts) (hcl : ClaimsMatch c)
    {P : Params E} {B : P.Bounds} (W : Wire P B) (hW : W.limbs = Soundness.eLimbs) (ir : Digest)
    (stmt : PcsQuotient.Statement) (proof : PcsQuotient.Proof) (r₁ r₂ : Digest)
    (h₁ : digestOfScalars proof.reduction.witnessRoot = some r₁)
    (h₂ : digestOfScalars proof.reduction.quotientRoot = some r₂) :
    PcsQuotient.verifyWith F 22 ir stmt proof =
      simulateQ (keccakCallsWith F)
        (Soundness.verifyES W c (Compose.withIr (Compose.toB ir) (Soundness.convP (stmt, proof)))) := by
  have hpo : (Compose.withIr (Compose.toB ir) (Soundness.convP (stmt, proof))).1 =
      rootProofIr ir stmt proof.reduction r₁ r₂ := by
    simp [Compose.withIr, Soundness.convP, Soundness.rootProofOf, rootProofIr, h₁, h₂,
      Soundness.stmtBytes]
  unfold PcsQuotient.verifyWith Soundness.verifyES
  rw [reduceWith_eq F W hW ir stmt proof.reduction r₁ r₂ h₁ h₂, simulateQ_bind, simulateQ_chainWith,
    hpo, bind_map_left]
  refine bind_congr fun ch => ?_
  have hred : Compose.reduceOf c 22 (rootProofIr ir stmt proof.reduction r₁ r₂) ch =
      (PcsQuotient.claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ proof.reduction.values
        proof.reduction.next).map claimsTr :=
    (hcl stmt ch.α ch.β ch.γ ch.t ch.ρ proof.reduction.values proof.reduction.next).symm
  rcases hc : PcsQuotient.claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ proof.reduction.values
      proof.reduction.next with _ | cl
  · rw [hc] at hred
    simp [hred]
  · rw [hc, Option.map_some] at hred
    have hsome : Compose.Reduce.reduce c 24
        (Compose.Reduce.stmtHalves (rootProofIr ir stmt proof.reduction r₁ r₂).stmt) ch.α ch.β ch.γ
        ch.t (rootProofIr ir stmt proof.reduction r₁ r₂).v.1
        (rootProofIr ir stmt proof.reduction r₁ r₂).v.2 ch.ρ = some (claimsTr cl) := hred
    obtain ⟨lw, lσ, lq, ls⟩ := reduce_lengths hsome
    obtain ⟨oW, oσ, oQ⟩ := layoutOK_layouts 22 (by decide) (by decide)
    obtain ⟨aW, aσ, aQ⟩ := WhirBridge.layouts_ok 22 (by decide) (by decide)
    have hwW : Whir.Admissible (PcsQuotient.witnessLayout 22).logN WhirBridge.logInvRate := by
      rw [← layoutTr_logN, layoutTr_witnessLayout]; exact aW
    have hwσ : Whir.Admissible (PcsQuotient.wiringLayout 22).logN WhirBridge.logInvRate := by
      rw [← layoutTr_logN, layoutTr_wiringLayout]; exact aσ
    have hwQ : Whir.Admissible (PcsQuotient.quotientLayout 22).logN WhirBridge.logInvRate := by
      rw [← layoutTr_logN, layoutTr_quotientLayout]; exact aQ
    set π := rootProofIr ir stmt proof.reduction r₁ r₂ with hπ
    have cW : ((Compose.deployD c 22).clW π ch).claims = [cl.witness].map claimTr := by
      show (Compose.toStmt _ (Compose.claimsFrom _ (Compose.reduceOf c 22 π ch) _)).claims = _
      rw [hred, Compose.claimsFrom_some]
      exact toStmt_claims_of (by simp) (by
        rw [show (WhirBridge.witnessLayout 22).vars = 25 from rfl]; simpa [claimsTr] using lw)
    have cσ : ((Compose.deployD c 22).clσ π ch).claims = [cl.wiring].map claimTr := by
      show (Compose.toStmt _ (Compose.claimsFrom _ (Compose.reduceOf c 22 π ch) _)).claims = _
      rw [hred, Compose.claimsFrom_some]
      exact toStmt_claims_of (by simp) (by
        rw [show (WhirBridge.wiringLayout 22).vars = 24 from rfl]; simpa [claimsTr] using lσ)
    have cQ : ((Compose.deployD c 22).clQ π ch).claims = [cl.quotient, cl.sum].map claimTr := by
      show (Compose.toStmt _ (Compose.claimsFrom _ (Compose.reduceOf c 22 π ch) _)).claims = _
      rw [hred, Compose.claimsFrom_some]
      refine toStmt_claims_of (by simp) ?_
      intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rw [show (WhirBridge.quotientLayout 22).vars = 30 from rfl]
      rcases hc with rfl | rfl
      · simpa [claimsTr] using lq
      · simpa [claimsTr] using ls
    have hR : (Compose.deployD c 22).R = WhirBridge.logInvRate := rfl
    simp only [Option.map_some]
    rw [openingWith_eq_ourVerifier' F _ (Compose.deployD c 22).Lw (layoutTr_witnessLayout 22) oW hwW
        r₁ ((Compose.deployD c 22).clW π ch) _ cW,
      openingWith_eq_ourVerifier' F _ (Compose.deployD c 22).Lσ (layoutTr_wiringLayout 22) oσ hwσ
        ir ((Compose.deployD c 22).clσ π ch) _ cσ,
      openingWith_eq_ourVerifier' F _ (Compose.deployD c 22).LQ (layoutTr_quotientLayout 22) oQ hwQ
        r₂ ((Compose.deployD c 22).clQ π ch) _ cQ]
    simp only [hred, Option.isSome_some, ↓reduceIte, simulateQ_bind]
    simp only [Compose.wIn, Compose.σIn, Compose.qIn, hπ, rootProofIr, ofB_toB, hR, Compose.withIr,
      Soundness.convP, Soundness.openProofsOf]
    refine bind_congr fun bW => ?_
    cases bW
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
      refine bind_congr fun bσ => ?_
      cases bσ <;> simp

/-- **`Soundness.VerifierBridge`**, given the claims at the constants `c`: the statement's verifier
over `π` is `Soundness.verifyES` over `π` (`keccakCallsOverQueryPermutation`) on the converted proof. -/
theorem verifierBridge_of_claims (c : Compose.Reduce.Consts) (h : Compose.IsCantor c.beta)
    (hcl : ClaimsMatch c) : Soundness.VerifierBridge c h := by
  intro ir stmt proof r₁ r₂ h₁ h₂
  show PcsQuotient.verifyWith Common.queryPermutation 22 ir stmt proof = _
  rw [verifyWith_eq_verifyES Common.queryPermutation c hcl
    (Soundness.deployedWire (Soundness.inst c h)) rfl ir stmt proof r₁ r₂ h₁ h₂,
    keccakCallsWith_queryPermutation]

end Bridge

/-- info: 'Bridge.simulateQ_chainWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.simulateQ_chainWith

/-- info: 'Bridge.verifyWith_eq_verifyES' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.verifyWith_eq_verifyES

/-- info: 'Bridge.verifierBridge_of_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.verifierBridge_of_claims
