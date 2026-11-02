-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Claims
import Compose.Rpm
import QuotientSecurity.Deployed
import PcsQuotient.Security

/-!
# The deployed objects the end theorem is about

`formal/Compose`'s random-permutation theorem (`knowledgeSoundness_wired_setup_rpm_bits`) is about
an abstract field `F`, parameters `P`, a `Wire` and a `Deploy`; the Statement
(`formal/Statement`, `PcsQuotient`) about the deployed membership proof. Here the first is
instantiated at the second:

* the field is mumbai's `E` (`F192`), F1's instance `inst c h` (`Hypotheses.lean`: the Cantor
  basis of `beta()`'s words, `coordinate_weight`'s weights, the deployed wiring), the openings
  `deployD c 22` (`reduce`'s claims, `Compose/Claims.lean`);
* **the wire** `deployedWire c h`: the statement's 64 bytes read as their halves then `1, 0, 0, 0`
  (`Reduce.stmtWords`), a field element held as its three limbs, low first, each a 64-bit lane
  (`eLimbs`: `F192`'s `(c0, c1, c2)`, the Statement's `challengeOf` and `scalarBytes`); its
  index root and encodings are never read by the composed verifier (the chain takes the root from
  the proof, and the commitments are the Merkle roots), and are any injective ones;
* **the proof's conversion** (`rootProofOf`, `openProofsOf`, `convAdv`): the Statement's proof is
  Compose's: the statement's `y ‖ root`, the two roots its scalars name (`digestOfScalars`), the
  four values and `next`, and the three opening proofs (mumbai's format on both sides);
* **the verifier with the Statement's early stops** (`verifyES`): the chain, then the three
  openings, each run only if the reduction (`reduce`) and the openings before it accept, an opening
  whose proof holds no root rejected before any query (`ourVerifierEarly`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge

/-! ## The limbs -/

/-- A field element as its three limbs, low first, each a 64-bit lane (`F192`'s `(c0, c1, c2)`). -/
def eLimbs : E ≃ Limbs where
  toFun x := ((x.limb 0).lane, (x.limb 1).lane, (x.limb 2).lane)
  invFun l := E.ofLimbs (K.ofLane l.1) (K.ofLane l.2.1) (K.ofLane l.2.2)
  left_inv x := by
    simp only
    have h : ∀ a : K, K.ofLane a.lane = a := fun _ => rfl
    rw [h, h, h, ofLimbs_limb]
  right_inv l := by
    obtain ⟨a, b, c⟩ := l
    have h : ∀ w : UInt64, (K.ofLane w).lane = w := fun _ => rfl
    simp only [limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, h]

/-! ## The wire -/

/-- A countable type's injective encoding as bytes (a run of zeros as long as its index). -/
noncomputable def countEnc (α : Type) [Countable α] : α → List UInt8 :=
  fun a => List.replicate ((Countable.exists_injective_nat α).choose a) 0

theorem countEnc_injective (α : Type) [Countable α] : Function.Injective (countEnc α) := by
  intro a b h
  have := congrArg List.length h
  simp only [countEnc, List.length_replicate] at this
  exact (Countable.exists_injective_nat α).choose_spec this

/-- Polynomials of degree at most `n` agree when their coefficients up to `n` do. -/
theorem poly_eq_of_coeff {p q : Polynomial E} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ i : Fin (n + 1), p.coeff i = q.coeff i) : p = q := by
  refine Polynomial.ext fun k => ?_
  by_cases hk : k ≤ n
  · exact h ⟨k, by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- A first message within the bounds is its coefficients up to the bound: finitely many. -/
instance finite_msg₁ {P : Params E} (B : P.Bounds) : Finite B.Msg₁ := by
  refine Finite.of_injective
    (fun g : B.Msg₁ => fun (j : Fin 4) (i : Fin (B.witness + 1)) => (g.1 j).coeff i) ?_
  intro g g' hg
  exact Subtype.ext (funext fun j => poly_eq_of_coeff (g.2 j) (g'.2 j)
    fun i => congrFun (congrFun hg j) i)

/-- A second message within the bounds is its five polynomials' coefficients up to the bound. -/
instance finite_msg₂ {P : Params E} (B : P.Bounds) : Finite B.Msg₂ := by
  refine Finite.of_injective
    (fun R : B.Msg₂ => fun (i : Fin (B.quotient + 1)) =>
      (R.1.h₀.coeff i, R.1.hHigh.coeff i, R.1.q.coeff i, R.1.qGate.coeff i, R.1.junk.coeff i)) ?_
  intro R R' hR
  obtain ⟨⟨h₀, hHigh, q, qGate, junk⟩, b₁, b₂, b₃, b₄, b₅⟩ := R
  obtain ⟨⟨h₀', hHigh', q', qGate', junk'⟩, b₁', b₂', b₃', b₄', b₅'⟩ := R'
  have e := fun i => congrFun hR i
  simp only [Prod.mk.injEq] at e
  refine Subtype.ext ?_
  simp only [Params.Quotients.mk.injEq]
  exact ⟨poly_eq_of_coeff b₁ b₁' fun i => (e i).1, poly_eq_of_coeff b₂ b₂' fun i => (e i).2.1,
    poly_eq_of_coeff b₃ b₃' fun i => (e i).2.2.1, poly_eq_of_coeff b₄ b₄' fun i => (e i).2.2.2.1,
    poly_eq_of_coeff b₅ b₅' fun i => (e i).2.2.2.2⟩

/-- **The deployed wire** for F1's instance `I`: the statement's bytes read as their halves then
`1, 0, 0, 0` (`stmtWords`), the limbs `eLimbs`; the index root and the encodings, which the
composed verifier does not read, any (zero, injective). -/
noncomputable def deployedWire (I : Instance E) : Wire I.params I.bounds where
  indexRoot := default
  decode := stmtWords
  limbs := eLimbs
  enc₁ := countEnc I.bounds.Msg₁
  enc₁_injective := countEnc_injective I.bounds.Msg₁
  enc₂ := countEnc I.bounds.Msg₂
  enc₂_injective := countEnc_injective I.bounds.Msg₂

theorem deployedWire_decode (I : Instance E) (sb : Vector UInt8 64) :
    (deployedWire I).decode sb = stmtWords sb := rfl

/-! ## The proof's conversion -/

/-- The statement's 64 bytes: `y`, then `root`. -/
def stmtBytes (stmt : PcsQuotient.Statement) : Vector UInt8 64 := stmt.y ++ stmt.root

/-- **The reduction's proof as Compose reads it**: the statement's bytes, the two roots the proof's
scalars name (zero if they name none: the Statement rejects such a proof), the four values and
`next`; the circuit's commitment is the setup's (`withIr`). -/
def rootProofOf (stmt : PcsQuotient.Statement) (proof : PcsQuotient.Proof) : RootProof E where
  stmt := stmtBytes stmt
  r₁ := toB ((digestOfScalars proof.reduction.witnessRoot).getD default)
  r₂ := toB ((digestOfScalars proof.reduction.quotientRoot).getD default)
  v := (fun i => proof.reduction.values.get i, proof.reduction.next)
  ir := default

/-- The three opening proofs, in mumbai's format on both sides. -/
def openProofsOf (proof : PcsQuotient.Proof) : OpenProofs :=
  (proof.witness, proof.wiring, proof.quotient)

/-- A statement and a proof as Compose's adversary outputs them. -/
def convP (z : PcsQuotient.Statement × PcsQuotient.Proof) : RootProof E × OpenProofs :=
  (rootProofOf z.1 z.2, openProofsOf z.2)

/-- **The Statement's adversary as Compose's**: it ignores the commitment it is given (it computes
whatever it needs of the public setup with `π`) and outputs its statement and proof, converted. -/
def convAdv (A : PcsQuotient.Adversary) :
    Bytes32 → OracleComp Common.RandomPermutationOracles (RootProof E × OpenProofs) :=
  fun _ => convP <$> A

/-! ## The verifier with early stops -/

variable {P : Params E} {B : P.Bounds}

/-- **An opening with the Statement's first stop**: a proof whose scalar stream holds fewer than two
scalars (no root) is rejected before any query (`PcsQuotient.openingWith` reads the root first);
otherwise `opening::verify` (`ourVerifier`), which rejects it too, after its seed. -/
def ourVerifierEarly (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof) :
    OracleComp KeccakCalls Bool :=
  match w.2.stream with
  | _ :: _ :: _ => ourVerifier L R w
  | _ => pure false

/-- **The deployed verifier with the Statement's early stops**: the chain; `false` if `reduce`
rejects (a vanishing denominator); then the witness, wiring and quotient openings of `deployD c 22`
(`ourVerifierEarly`), each run only if the one before accepted (`protocol::verify` then
`verify_openings`). -/
def verifyES (W : Wire P B) (c : Consts) (po : RootProof E × OpenProofs) :
    OracleComp KeccakCalls Bool :=
  chainWith W hash256 po.1 >>= fun ch =>
    if (reduceOf c 22 po.1 ch).isSome then
      ourVerifierEarly (deployD c 22).Lw (deployD c 22).R
          (wIn (deployD c 22) ⟨po.1, po.2, [], ch⟩) >>= fun bW =>
        if bW then
          ourVerifierEarly (deployD c 22).Lσ (deployD c 22).R
              (σIn (deployD c 22) ⟨po.1, po.2, [], ch⟩) >>= fun bσ =>
            if bσ then
              ourVerifierEarly (deployD c 22).LQ (deployD c 22).R
                (qIn (deployD c 22) ⟨po.1, po.2, [], ch⟩)
            else pure false
        else pure false
    else pure false

/-! ## The setup's log -/

/-- The setup tree's Keccak-256 evaluations as a transcript of Compose's (inputs, 32-byte
answers). -/
def treeTr (t : LeanVM.Prover.Tree) : Transcript :=
  (PcsQuotient.Tree.evaluations t).map fun e => (e.1, toB e.2)

end Soundness
