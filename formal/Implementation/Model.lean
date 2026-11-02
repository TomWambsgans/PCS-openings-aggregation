-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Verifier

/-!
# The `Wire` of the deployed contract, and the graph against `Wire.verifyWith`

`QuotientRpm.Wire` leaves open what the chain reads besides the proof. Here it is instantiated
(`wire`): the index root `idx` (an input, the contract's storage slot 0), the statement's 64 bytes
read as `statement::halves` reads them, then the words `(1, 0, 0, 0)` (`decodeStmt`), `F192`'s
limbs, and — the model's commitments being ideal — an injective encoding of each message, its
polynomials' coefficients up to the degree bound as `scalarWord`s (`encW`, `encQ`; the deployed
roots are Merkle roots of WHIR encodings, which the model does not have).

`verifyWith_eq`: the model's verifier with this `Wire` decides `Params.Accepts` at the challenges
of `modelVals`, the chain the graph's leaves hold on `calldataOf` (`leafVals_calldataOf`).

`graph_iff_verifyWith` (**F5**): on the calldata of a model proof `π` (its statement, the roots
`H(enc₁ g)`, `H(enc₂ R)` the model's chain absorbs, its five values), the contract reaches its calls
of `PCS_OPEN` and the claims it hands them hold of the tables whose polynomials are `π`'s messages,
exactly when no `1 + w_k(t)` vanishes and `Wire.verifyWith` accepts `π`.
-/

set_option linter.unusedSectionVars false

namespace Implementation

open QuotientRpm QuotientSecurity Program Emitted Polynomial

local notation "SQ" => QuotientSecurity.sq

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
  {limbs : F ≃ Limbs}

/-! ## Encodings of the messages -/

/-- A polynomial's coefficients `0 .. d`, each as the chain hashes a scalar. -/
def encPoly (limbs : F ≃ Limbs) (d : ℕ) (p : F[X]) : List UInt8 :=
  (List.range (d + 1)).flatMap fun i => scalarWord (limbs (p.coeff i))

theorem length_encPoly (d : ℕ) (p : F[X]) : (encPoly limbs d p).length = 32 * (d + 1) := by
  simp [encPoly, List.length_flatMap, mul_comm]

theorem flatMap_inj (f g : ℕ → List UInt8) (hf : ∀ i, (f i).length = 32) (hg : ∀ i, (g i).length = 32) :
    ∀ l : List ℕ, l.flatMap f = l.flatMap g → ∀ i ∈ l, f i = g i
  | [], _ => by simp
  | i :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hf, hg])
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h1
    · exact flatMap_inj f g hf hg l h2 j hj

theorem encPoly_inj {d : ℕ} {p q : F[X]} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (h : encPoly limbs d p = encPoly limbs d q) : p = q := by
  have hc := flatMap_inj _ _ (fun i => length_scalarWord _) (fun i => length_scalarWord _) _ h
  ext i
  by_cases hi : i ≤ d
  · exact limbs.injective (scalarWord_injective (hc i (List.mem_range.mpr (by omega))))
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

variable (hF : IsF192 limbs) (σ : Equiv.Perm (Fin (22 + 2) → Bool))

/-- The degree bounds of the protocol's parameters (`membershipBounds`). -/
noncomputable def bounds : (params hF σ).Bounds :=
  membershipBounds (basis hF) le24 σ (bConst limbs) (cConst limbs) (basis_hb0 hF) (basis_hb hF)

/-- The first message, its four polynomials' coefficients. -/
noncomputable def encW (g : (bounds hF σ).Msg₁) : List UInt8 :=
  encPoly limbs (bounds hF σ).witness (g.1 0) ++ encPoly limbs (bounds hF σ).witness (g.1 1) ++
    encPoly limbs (bounds hF σ).witness (g.1 2) ++ encPoly limbs (bounds hF σ).witness (g.1 3)

/-- The second message, its five polynomials' coefficients. -/
noncomputable def encQ (R : (bounds hF σ).Msg₂) : List UInt8 :=
  encPoly limbs (bounds hF σ).quotient R.1.h₀ ++ encPoly limbs (bounds hF σ).quotient R.1.hHigh ++
    encPoly limbs (bounds hF σ).quotient R.1.q ++ encPoly limbs (bounds hF σ).quotient R.1.qGate ++
    encPoly limbs (bounds hF σ).quotient R.1.junk

theorem encW_injective : Function.Injective (encW hF σ) := by
  intro g g' h
  simp only [encW] at h
  obtain ⟨h, h3⟩ := List.append_inj h (by simp [length_encPoly])
  obtain ⟨h, h2⟩ := List.append_inj h (by simp [length_encPoly])
  obtain ⟨h0, h1⟩ := List.append_inj h (by simp [length_encPoly])
  apply Subtype.ext
  funext j
  fin_cases j
  · exact encPoly_inj (g.2 0) (g'.2 0) h0
  · exact encPoly_inj (g.2 1) (g'.2 1) h1
  · exact encPoly_inj (g.2 2) (g'.2 2) h2
  · exact encPoly_inj (g.2 3) (g'.2 3) h3

theorem encQ_injective : Function.Injective (encQ hF σ) := by
  intro R R' h
  simp only [encQ] at h
  obtain ⟨h, h4⟩ := List.append_inj h (by simp [length_encPoly])
  obtain ⟨h, h3⟩ := List.append_inj h (by simp [length_encPoly])
  obtain ⟨h, h2⟩ := List.append_inj h (by simp [length_encPoly])
  obtain ⟨h0, h1⟩ := List.append_inj h (by simp [length_encPoly])
  obtain ⟨⟨a0, a1, a2, a3, a4⟩, d0, d1, d2, d3, d4⟩ := R
  obtain ⟨⟨b0, b1, b2, b3, b4⟩, e0, e1, e2, e3, e4⟩ := R'
  simp only at h0 h1 h2 h3 h4
  obtain rfl := encPoly_inj d0 e0 h0
  obtain rfl := encPoly_inj d1 e1 h1
  obtain rfl := encPoly_inj d2 e2 h2
  obtain rfl := encPoly_inj d3 e3 h3
  obtain rfl := encPoly_inj d4 e4 h4
  rfl

/-- The statement's 64 bytes as the model's eight words: `y`'s and `root`'s halves
(`statement::halves`), then `(1, 0, 0, 0)` (the words of the constants, `circuit::public_words`). -/
noncomputable def decodeStmt (sb : Vector UInt8 64) : Fin 8 → F :=
  ![elem limbs (halfOf sb 0), elem limbs (halfOf sb 1), elem limbs (halfOf sb 2),
    elem limbs (halfOf sb 3), 1, 0, 0, 0]

/-- **The `Wire` of the deployed contract**, for the index root `idx`. -/
noncomputable def wire (idx : Bytes32) : Wire (params hF σ) (bounds hF σ) where
  indexRoot := idx
  decode := decodeStmt (limbs := limbs)
  limbs := limbs
  enc₁ := encW hF σ
  enc₁_injective := encW_injective hF σ
  enc₂ := encQ hF σ
  enc₂_injective := encQ_injective hF σ

variable (H : List UInt8 → Vector UInt8 32) (idx : Bytes32)

/-- The chain's values of a model proof: its statement, the roots its messages hash to, its five
values. -/
noncomputable def proofVals (π : ChainProof (params hF σ) (bounds hF σ)) : Vals F :=
  modelVals H idx π.stmt (H (encW hF σ π.g)) (H (encQ hF σ π.R)) limbs (π.v.1 0) (π.v.1 1)
    (π.v.1 2) (π.v.1 3) π.v.2

theorem proofVals_a (π : ChainProof (params hF σ) (bounds hF σ)) :
    (proofVals hF σ H idx π).a = π.v.1 := by
  funext k; fin_cases k <;> rfl

-- `Wire.verifyWith` decides with classical instances.
open Classical in
/-- **The model's verifier with the deployed `Wire`** accepts exactly when `Params.Accepts` holds
at the challenges of the chain the graph's leaves hold (`proofVals`, `modelVals`). -/
theorem verifyWith_iff (π : ChainProof (params hF σ) (bounds hF σ)) :
    (wire hF σ idx).verifyWith (m := Id) H π = true ↔
      (params hF σ).Accepts (decodeStmt (limbs := limbs) π.stmt) π.g.1 π.R.1
        (proofVals hF σ H idx π).α (proofVals hF σ H idx π).β (proofVals hF σ H idx π).γ
        (proofVals hF σ H idx π).t π.v.1 π.v.2 (proofVals hF σ H idx π).ρ := by
  have hw : Wire.valueWords (wire hF σ idx) π.v =
      [π.v.1 0, π.v.1 1, π.v.1 2, π.v.1 3, π.v.2].flatMap fun x => scalarWord (limbs x) := by
    simp [Wire.valueWords, Wire.word, wire, List.append_assoc]
  unfold Wire.verifyWith Wire.afterValues
  rw [hw]
  exact decide_eq_true_iff

/-- **F5: the graph is the model's verifier.** On the calldata of a model proof `π` — its
statement's bytes, the roots `H(enc₁ g)` and `H(enc₂ R)` that `Wire.verifyWith` absorbs, its five
values — with tables `cW`, `cQ` whose polynomials are `π`'s messages and a wiring table `cF` of `σ`:
the contract (the graph, `run`) reaches its calls of `PCS_OPEN` with claims (`run_words`) that hold
of `cW`, `cF`, `cQ` exactly when no `1 + w_k(t)` vanishes and the model's verifier accepts `π`. -/
theorem graph_iff_verifyWith (hfr : FrobOK limbs) (π : ChainProof (params hF σ) (bounds hF σ))
    (cW : (Fin (22 + 1 + 1 + 1) → Bool) → F) (cF : (Fin (22 + 2) → Bool) → F)
    (hcF : ∀ x, (tablePoly cF).eval ((basis hF).point x) = (basis hF).point (σ x))
    (cQ : (Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → F)
    (hg : π.g.1 = witnessOfTable cW) (hR : π.R.1 = quotientsOfTable (yConst limbs) cQ) :
    let I := proofVals hF σ H idx π
    ((run H idx (calldataOf limbs π.stmt (H (encW hF σ π.g)) (H (encQ hF σ π.R))
        [π.v.1 0, π.v.1 1, π.v.1 2, π.v.1 3, π.v.2])).isSome ∧
      (mle cW (Fin.cons I.ρ (Fin.cons (I.ρ ^ 2) (claimPoint 2 (22 + 1) I.t)))
          = (∑ j, Params.opening I.ρ j * I.a j) / claimScale 2 (22 + 1) I.t ∧
        mle cF (claimPoint 0 (22 + 2) I.t) = I.next / claimScale 0 (22 + 2) I.t ∧
        mle cQ (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) I.t)
            ((params hF σ).vCells.eval I.t / (params hF σ).claimDen I.α I.β I.t I.a I.next)) I.ρ)
              (yConst limbs / (1 + yConst limbs))) (yConst limbs ^ 2 / (1 + yConst limbs ^ 2)))
          = (params hF σ).claimValue I.α I.β I.γ I.t I.ρ I.a I.next /
              ((1 + yConst limbs) * (1 + yConst limbs ^ 2)) /
            claimScale 0 (22 + 2 + 1 + 1) I.t ∧
        mle cQ (sumPoint (22 + 2) (yConst limbs)) =
          (params hF σ).target ![I.s 0, I.s 1, I.s 2, I.s 3, 1, 0, 0, 0] I.γ /
            ((1 + yConst limbs) * (1 + yConst limbs ^ 2)))) ↔
      ((∀ i : Fin (22 + 2 + 1 + 1), 1 + SQ^[(i : ℕ)] I.t ≠ 0) ∧
        (wire hF σ idx).verifyWith (m := Id) H π = true) := by
  intro I
  rw [verifyWith_iff, hg, hR]
  have hs : decodeStmt (limbs := limbs) π.stmt = ![I.s 0, I.s 1, I.s 2, I.s 3, 1, 0, 0, 0] := by
    funext k; fin_cases k <;> rfl
  rw [hs, ← proofVals_a hF σ H idx π]
  exact run_accepts_iff hF σ H idx π.stmt (H (encW hF σ π.g)) (H (encQ hF σ π.R)) (π.v.1 0)
    (π.v.1 1) (π.v.1 2) (π.v.1 3) π.v.2 hfr cW cF hcF cQ

end Implementation
