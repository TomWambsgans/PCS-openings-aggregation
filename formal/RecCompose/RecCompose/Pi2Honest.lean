-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The tables' model is `Tables.lean`'s (`pi2Model`,
-- `claim_wFold`, `claim_quotient`, `claim_sum`, `claim_setup`), the verifier's arithmetic `formal/RecStatement`'s
-- (`checks_claims_iff_post2`).
import RecCompose.Pi2HonestQ

/-!
# π2's honest prover: its claims hold and the verifier's check passes, off the bad challenges

**`pi2_honest`**: at a setup of the real deployment's circuit (the compiled circuit `C.G roots`, its facts `Fa`, the setup
columns `hcol`), for a witness `w` satisfying the circuit at the public limbs of the scalars, the honest prover's stacks
(`honestW`: `W`'s placed table; `honestQ`: `h`'s and `q`'s novel coefficients placed) and the honest inputs of the
verifier's arithmetic (`honestInputs`: the true fold values at `t`, `ξ = κ(t) + β σ(t)` from the setup's halves, any
`ρ`): **the verifier's one check passes and π2's four claims hold on the stacks** (`Pi2ClaimsHold`), unless

* **`BadCopy`** (`α, β, γ`): a pulled `d_pull(i) = α + w_i + β ω_i`, a `d_push(i) = α + P_i + β ω_{σ_i}` or a public
  `d_pub(j) = α + F_j + β ω_{N+j}` is zero;
* **`BadT`** (`t`): `t ∈ V_{m+2}` (`w_{m+2}(t) = 0`) or `c_h + c_q = d_pull(t) d_push(t) + Z_V(t) = 0`.

The proof: the model's polynomials of the honest stacks are the prover's (`modelW_eq`, `modelSigma_eq`,
`modelKappa_eq`, `modelH_eq`, `modelQ_eq`: by the stacks' placement and interpolation on `V_m`), `q` the honest one
(`novP_qNovel`), so the identity is zero; `Σ_V h` is the target (`sum_hValues`); `ξ` is the setup's claim
(`xiOf_eq`); the fold values are `W`'s true ones; so `RecPiop.Post2` holds, and `checks_claims_iff_post2` with the
model's claims (`claims_of_model`) gives the claims.

**Counting** (`card_badCopy_le`, `card_badT_le`): at most `(2N + n_P) |E|²` triples `(α, β, γ)` are bad (each
denominator is zero on `|E|²` of them, `α` being determined by `β, γ`), and for a good triple at most `8N` points `t`
(`V_{m+2}`'s `4N`, and the roots of `d_pull d_push + Z_V`, a nonzero polynomial of degree below `4N`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

/-! ## The honest objects -/

/-- **The honest `W` stack**: the witness's basis-`B` coefficients placed under `W`'s layout (the prover's `wStack`). -/
def honestW (G : RecPiop.Circuit E) (w : ℕ → K) : Stk :=
  fun j ↦ (placePublic (layoutsOf G.logN).1 fun i ↦ (wTableB G w).getD i 0).getD j 0

/-- **The honest `Q` stack**: `h`'s and `q`'s novel coefficients placed under `Q`'s layout (the prover's `qStack`). -/
def honestQ (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ : E) : Stk :=
  fun j ↦ (placePublic (layoutsOf G.logN).2.1 (qEntry G.logN (hNovel G w α β γ) (qNovel G w α β γ))).getD j 0

/-- **The honest inputs** of the verifier's arithmetic: the scalars, the challenges, the true fold values at `t` and
`ξ` from the setup's halves (the prover's `inputs`). -/
def honestInputs (G : RecPiop.Circuit E) (setupStack : Array K) (w : ℕ → K) (scalars : List E)
    (α β γ t ρ : E) : Inputs E :=
  ⟨scalars, α, β, γ, t, foldValues G.logN G.logW (wTableB G w) t, xiOf G.logN setupStack β t, ρ⟩

/-- **The witness's polynomial** (degree below `N`): its novel coefficients'. -/
noncomputable def witnessPoly (G : RecPiop.Circuit E) (w : ℕ → K) : E[X] :=
  UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesK G.logN (wValues G w)).getD j 0

/-- `σ`'s and `κ`'s polynomials (degree below `N`). -/
noncomputable def sigmaPoly (G : RecPiop.Circuit E) : E[X] :=
  UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (sigmaValues G)).getD j 0

noncomputable def kappaPoly (G : RecPiop.Circuit E) : E[X] :=
  UniComplete.AlgC.novP G.logN fun j ↦ (UniComplete.novelOfValuesE G.logN (kappaValues G)).getD j 0

/-- **The copy argument's bad challenges**: a pulled `d_pull`, a `d_push` on `V_m` or a public `d_pub` zero. -/
def BadCopy (G : RecPiop.Circuit E) (w : ℕ → K) (pub : ℕ → List E) (α β γ : E) : Prop :=
  (∃ i < G.N, ¬ G.IsHole i ∧ RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i = 0) ∨
    (∃ i < G.N, G.dPush pi2Omega (RecCircuit.emb w) α β γ i = 0) ∨
      (∃ j < G.nP, G.dPub pi2Omega pub α β γ j = 0)

/-- **The bad points `t`**: `t ∈ V_{m+2}`, or `c_h + c_q = d_pull(t) d_push(t) + Z_V(t)` zero. -/
def BadT (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ t : E) : Prop :=
  QuotientSecurity.sq^[G.logN + 2] t = 0 ∨
    (RecPiop.dPullP (witnessPoly G w) α β *
        (C α + G.pushPoly pi2Omega (kappaPoly G) (witnessPoly G w) γ + C β * sigmaPoly G) +
      G.zV pi2Omega).eval t = 0

/-! ## Facts of the honest objects -/

theorem size_wValues (G : RecPiop.Circuit E) (w : ℕ → K) : (wValues G w).size = 2 ^ G.logN := by
  simp [wValues, RecPiop.Circuit.N]

theorem witnessPoly_omega (G : RecPiop.Circuit E) (w : ℕ → K) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (witnessPoly G w).eval (pi2Omega i) = RecCircuit.emb w i := by
  unfold witnessPoly
  rw [novP_valuesK_omega hm _ (size_wValues G w) hi]
  unfold wValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]
  rfl

theorem sigmaPoly_omega (G : RecPiop.Circuit E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (sigmaPoly G).eval (pi2Omega i) = pi2Omega (G.sigma i) := by
  unfold sigmaPoly
  rw [novP_values_omega hm _ (by simp [sigmaValues, RecPiop.Circuit.N]) hi]
  unfold sigmaValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]
  rw [pi2Omega_eq]

theorem kappaPoly_omega (G : RecPiop.Circuit E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (kappaPoly G).eval (pi2Omega i) = G.kappa i := by
  unfold kappaPoly
  rw [novP_values_omega hm _ (by simp [kappaValues, RecPiop.Circuit.N]) hi]
  unfold kappaValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show i < G.N from hi, dite_true, Option.getD_some]

theorem hNovel_omega (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ : E) (hm : G.logN ≤ 28) {i : ℕ} (hi : i < G.N) :
    (UniComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β γ).getD j 0).eval (pi2Omega i) =
      (hValues G w α β γ).getD i 0 :=
  novP_values_omega hm _ (size_hValues w α β γ) hi

/-! ## The stacks read back -/

theorem layoutW_eq {m : ℕ} (hm : 20 ≤ m) :
    (layoutsOf m).1 = PcsQuotient.Layout.ofChunks m m (max m minCertifiedStack) [(0, 2 ^ m)] := by
  simp only [layoutsOf, certifiedFrom, hm, ite_true]

theorem layoutQ_eq {m : ℕ} (hm : 20 ≤ m) :
    (layoutsOf m).2.1 = PcsQuotient.Layout.ofChunks (m + 5) m (max (m + 4) minCertifiedStack) (quotientChunks m) := by
  simp only [layoutsOf, certifiedFrom, hm, ite_true]

/-- **`W`'s layout reads back the honest table.** -/
theorem readW_honest (G : RecPiop.Circuit E) (w : ℕ → K) (hm : 20 ≤ G.logN) {i : ℕ} (hi : i < 2 ^ G.logN) :
    (layoutsOf G.logN).1.readEntry (honestW G w) i = (wTableB G w).getD i 0 := by
  unfold honestW
  rw [layoutW_eq hm]
  refine readEntry_placePublic _ (placePublic_logPiece _ _ _ _) _ i (block_mem_ofChunks
    (by simp only [minCertifiedStack, PcsQuotient.laneFold]; omega) (List.mem_singleton_self _)
    (Nat.div_eq_of_lt hi))

theorem mem_quotientChunks_h {m l : ℕ} (hl : l < 3) : (8 * l, 2 ^ m) ∈ quotientChunks m := by
  unfold quotientChunks
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons]
  exact ⟨l, hl, Or.inl rfl⟩

theorem mem_quotientChunks_q {m l d : ℕ} (hl : l < 3) (hd : d < 4) : (8 * l + 4 + d, 2 ^ m) ∈ quotientChunks m := by
  unfold quotientChunks
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map]
  exact ⟨l, hl, Or.inr ⟨d, hd, rfl⟩⟩

/-- **`Q`'s layout reads back the honest table** at a listed chunk. -/
theorem readQ_honest (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ : E) (hm : 20 ≤ G.logN) {c i : ℕ}
    (hc : (c, 2 ^ G.logN) ∈ quotientChunks G.logN) (hi : i / 2 ^ G.logN = c) :
    (layoutsOf G.logN).2.1.readEntry (honestQ G w α β γ) i =
      qEntry G.logN (hNovel G w α β γ) (qNovel G w α β γ) i := by
  unfold honestQ
  rw [layoutQ_eq hm]
  exact readEntry_placePublic _ (placePublic_logPiece _ _ _ _) _ i (block_mem_ofChunks
    (by simp only [minCertifiedStack, PcsQuotient.laneFold]; omega) hc hi)

theorem qEntry_at (m : ℕ) (hN qN : Array E) {pd kind l : ℕ} (hpd : pd < 2 ^ (m + 2)) (hk : kind < 2) :
    qEntry m hN qN (pd + 2 ^ (m + 2) * (kind + 2 * l)) =
      if kind = 0 then (if pd < 2 ^ m then limbN (hN.getD pd 0) l else 0) else limbN (qN.getD pd 0) l := by
  unfold qEntry
  have h1 : (pd + 2 ^ (m + 2) * (kind + 2 * l)) % 2 ^ (m + 2) = pd := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpd]
  have h2 : (pd + 2 ^ (m + 2) * (kind + 2 * l)) / 2 ^ (m + 2) = kind + 2 * l := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hpd, zero_add]
  have h3 : (kind + 2 * l) / 2 = l := by omega
  have h4 : (kind + 2 * l) % 2 = kind := by omega
  simp only [h1, h2, h3, h4]

theorem yE_eq : yE = Primitives.F192.Y := rfl

theorem limbN_zero (x : E) : limbN x 0 = x.limb 0 := rfl
theorem limbN_one (x : E) : limbN x 1 = x.limb 1 := rfl
theorem limbN_two (x : E) : limbN x 2 = x.limb 2 := rfl

/-- **An element of `E` from its limbs**: `Σ_l Y^l c_l`. -/
theorem limbs_sum_eq (x : E) : ∑ l ∈ range 3, yE ^ l * ofK (limbN x l) = x := by
  have hk : ∀ a : K, ofK a = Primitives.F192.ofF64 a := fun _ ↦ rfl
  have hl : ∀ i, x.limb i = Primitives.F192.limb x i := fun _ ↦ rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, limbN_zero, limbN_one, limbN_two, hk, hl]
  conv_rhs => rw [← Primitives.F192.ofLimbs_limb x, Primitives.F192.ofLimbs_eq]
  rw [yE_eq]
  ring

/-- **`h`'s coefficient read back from the honest `Q`** (`pd < N`). -/
theorem qCoef_honest_h (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ : E) (hm : 20 ≤ G.logN) {pd : ℕ}
    (hpd : pd < 2 ^ G.logN) :
    qCoef (qTable G.logN (honestQ G w α β γ)) G.logN 0 pd = (hNovel G w α β γ).getD pd 0 := by
  have hpd' : pd < 2 ^ (G.logN + 2) := lt_of_lt_of_le hpd (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold qCoef qTable
  conv_rhs => rw [← limbs_sum_eq ((hNovel G w α β γ).getD pd 0)]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := mem_range.mp hl
  rw [readQ_honest G w α β γ hm (mem_quotientChunks_h hl') (by rw [chunk_of, Nat.div_eq_of_lt hpd]; ring),
    qEntry_at _ _ _ hpd' (by norm_num)]
  simp [hpd]

/-- **`q`'s coefficient read back from the honest `Q`** (`pd < 4N`). -/
theorem qCoef_honest_q (G : RecPiop.Circuit E) (w : ℕ → K) (α β γ : E) (hm : 20 ≤ G.logN) {pd : ℕ}
    (hpd : pd < 2 ^ (G.logN + 2)) :
    qCoef (qTable G.logN (honestQ G w α β γ)) G.logN 1 pd = (qNovel G w α β γ).getD pd 0 := by
  have hd : pd / 2 ^ G.logN < 4 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [pow_add] at hpd
    omega
  unfold qCoef qTable
  conv_rhs => rw [← limbs_sum_eq ((qNovel G w α β γ).getD pd 0)]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := mem_range.mp hl
  rw [readQ_honest G w α β γ hm (mem_quotientChunks_q (d := pd / 2 ^ G.logN) hl' hd)
      (by rw [chunk_of]; ring),
    qEntry_at _ _ _ hpd (by norm_num)]
  simp

end RecCompose

/-- info: 'RecCompose.qCoef_honest_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.qCoef_honest_q

/-- info: 'RecCompose.readW_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.readW_honest
