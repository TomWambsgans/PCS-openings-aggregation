-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The degree bookkeeping follows
-- `formal/QuotientSecurity/Degrees.lean` (crates/quotient's two identities).
import RecPiop.Indicator
import RecPiop.Copy

/-!
# π2's quotient identity and its degrees

`PI2.md` §1, SPEC-REC.md §2.3: with `w` the witness's polynomial (degree below `N`, its values on
`V_m` the witness), the **push polynomial**

`P = w + Σ_p I_p·(E_p + w) + κ`,

`E_p` pair `p`'s formula on the row's cells `w(X + ω_{k ⊕ c})` (`cellPoly`; `ω_{k ⊕ c}` moves role
`k`'s position to cell `c` of its row, `cellPoly_eval`), takes the push values on `V_m`
(`pushPoly_eval`: the pairs cover each non-forward once, and in characteristic two
`w + (E + w) = E`); `1_S = Σ_{port pairs} I_p` is the holes' indicator there (`holePoly_eval`).
The **identity** (`idPoly`)

`h·d_pull·d_push + (1 + 1_S)·d_push + d_pull + q·Z_V`, `d_pull = α + w + βX`,
`d_push = α + P + βσ`, `Z_V = Π_{i<N} (X + ω_i)`,

evaluates on `V_m` to the copy argument's pointwise identity (`idPoly_eval_omega`), so if it is
the zero polynomial and `Σ_V h` is the target, the state `CopyOK` holds (`copyOK_of_idPoly`).

**The degrees** (`natDegree_idPoly_le`): with `w, σ, κ, h` below `N` and `q` below `4N`, the
indicators are at most `N − 2^s` (`natDegree_ind_le`), the formulas at most `2(N − 1)`, so
`P` and `d_push` at most `3(N − 1) < 3N` (`natDegree_pushPoly_le`), `1_S` below `N`, and the identity
at most `5N − 1`. **Schwartz–Zippel in `t`** (`card_idPoly_eval_eq_zero_le`): a nonzero identity
vanishes at at most `5N − 1` points `t`, so the identity at a random `t` is the identity on `V_m`
but with probability `(5N − 1)/|F|`.

The setup's polynomials `σ`, `κ` (`SetupPolys`) are any of degree below `N` taking the columns'
values on `V_m` (`SetupPolys.ofInterpolate` builds them by interpolation).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial

variable {F : Type} [Field F] [CharP F 2]

/-! ## Formulas on polynomials -/

theorem Poly2.eval_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) (p : Poly2 F) (cell : ℕ → R) : φ (p.eval cell) = p.eval (φ ∘ cell) := by
  unfold Poly2.eval
  simp only [map_add, map_list_sum, List.map_map]
  congr 2
  · refine List.map_congr_left fun t _ => ?_
    simp [map_mul, AlgHom.commutes]
  · refine List.map_congr_left fun t _ => ?_
    simp [map_mul, AlgHom.commutes]

theorem fpEval_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) (ls : List (Limb F)) (γ : F) (cell : ℕ → R) :
    φ (fpEval ls γ cell) = fpEval ls γ (φ ∘ cell) := by
  unfold fpEval
  simp only [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp [map_mul, AlgHom.commutes]

theorem Role.value_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) (r : Role F) (γ : F) (own : R) (cell : ℕ → R) :
    φ (r.value γ own cell) = r.value γ (φ own) (φ ∘ cell) := by
  cases r with
  | forward => rfl
  | expr p => exact Poly2.eval_map φ p cell
  | port ls => exact fpEval_map φ ls γ cell

/-- **A role's formula on polynomials, evaluated, is the formula on the values.** -/
theorem Role.value_eval (r : Role F) (γ : F) (own : F[X]) (cell : ℕ → F[X]) (x : F) :
    (r.value γ own cell).eval x = r.value γ (own.eval x) (fun c => (cell c).eval x) := by
  have h := Role.value_map (aeval x) r γ own cell
  simp only [coe_aeval_eq_eval] at h
  exact h

theorem natDegree_list_sum_le {l : List F[X]} {D : ℕ} (h : ∀ p ∈ l, p.natDegree ≤ D) :
    l.sum.natDegree ≤ D := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons]
    exact natDegree_add_le_of_degree_le (h a (List.mem_cons_self ..))
      (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem Poly2.natDegree_eval_le (p : Poly2 F) {cell : ℕ → F[X]} {D : ℕ}
    (h : ∀ c, (cell c).natDegree ≤ D) : (p.eval cell).natDegree ≤ 2 * D := by
  unfold Poly2.eval
  refine natDegree_add_le_of_degree_le (natDegree_list_sum_le fun q hq => ?_)
    (natDegree_list_sum_le fun q hq => ?_)
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
    rw [Polynomial.algebraMap_eq]
    exact (natDegree_C_mul_le _ _).trans ((h _).trans (by omega))
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
    rw [Polynomial.algebraMap_eq]
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have := h t.1
    have := h t.2.1
    omega

theorem fpEval_natDegree_le (ls : List (Limb F)) (γ : F) {cell : ℕ → F[X]} {D : ℕ}
    (h : ∀ c, (cell c).natDegree ≤ D) : (fpEval ls γ cell).natDegree ≤ D := by
  unfold fpEval
  refine natDegree_list_sum_le fun q hq => ?_
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hq
  rw [Polynomial.algebraMap_eq]
  exact (natDegree_C_mul_le _ _).trans (h _)

theorem Role.natDegree_value_le (r : Role F) (γ : F) {own : F[X]} {cell : ℕ → F[X]} {D : ℕ}
    (ho : own.natDegree ≤ D) (h : ∀ c, (cell c).natDegree ≤ D) :
    (r.value γ own cell).natDegree ≤ 2 * D := by
  cases r with
  | forward => exact ho.trans (by omega)
  | expr p => exact Poly2.natDegree_eval_le p h
  | port ls => exact (fpEval_natDegree_le ls γ h).trans (by omega)

/-! ## The polynomials of the identity -/

/-- **A cell of a role-`k` position's row**, as a polynomial: `w(X + ω_{k ⊕ c})`. -/
noncomputable def cellPoly (ω : ℕ → F) (wP : F[X]) (k c : ℕ) : F[X] :=
  wP.comp (X + C (ω (k ^^^ c)))

/-- **The pull's denominator** `α + w + βX`. -/
noncomputable def dPullP (wP : F[X]) (α β : F) : F[X] := C α + wP + C β * X

/-- **The setup's polynomials**: `σ` (the tags) and `κ` (the constants), of degree below `N`,
taking the columns' values on `V_m`. -/
structure SetupPolys (G : Circuit F) (ω : ℕ → F) where
  σP : F[X]
  κP : F[X]
  σ_deg : σP.natDegree < G.N
  κ_deg : κP.natDegree < G.N
  σ_eval : ∀ i < G.N, σP.eval (ω i) = ω (G.sigma i)
  κ_eval : ∀ i < G.N, κP.eval (ω i) = G.kappa i

theorem natDegree_lt_of_degree_lt' {p : F[X]} {m : ℕ} (h : p.degree < m) (hm : 0 < m) :
    p.natDegree < m := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero]; exact hm
  · exact (natDegree_lt_iff_degree_lt hp).mpr h

/-- **The setup's polynomials exist**: `σ` and `κ` by interpolation on `V_m`. -/
noncomputable def SetupPolys.ofInterpolate (G : Circuit F) {ω : ℕ → F} {n : ℕ} (hP : Points ω n)
    (hn : G.logN ≤ n) : SetupPolys G ω :=
  have hinj : Set.InjOn ω (range G.N : Set ℕ) := fun a ha b hb h => by
    have hN : G.N ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    exact hP.inj a (by omega) b (by omega) h
  have hN : 0 < G.N := Nat.two_pow_pos _
  { σP := Lagrange.interpolate (range G.N) ω (fun i => ω (G.sigma i))
    κP := Lagrange.interpolate (range G.N) ω G.kappa
    σ_deg := natDegree_lt_of_degree_lt' (by
      simpa using Lagrange.degree_interpolate_lt (fun i => ω (G.sigma i)) hinj) hN
    κ_deg := natDegree_lt_of_degree_lt' (by
      simpa using Lagrange.degree_interpolate_lt G.kappa hinj) hN
    σ_eval := fun i hi => Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_range.mpr hi)
    κ_eval := fun i hi => Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_range.mpr hi) }

namespace Circuit

variable (G : Circuit F) [DecidableEq F] (ω : ℕ → F)

/-- **Pair `p`'s formula** `E_p` on the row's cells, a polynomial. -/
noncomputable def formulaPoly (wP : F[X]) (γ : F) (p : Block × ℕ) : F[X] :=
  (G.regionRole p.1 p.2).value γ wP (cellPoly ω wP p.2)

/-- **The push polynomial** `P = w + Σ_p I_p·(E_p + w) + κ`. -/
noncomputable def pushPoly (κP wP : F[X]) (γ : F) : F[X] :=
  wP + ∑ p ∈ G.pairs, G.ind ω p * (G.formulaPoly ω wP γ p + wP) + κP

/-- **The holes' indicator** `1_S`: the port pairs' indicators. -/
noncomputable def holePoly : F[X] :=
  ∑ p ∈ G.pairs.filter (fun p => (G.regionRole p.1 p.2).isPort = true), G.ind ω p

/-- **`V_m`'s vanishing polynomial** `Z_V = Π_{i<N} (X + ω_i)`. -/
noncomputable def zV : F[X] := ∏ i ∈ range G.N, (X + C (ω i))

/-- **The push's denominator** `α + P + βσ`. -/
noncomputable def dPushP (S : SetupPolys G ω) (wP : F[X]) (α β γ : F) : F[X] :=
  C α + G.pushPoly ω S.κP wP γ + C β * S.σP

/-- **The identity**
`h·d_pull·d_push + (1 + 1_S)·d_push + d_pull + q·Z_V`, zero on `V_m` but for `q·Z_V`. -/
noncomputable def idPoly (S : SetupPolys G ω) (wP hP qP : F[X]) (α β γ : F) : F[X] :=
  hP * dPullP wP α β * G.dPushP ω S wP α β γ + (1 + G.holePoly ω) * G.dPushP ω S wP α β γ +
    dPullP wP α β + qP * G.zV ω

variable {G ω} {n : ℕ}

/-! ## On `V_m` -/

/-- **A row's cell from a role-`k` position**: `i ⊕ (k ⊕ c)` is cell `c` of `i`'s row. -/
theorem xor_role (i : ℕ) {c : ℕ} (hc : c < G.W) : i ^^^ ((i % G.W) ^^^ c) = G.base i + c := by
  have hdvd : 2 ^ G.logW ∣ G.base i := Dvd.intro_left _ rfl
  have hk : i % G.W < 2 ^ G.logW := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hi : G.base i ^^^ (i % G.W) = i := by
    rw [← Heap.add_eq_xor_of_dvd hdvd hk]
    exact Nat.div_add_mod' i G.W
  rw [Heap.add_eq_xor_of_dvd hdvd hc]
  calc i ^^^ ((i % G.W) ^^^ c) = (G.base i ^^^ (i % G.W)) ^^^ ((i % G.W) ^^^ c) := by rw [hi]
    _ = G.base i ^^^ c := by
      rw [Nat.xor_assoc, ← Nat.xor_assoc (i % G.W), Nat.xor_self, Nat.zero_xor]

theorem cellPoly_eval (hP : Points ω n) (wP : F[X]) (i : ℕ) {c : ℕ} (hc : c < G.W) :
    (cellPoly ω wP (i % G.W) c).eval (ω i) = wP.eval (ω (G.base i + c)) := by
  unfold cellPoly
  rw [eval_comp, eval_add, eval_X, eval_C, ← hP.xor, xor_role i hc]

theorem formulaPoly_eval (hV : G.Valid) (hP : Points ω n) (wP : F[X]) (γ : F)
    {p : Block × ℕ} (hp : p ∈ G.pairs) {i : ℕ} (hi : G.InPair p i) :
    (G.formulaPoly ω wP γ p).eval (ω i) =
      (G.role i).value γ (wP.eval (ω i)) (fun c => wP.eval (ω (G.base i + c))) := by
  unfold formulaPoly
  rw [Role.value_eval, ← role_of_inPair hV hp hi]
  refine Role.value_congr _ γ (fun _ => rfl) fun c hc => ?_
  rw [← hi.2.2]
  exact cellPoly_eval hP wP i (role_reads_lt hV hc)

/-- **The push polynomial takes the pushes on `V_m`.** -/
theorem pushPoly_eval (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (κP wP : F[X])
    (hκ : ∀ i < G.N, κP.eval (ω i) = G.kappa i) (γ : F) {i : ℕ} (hi : i < G.N) :
    (G.pushPoly ω κP wP γ).eval (ω i) = G.push (fun j => wP.eval (ω j)) γ i := by
  unfold pushPoly push
  rw [eval_add, eval_add, eval_finsetSum, hκ i hi]
  cases hf : (G.role i).isForward with
  | true =>
    have hs : ∑ p ∈ G.pairs, (G.ind ω p * (G.formulaPoly ω wP γ p + wP)).eval (ω i) = 0 :=
      Finset.sum_eq_zero fun p hp => by
        rw [eval_mul, ind_eval_not_mem hi (not_inPair_of_forward hV hp hf), zero_mul]
    rw [hs, add_zero]
    cases hr : G.role i with
    | forward => rfl
    | expr _ => rw [hr] at hf; simp [Role.isForward] at hf
    | port _ => rw [hr] at hf; simp [Role.isForward] at hf
  | false =>
    obtain ⟨p₀, hp₀, hi₀⟩ := exists_pair hi hf
    rw [Finset.sum_eq_single p₀ (fun p hp hne => by
        rw [eval_mul, ind_eval_not_mem hi (fun h => hne (pair_unique hV hp hp₀ h hi₀)), zero_mul])
      (fun h => absurd hp₀ h)]
    rw [eval_mul, ind_eval_mem hV hP hn hp₀ hi₀, one_mul, eval_add, formulaPoly_eval hV hP wP γ hp₀ hi₀]
    have e : ∀ a b : F, a + (b + a) = b := fun a b => by
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [e]

/-- **The holes' polynomial is the holes' indicator on `V_m`.** -/
theorem holePoly_eval (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) {i : ℕ} (hi : i < G.N) :
    (G.holePoly ω).eval (ω i) = G.holeInd i := by
  unfold holePoly holeInd
  rw [eval_finsetSum]
  by_cases hh' : G.IsHole i
  · have hh : (G.role i).isPort = true := hh'
    have hf : (G.role i).isForward = false := by
      cases hr : G.role i <;> rw [hr] at hh <;> simp_all [Role.isForward, Role.isPort]
    obtain ⟨p₀, hp₀, hi₀⟩ := exists_pair hi hf
    have hm : p₀ ∈ G.pairs.filter (fun p => (G.regionRole p.1 p.2).isPort = true) :=
      Finset.mem_filter.mpr ⟨hp₀, by rw [← role_of_inPair hV hp₀ hi₀]; exact hh⟩
    rw [Finset.sum_eq_single p₀ (fun p hp hne => ind_eval_not_mem hi
        (fun h => hne (pair_unique hV (Finset.mem_filter.mp hp).1 hp₀ h hi₀)))
      (fun h => absurd hm h), ind_eval_mem hV hP hn hp₀ hi₀, ite_eq_left hh']
  · rw [ite_eq_right hh']
    refine Finset.sum_eq_zero fun p hp => ind_eval_not_mem hi fun h => hh' ?_
    show (G.role i).isPort = true
    rw [role_of_inPair hV (Finset.mem_filter.mp hp).1 h]
    exact (Finset.mem_filter.mp hp).2

theorem zV_eval {i : ℕ} (hi : i < G.N) : (G.zV ω).eval (ω i) = 0 := by
  unfold zV
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) (by simp [CharTwo.add_self_eq_zero])

theorem dPullP_eval (wP : F[X]) (α β : F) (i : ℕ) :
    (dPullP wP α β).eval (ω i) = dPull ω (fun j => wP.eval (ω j)) α β i := by
  simp [dPullP, dPull, den]

theorem dPushP_eval (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (S : SetupPolys G ω)
    (wP : F[X]) (α β γ : F) {i : ℕ} (hi : i < G.N) :
    (G.dPushP ω S wP α β γ).eval (ω i) = G.dPush ω (fun j => wP.eval (ω j)) α β γ i := by
  unfold dPushP dPush den
  rw [eval_add, eval_add, eval_mul, eval_C, eval_C, pushPoly_eval hV hP hn S.κP wP S.κ_eval γ hi,
    S.σ_eval i hi]

/-- **The identity on `V_m` is the copy argument's pointwise identity**, with `h_i = h(ω_i)`. -/
theorem idPoly_eval_omega (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n)
    (S : SetupPolys G ω) (wP hP' qP : F[X]) (α β γ : F) {i : ℕ} (hi : i < G.N) :
    (G.idPoly ω S wP hP' qP α β γ).eval (ω i) =
      hP'.eval (ω i) * dPull ω (fun j => wP.eval (ω j)) α β i *
          G.dPush ω (fun j => wP.eval (ω j)) α β γ i +
        (1 + G.holeInd i) * G.dPush ω (fun j => wP.eval (ω j)) α β γ i +
          dPull ω (fun j => wP.eval (ω j)) α β i := by
  unfold idPoly
  rw [eval_add, eval_add, eval_add, eval_mul, eval_mul, eval_mul, eval_mul, eval_add, eval_one,
    zV_eval hi, mul_zero, add_zero, dPullP_eval, dPushP_eval hV hP hn S wP α β γ hi,
    holePoly_eval hV hP hn hi]

/-- **The identity as a polynomial gives the state after `α, β, γ`**: if it is zero, and `Σ_V h`
is the target with the public denominators nonzero, `CopyOK` holds of the witness `w(ω_i)`. -/
theorem copyOK_of_idPoly (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (S : SetupPolys G ω)
    (pub : ℕ → List F) (wP hP' qP : F[X]) (α β γ : F) (hid : G.idPoly ω S wP hP' qP α β γ = 0)
    (hsum : ∑ i ∈ range G.N, hP'.eval (ω i) = G.target ω pub α β γ)
    (hpub : ∀ j < G.nP, G.dPub ω pub α β γ j ≠ 0) :
    G.CopyOK ω pub (fun j => wP.eval (ω j)) α β γ :=
  ⟨hpub, ⟨fun i => hP'.eval (ω i), fun i hi => by
    unfold PointId
    rw [← idPoly_eval_omega hV hP hn S wP hP' qP α β γ hi, hid, eval_zero], hsum⟩⟩

/-! ## The degrees -/

theorem natDegree_cellPoly_le (wP : F[X]) (k c : ℕ) : (cellPoly ω wP k c).natDegree ≤ wP.natDegree := by
  unfold cellPoly
  refine natDegree_comp_le.trans ?_
  rw [natDegree_X_add_C, mul_one]

theorem N_ge_two (hV : G.Valid) : 2 ≤ G.N := by
  unfold N
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ G.logN := Nat.pow_le_pow_right (by norm_num) (by have := hV.logW_lt; omega)

/-- **The push polynomial has degree below `3N`**: `3(N − 1)`. -/
theorem natDegree_pushPoly_le (hV : G.Valid) {κP wP : F[X]} (hκ : κP.natDegree < G.N)
    (hw : wP.natDegree < G.N) (γ : F) : (G.pushPoly ω κP wP γ).natDegree ≤ 3 * (G.N - 1) := by
  have hw' : wP.natDegree ≤ G.N - 1 := by omega
  unfold pushPoly
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by omega) ?_) (by omega)
  refine natDegree_sum_le_of_forall_le _ _ fun p hp => ?_
  refine natDegree_mul_le_of_le (natDegree_ind_le' hV hp)
    (natDegree_add_le_of_degree_le (n := 2 * (G.N - 1)) ?_ (by omega)) |>.trans (by omega)
  exact Role.natDegree_value_le _ γ hw' fun c => (natDegree_cellPoly_le wP _ c).trans hw'

theorem natDegree_holePoly_le (hV : G.Valid) : (G.holePoly ω).natDegree ≤ G.N - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun _ hp => natDegree_ind_le' hV (Finset.mem_filter.mp hp).1

theorem natDegree_zV_le : (G.zV ω).natDegree ≤ G.N := by
  unfold zV
  refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
  simp

theorem natDegree_dPullP_le {wP : F[X]} {D : ℕ} (hw : wP.natDegree ≤ D) (hD : 1 ≤ D) (α β : F) :
    (dPullP wP α β).natDegree ≤ D := by
  unfold dPullP
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ hw) ?_
  · rw [natDegree_C]; exact Nat.zero_le _
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans hD)

theorem natDegree_dPushP_le (hV : G.Valid) (S : SetupPolys G ω) {wP : F[X]}
    (hw : wP.natDegree < G.N) (α β γ : F) :
    (G.dPushP ω S wP α β γ).natDegree ≤ 3 * (G.N - 1) := by
  have := S.σ_deg
  unfold dPushP
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_
    (natDegree_pushPoly_le hV S.κ_deg hw γ)) ?_
  · rw [natDegree_C]; exact Nat.zero_le _
  · exact (natDegree_C_mul_le _ _).trans (by omega)

/-- **The identity has degree at most `5N − 1`**, for `w, σ, κ, h` below `N` and `q` below `4N`
(`q·Z_V` dominates; `h·d_pull·d_push` is at most `5(N − 1)`, `(1 + 1_S)·d_push` at most
`4(N − 1)`). -/
theorem natDegree_idPoly_le (hV : G.Valid) (S : SetupPolys G ω) {wP hP qP : F[X]}
    (hw : wP.natDegree < G.N) (hh : hP.natDegree < G.N) (hq : qP.natDegree < 4 * G.N)
    (α β γ : F) : (G.idPoly ω S wP hP qP α β γ).natDegree ≤ 5 * G.N - 1 := by
  have h2 := N_ge_two hV
  have hpull := natDegree_dPullP_le (D := G.N - 1) (by omega) (by omega) α β (wP := wP)
  have hpush := natDegree_dPushP_le hV S hw α β γ
  have hhole := natDegree_holePoly_le hV (ω := ω)
  have hz := natDegree_zV_le (G := G) (ω := ω)
  have h1 : (1 + G.holePoly ω).natDegree ≤ G.N - 1 :=
    natDegree_add_le_of_degree_le (by rw [natDegree_one]; exact Nat.zero_le _) hhole
  have hA := natDegree_mul_le_of_le (natDegree_mul_le_of_le hh.le hpull) hpush
  have hB := natDegree_mul_le_of_le h1 hpush
  have hD := natDegree_mul_le_of_le (Nat.le_sub_one_of_lt hq) hz
  unfold idPoly
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (hA.trans ?_) (hB.trans ?_)) (hpull.trans ?_)) (hD.trans ?_) <;>
  · generalize G.N = N at *
    omega

/-! ## Schwartz–Zippel in `t` -/

/-- A nonzero polynomial vanishes at at most its degree's number of points. -/
theorem card_eval_eq_zero_le [Fintype F] (p : F[X]) (hp : p ≠ 0) :
    (univ.filter fun t => p.eval t = 0).card ≤ p.natDegree := by
  refine (Finset.card_le_card fun t ht => ?_).trans ((Multiset.toFinset_card_le _).trans
    (card_roots' p))
  rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
  exact (Finset.mem_filter.mp ht).2

/-- **The identity at a random point**: a nonzero identity vanishes at at most `5N − 1` points
`t`. -/
theorem card_idPoly_eval_eq_zero_le [Fintype F] (hV : G.Valid) (S : SetupPolys G ω)
    {wP hP qP : F[X]} (hw : wP.natDegree < G.N) (hh : hP.natDegree < G.N)
    (hq : qP.natDegree < 4 * G.N) (α β γ : F) (hne : G.idPoly ω S wP hP qP α β γ ≠ 0) :
    (univ.filter fun t => (G.idPoly ω S wP hP qP α β γ).eval t = 0).card ≤ 5 * G.N - 1 :=
  (card_eval_eq_zero_le _ hne).trans (natDegree_idPoly_le hV S hw hh hq α β γ)

end Circuit

end RecPiop
