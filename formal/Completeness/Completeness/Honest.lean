-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Completeness.Tables
import Completeness.Reduction
import Completeness.Circuit

/-!
# The honest prover's messages, as the tables it commits

On F1's instance over a field `F` with the base field `K` (a `LimbSystem`: `F = K + K Y + K Y^2`)
and a Cantor basis in `K` (`hB`: the deployed `beta()` is `F64`'s), the honest prover of
`prove_with_randomness`:

* **the witness table** (`witnessTable`, `m + 1 = 25` variables over `K`): the table whose
  polynomial takes the cells' values at the cells (`cellTable`, `domain::coefficients` of the
  cells), then the masks at entries `2^24 + 4 i + j` (`mask[4 i + j] = masks[j][i]`); its first
  message is `witnessOfTable` of it, whose cells are the assignment's whatever the masks
  (`cellsOf_honest`) and whose row polynomials have degree at most `2^22 + 2`;
* **the wiring table** (`wiringTableK`): the setup's, over `K`, whose polynomial is the wiring
  polynomial (`sigmaPoly_eq`);
* **the second message** is F1's `Params.honest`; its gate quotient is the image of a polynomial
  over `K` (`qGate_mem_lifts`), and the three quotients have the degrees the quotient table's
  chunks hold (`honest_degrees`): `h` below `2^24`, `q` at most `3 · 2^24 + 9249` (the chunks hold
  `3 · 2^24 + 9280`), the gate's at most `7 · 2^22 + 22` (`7 · 2^22 + 64`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Completeness

open QuotientSecurity

/-! ## The instance's parameters, field by field (stated generically, so nothing is unfolded) -/

section OfCantor

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] {N n : ℕ} (B : CantorBasis F N)
  (hm : n + 2 ≤ N) (σ : Equiv.Perm (Fin (n + 2) → Bool)) (words : ℕ)
  (wordSum : Fin words → ((Fin (n + 2) → Bool) → F) →ₗ[F] F) (pub : F → F[X])
  (hPub : ∀ (γ : F) (w : (Fin (n + 2) → Bool) → F),
    ∑ x, (pub γ).eval (B.point x) * w x = ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J w)

theorem ofCantor_sigmaPoly :
    (Params.ofCantor B hm σ words wordSum pub hPub).sigmaPoly = tablePoly (wiringTable B hm σ) :=
  rfl

theorem ofCantor_θ : (Params.ofCantor B hm σ words wordSum pub hPub).θ = B.β 1 := rfl

theorem ofCantor_vRows :
    (Params.ofCantor B hm σ words wordSum pub hPub).vRows = ∏ x : cantorT B n, (X - C (x : F)) :=
  rfl

end OfCantor

variable {K F : Type} [Field K] [CharP K 2] [Field F] [DecidableEq F] [CharP F 2]

namespace Instance'

variable (I : Instance F)

theorem sigmaPoly_eq : I.params.sigmaPoly = tablePoly (wiringTable I.basis le24 I.wiring) :=
  ofCantor_sigmaPoly I.basis le24 I.wiring 8 _ _ I.pub_hPub

theorem θ_eq : I.params.θ = I.basis.β 1 := ofCantor_θ I.basis le24 I.wiring 8 _ _ I.pub_hPub

theorem vRows_eq : I.params.vRows = ∏ x : cantorT I.basis 22, (X - C (x : F)) :=
  ofCantor_vRows I.basis le24 I.wiring 8 _ _ I.pub_hPub

end Instance'

/-! ## A basis in the base field -/

section Basis

variable (ι : K →+* F)

/-- The points of a basis in `K`, read in `F`. -/
theorem point_map {m : ℕ} (BK : CantorBasis K (22 + 2)) (B : CantorBasis F (22 + 2))
    (hB : ∀ k, B.β k = ι (BK.β k)) (x : Fin m → Bool) : B.point x = ι (BK.point x) := by
  unfold CantorBasis.point
  rw [map_sum]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [hB]

/-- A table over `K` whose polynomial takes given values at the basis's points (`exists_table`
over `K`). -/
noncomputable def tableOf {m : ℕ} (BK : CantorBasis K (22 + 2)) (hm : m ≤ 22 + 2)
    (f : (Fin m → Bool) → K) : (Fin m → Bool) → K :=
  (BK.exists_table hm f).choose

theorem tableOf_eval {m : ℕ} (BK : CantorBasis K (22 + 2)) (hm : m ≤ 22 + 2)
    (f : (Fin m → Bool) → K) (x : Fin m → Bool) :
    (tablePoly (tableOf BK hm f)).eval (BK.point x) = f x :=
  (BK.exists_table hm f).choose_spec x

/-- Read in `F`, at the points of the basis read in `F`. -/
theorem tableOf_eval_map {m : ℕ} (BK : CantorBasis K (22 + 2)) (B : CantorBasis F (22 + 2))
    (hB : ∀ k, B.β k = ι (BK.β k)) (hm : m ≤ 22 + 2) (f : (Fin m → Bool) → K)
    (x : Fin m → Bool) :
    (tablePoly fun b => ι (tableOf BK hm f b)).eval (B.point x) = ι (f x) := by
  rw [tablePoly_map, point_map ι BK B hB, eval_map, eval₂_at_apply, tableOf_eval]

end Basis

/-! ## The witness table -/

/-- `idx` of a first coordinate. -/
theorem idx_cons {M : ℕ} (x : Bool) (b : Fin M → Bool) :
    idx (Fin.cons x b : Fin (M + 1) → Bool) = (if x then 1 else 0) + 2 * idx b := by
  unfold idx
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, Fin.val_succ, pow_succ,
    mul_sum]
  congr 1
  exact sum_congr rfl fun k _ => by split_ifs <;> ring

/-- **A table vanishing from index `D` on holds a polynomial of degree below `D`.** -/
theorem natDegree_tablePoly_lt_of_support {R : Type*} [Field R] [CharP R 2] {M D : ℕ}
    (c : (Fin M → Bool) → R) (hD : 0 < D) (hc : ∀ b, D ≤ idx b → c b = 0) :
    (tablePoly c).natDegree < D := by
  refine lt_of_le_of_lt (b := D - 1) ?_ (by omega)
  unfold tablePoly
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  by_cases hb : D ≤ idx b
  · rw [hc b hb]; simp
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  have : ∑ k : Fin M, (if b k then (digitPoly (k : ℕ) : R[X]) else 1).natDegree = idx b := by
    unfold idx
    refine sum_congr rfl fun k _ => ?_
    split_ifs
    · exact (digitPoly_monic_natDegree (F := R) k).2
    · simp
  omega

/-- A row polynomial of the first message a table holds: its two first coordinates are the
role's bits. -/
theorem witnessOfTable_apply {R : Type*} [Field R] {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → R)
    (j : Fin 4) :
    witnessOfTable c j = tablePoly fun b => c (Fin.cons (roleBit0 j) (Fin.cons (roleBit1 j) b)) := by
  fin_cases j <;> rfl

/-- The masks' table on `24` digits: entry `4 i + j` is coefficient `i` of mask `j` (`i < 3`). -/
def maskTable (m : Fin 4 → Fin 3 → K) : (Fin (22 + 2) → Bool) → K := fun b =>
  if h : idx b < 12 then m ⟨idx b % 4, Nat.mod_lt _ (by norm_num)⟩ ⟨idx b / 4, by omega⟩ else 0

/-- **The witness table** (`witness_layout`, `m + 1 = 25` variables): the cells' table, then the
masks. -/
noncomputable def witnessTable (BK : CantorBasis K (22 + 2)) (f : (Fin (22 + 2) → Bool) → K)
    (m : Fin 4 → Fin 3 → K) : (Fin (22 + 2 + 1) → Bool) → K :=
  joinTable (tableOf BK le_rfl f) (maskTable m)

theorem joinTable_snoc {M : ℕ} (c₀ c₁ : (Fin M → Bool) → K) (b : Fin M → Bool) (x : Bool) :
    joinTable c₀ c₁ (Fin.snoc b x) = if x then c₁ b else c₀ b := by
  simp [joinTable, Fin.init_snoc]

/-- **The witness table vanishes off its chunks**: below `2^24` (the cells) or at `2^24 + j`,
`j < 12` (the masks). -/
theorem witnessTable_support (BK : CantorBasis K (22 + 2)) (f : (Fin (22 + 2) → Bool) → K)
    (m : Fin 4 → Fin 3 → K) (b : Fin (22 + 2 + 1) → Bool) (hb : witnessTable BK f m b ≠ 0) :
    idx b < 2 ^ 24 ∨ (2 ^ 24 ≤ idx b ∧ idx b < 2 ^ 24 + 12) := by
  have e : b = Fin.snoc (Fin.init b) (b (Fin.last _)) := (Fin.snoc_init_self b).symm
  have hlt := idx_lt (Fin.init b)
  rw [e, idx_snoc]
  unfold witnessTable at hb
  rw [e, joinTable_snoc] at hb
  split_ifs at hb ⊢ with hl
  · right
    unfold maskTable at hb
    split_ifs at hb with h12
    · omega
    · exact absurd rfl hb
  · left
    simpa using hlt

variable (ι : K →+* F) (I : Instance F) (BK : CantorBasis K (22 + 2))
  (hB : ∀ k, I.basis.β k = ι (BK.β k))

include hB in
/-- **The honest first message's cells are the values the table was built from**, read in `F`,
whatever the masks. -/
theorem cellsOf_honest (f : (Fin (22 + 2) → Bool) → K) (m : Fin 4 → Fin 3 → K)
    (x : Fin (22 + 2) → Bool) :
    I.cellsOf (witnessOfTable fun b => ι (witnessTable BK f m b)) x = ι (f x) := by
  rw [cellsOf_witnessTable]
  have : (fun b : Fin (22 + 2) → Bool => ι (witnessTable BK f m (Fin.snoc b false))) =
      fun b => ι (tableOf BK le_rfl f b) := funext fun b => by
    unfold witnessTable
    rw [joinTable_snoc]
    rfl
  rw [this, tableOf_eval_map ι BK I.basis hB]

/-- **The honest row polynomials have degree at most `2^22 + 2`**: each is a quarter of the
witness table, whose entries past `2^22 + 2` (`2^24 + 12` in the table) are zero. -/
theorem natDegree_witnessOfTable_le (f : (Fin (22 + 2) → Bool) → K) (m : Fin 4 → Fin 3 → K)
    (j : Fin 4) :
    ((witnessOfTable fun b => ι (witnessTable BK f m b)) j).natDegree ≤ 2 ^ 22 + 2 := by
  have key : ∀ x y : Bool,
      (tablePoly fun b : Fin (22 + 1) → Bool =>
        ι (witnessTable BK f m (Fin.cons x (Fin.cons y b)))).natDegree ≤ 2 ^ 22 + 2 := by
    intro x y
    have := natDegree_tablePoly_lt_of_support (D := 2 ^ 22 + 3)
      (fun b : Fin (22 + 1) → Bool => ι (witnessTable BK f m (Fin.cons x (Fin.cons y b))))
      (by positivity) fun b hb => by
        by_contra hne
        have hne' : witnessTable BK f m (Fin.cons x (Fin.cons y b)) ≠ 0 := fun h => hne (by
          simp only [h, map_zero])
        have hs := witnessTable_support BK f m _ hne'
        rw [idx_cons, idx_cons] at hs
        split_ifs at hs <;> omega
    omega
  rw [witnessOfTable_apply]
  exact key _ _

/-! ## The wiring table -/

/-- **The setup's wiring table** over `K`: its polynomial sends each cell's point to its
successor's (`Index::new`). -/
noncomputable def wiringTableK (σ : Equiv.Perm (Fin (22 + 2) → Bool)) : (Fin (22 + 2) → Bool) → K :=
  tableOf BK le_rfl fun x => BK.point (σ x)

include hB in
/-- **The wiring polynomial is the setup's table's.** -/
theorem sigmaPoly_eq_wiringTableK :
    I.params.sigmaPoly = tablePoly fun b => ι (wiringTableK BK I.wiring b) := by
  rw [Instance'.sigmaPoly_eq]
  refine I.basis.tablePoly_ext le24 _ _ fun x => ?_
  rw [wiringTable_eval, wiringTableK, tableOf_eval_map ι BK I.basis hB, point_map ι BK I.basis hB]

/-! ## The second message's degrees -/

/-- **The honest quotients' degrees**: for a first message of degree at most `2^22 + 2`, `h`
below `2^24`, `q` at most `3 · 2^24 + 9249`, the gate's at most `7 · 2^22 + 22` (the
computation of `Instance.honest_legal`, with its exact numbers). -/
theorem honest_degrees (g : Fin 4 → F[X]) (hg : ∀ j, (g j).natDegree ≤ 2 ^ 22 + 2) (α β γ : F) :
    (Params.honest I.params g α β γ).h₀.natDegree < 2 ^ 24 ∧
      (Params.honest I.params g α β γ).q.natDegree ≤ 3 * 2 ^ 24 + 9249 ∧
      (Params.honest I.params g α β γ).qGate.natDegree ≤ 7 * 2 ^ 22 + 22 := by
  classical
  let B' : I.params.Bounds := { I.bounds with witness := 2 ^ 22 + 2 }
  let gm : B'.Msg₁ := ⟨g, hg⟩
  have hcell : ∀ c, (Params.cellPoly I.params g c).natDegree ≤ 16777227 := fun c =>
    (Params.natDegree_cellPoly_le B' gm c).trans (by
      show 3 + (2 ^ 22 + 2) * 4 ≤ 16777227
      norm_num)
  have hgate : (Params.gatePoly I.params g).natDegree ≤ 33554454 :=
    (Params.natDegree_gatePoly_le B' gm).trans (by
      show 2 * (3 + (2 ^ 22 + 2) * 4) ≤ 33554454
      norm_num)
  have hσ : I.params.sigmaPoly.natDegree ≤ 16777216 := I.bounds.hSigma.trans (by
    show 2 ^ (22 + 2) ≤ 16777216
    norm_num)
  have hpub : (I.params.pub γ).natDegree ≤ 16786432 := (I.bounds.hPub γ).trans (by
    show 2 ^ 24 + 9 * 2 ^ 10 ≤ 16786432
    norm_num)
  have hE := I.exact
  have hcmon : I.params.vCells.Monic := (digitPoly_monic_natDegree (22 + 2)).1
  have hcdeg : I.params.vCells.natDegree = 16777216 :=
    (digitPoly_monic_natDegree (F := F) (22 + 2)).2.trans (by norm_num)
  have hrmon : I.params.vRows.Monic := by
    rw [hE.rows]; exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hrdeg : I.params.vRows.natDegree = 4194304 := by
    rw [hE.rows, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    exact (card_cantorT (n := 22) I.basis le24).trans (by norm_num)
  have hdl : (Lagrange.interpolate Finset.univ I.params.pt
      (Params.sumValue I.params g α β γ)).degree < 16777216 := by
    refine lt_of_lt_of_eq (Lagrange.degree_interpolate_lt _ I.params.pt_injective.injOn) ?_
    rw [Finset.card_univ]
    exact_mod_cast I.nCells.trans (by norm_num)
  have hh : (Lagrange.interpolate Finset.univ I.params.pt
      (Params.sumValue I.params g α β γ)).natDegree ≤ 16777216 :=
    natDegree_le_of_degree_le hdl.le
  have hall := Params.natDegree_honest_le I.params g α β γ 16777227 16786432 16777216 hcell hσ
    hpub hcmon hcdeg (by norm_num) (by norm_num) hh
  refine ⟨?_, hall.1.trans (by norm_num), ?_⟩
  · show (Lagrange.interpolate Finset.univ I.params.pt
      (Params.sumValue I.params g α β γ)).natDegree < 2 ^ 24
    by_cases h0 : Lagrange.interpolate Finset.univ I.params.pt
        (Params.sumValue I.params g α β γ) = 0
    · rw [h0, natDegree_zero]; positivity
    · rw [natDegree_lt_iff_degree_lt h0]
      exact lt_of_lt_of_eq hdl (by norm_num)
  · refine (Params.natDegree_honest_qGate_le I.params g α β γ hrmon).trans ?_
    rw [hrdeg]
    exact (Nat.sub_le_sub_right hgate _).trans (by norm_num)

/-! ## The gate's quotient is over `K` -/

theorem lifts_comp {p q : F[X]} (hp : p ∈ lifts ι) (hq : q ∈ lifts ι) : p.comp q ∈ lifts ι := by
  obtain ⟨pK, rfl⟩ := (lifts_iff_set_range p).mp hp
  obtain ⟨qK, rfl⟩ := (lifts_iff_set_range q).mp hq
  exact (lifts_iff_set_range _).mpr ⟨pK.comp qK, Polynomial.map_comp ι pK qK⟩

theorem digit_mem_lifts (j : Fin 4) : (digit j : F[X]) ∈ lifts ι := by
  have hX : (X : F[X]) ∈ lifts ι := X_mem_lifts ι
  fin_cases j
  · exact Subsemiring.one_mem _
  · exact hX
  · exact Subsemiring.add_mem _ (Subsemiring.pow_mem _ hX 2) hX
  · exact Subsemiring.mul_mem _ (Subsemiring.add_mem _ (Subsemiring.pow_mem _ hX 2) hX) hX

theorem rowPoly_mem_lifts : (rowPoly : F[X]) ∈ lifts ι :=
  Subsemiring.add_mem _ (Subsemiring.pow_mem _ (X_mem_lifts ι) 4) (X_mem_lifts ι)

include hB in
theorem shift_mem_range (c : Fin 4) : shift I.params.θ c ∈ Set.range ι := by
  rw [Instance'.θ_eq, hB]
  fin_cases c
  · exact ⟨0, map_zero ι⟩
  · exact ⟨1, map_one ι⟩
  · exact ⟨BK.β 1, rfl⟩
  · exact ⟨BK.β 1 + 1, by simp [shift]⟩

include hB in
theorem cellPoly_mem_lifts (g : Fin 4 → F[X]) (hg : ∀ j, g j ∈ lifts ι) (c : Fin 4) :
    Params.cellPoly I.params g c ∈ lifts ι := by
  unfold Params.cellPoly
  refine Subsemiring.sum_mem _ fun j _ => Subsemiring.mul_mem _ ?_ ?_
  · refine lifts_comp ι (digit_mem_lifts ι j) (Subsemiring.add_mem _ (X_mem_lifts ι) ?_)
    obtain ⟨a, ha⟩ := shift_mem_range ι I BK hB c
    rw [← ha]
    exact C_mem_lifts ι a
  · exact lifts_comp ι (hg j) (rowPoly_mem_lifts ι)

include hB in
theorem vRows_mem_lifts : I.params.vRows ∈ lifts ι := by
  rw [Instance'.vRows_eq]
  refine Subsemiring.prod_mem _ fun x _ => ?_
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp x.2
  rw [← hy, point_map ι BK I.basis hB]
  exact (lifts_iff_set_range _).mpr ⟨X - C (BK.point (cellBits (y, 0))), by simp⟩

theorem honest_qGate (g : Fin 4 → F[X]) (α β γ : F) :
    (Params.honest I.params g α β γ).qGate = Params.gatePoly I.params g / I.params.vRows := rfl

include hB in
/-- **The honest gate quotient is over `K`**: the gate's polynomial and the rows' vanishing
polynomial are, and so is their quotient. -/
theorem qGate_mem_lifts (g : Fin 4 → F[X]) (hg : ∀ j, g j ∈ lifts ι) (α β γ : F) :
    (Params.honest I.params g α β γ).qGate ∈ lifts ι := by
  rw [honest_qGate]
  have hgate : Params.gatePoly I.params g ∈ lifts ι := by
    unfold Params.gatePoly gate
    have h := fun c => cellPoly_mem_lifts ι I BK hB g hg c
    exact Subsemiring.add_mem _ (Subsemiring.add_mem _ (Subsemiring.add_mem _ (h 3) (h 0)) (h 2))
      (Subsemiring.mul_mem _ (h 1) (h 2))
  obtain ⟨gK, hgK⟩ := (lifts_iff_set_range _).mp hgate
  obtain ⟨vK, hvK⟩ := (lifts_iff_set_range _).mp (vRows_mem_lifts ι I BK hB)
  rw [← hgK, ← hvK, ← Polynomial.map_div]
  exact (lifts_iff_set_range _).mpr ⟨gK / vK, rfl⟩

include hB in
/-- The honest first message is over `K`. -/
theorem witnessOfTable_mem_lifts {k : ℕ} (c : (Fin (k + 1 + 1) → Bool) → K) (j : Fin 4) :
    witnessOfTable (fun b => ι (c b)) j ∈ lifts ι := by
  rw [witnessOfTable_apply, tablePoly_map]
  exact (lifts_iff_set_range _).mpr ⟨_, rfl⟩

/-! ## The second message as a table -/

/-- `Accepts` reads the second message only through `h`, `q`, the gate's quotient, `junk` at `t`
and the sum over the cells. -/
theorem accepts_congr (P : Params F) {stmt : Fin P.words → F} {g : Params.Witness F}
    {R R' : Params.Quotients F} {α β γ t ρ s : F} {a : Fin 4 → F}
    (hh : R.h P = R'.h P) (hq : R.q = R'.q) (hg : R.qGate = R'.qGate) (hj : R.junk = R'.junk)
    (ht : R.top P = R'.top P) :
    P.Accepts stmt g R α β γ t a s ρ ↔ P.Accepts stmt g R' α β γ t a s ρ := by
  unfold Params.Accepts
  rw [hh, hq, hg, hj, ht]

/-! ## The quotient table -/

section Helpers

variable {K' : Type} [Field K'] [CharP K' 2]

open Classical in
/-- A table of a polynomial of degree below `D ≤ 2^M` vanishing from `D` on
(`exists_table_support`), or zero if there is none. -/
noncomputable def tableSupp (M : ℕ) (pK : K'[X]) (D : ℕ) : (Fin M → Bool) → K' :=
  if h : D ≤ 2 ^ M ∧ (pK = 0 ∨ pK.natDegree < D) then (exists_table_support M pK D h.1 h.2).choose
  else fun _ => 0

theorem tableSupp_spec {M D : ℕ} {pK : K'[X]} (hD : D ≤ 2 ^ M) (hp : pK = 0 ∨ pK.natDegree < D) :
    tablePoly (tableSupp M pK D) = pK := by
  unfold tableSupp
  rw [dif_pos ⟨hD, hp⟩]
  exact (exists_table_support M pK D hD hp).choose_spec.1

theorem tableSupp_support {M D : ℕ} (pK : K'[X]) (b : Fin M → Bool) (hb : D ≤ idx b) :
    tableSupp M pK D b = 0 := by
  unfold tableSupp
  split_ifs with h
  · exact (exists_table_support M pK D h.1 h.2).choose_spec.2 b hb
  · rfl

/-- Four tables on `M` digits as one on `M + 2`, the two new digits last. -/
def quad {M : ℕ} (f : Bool → Bool → (Fin M → Bool) → K') : (Fin (M + 1 + 1) → Bool) → K' :=
  joinTable (joinTable (f false false) (f true false)) (joinTable (f false true) (f true true))

theorem quad_snoc {M : ℕ} (f : Bool → Bool → (Fin M → Bool) → K') (b : Fin M → Bool)
    (x y : Bool) : quad f (Fin.snoc (Fin.snoc b x) y) = f x y b := by
  unfold quad
  rw [joinTable_snoc]
  cases y <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [joinTable_snoc] <;> cases x <;> rfl

theorem idx_quad_snoc {M : ℕ} (b : Fin M → Bool) (x y : Bool) :
    idx (Fin.snoc (Fin.snoc b x) y : Fin (M + 1 + 1) → Bool) =
      idx b + 2 ^ M * ((if x then 1 else 0) + 2 * if y then 1 else 0) := by
  rw [idx_snoc, idx_snoc, pow_succ]
  split_ifs <;> ring

theorem exists_snoc_snoc {M : ℕ} (b : Fin (M + 1 + 1) → Bool) :
    ∃ (c : Fin M → Bool) (x y : Bool), b = Fin.snoc (Fin.snoc c x) y :=
  ⟨Fin.init (Fin.init b), Fin.init b (Fin.last M), b (Fin.last (M + 1)), by
    rw [Fin.snoc_init_self, Fin.snoc_init_self]⟩

end Helpers

variable (S : LimbSystem K F)

/-- The four limbs of a polynomial over `F` (the fourth zero). -/
noncomputable def limb4 (p : F[X]) (e : Fin 4) : K[X] :=
  if h : (e : ℕ) < 3 then S.limbPoly p ⟨e, h⟩ else 0

/-- **The degree each slot of the quotient table holds** (`quotient_chunks`, in entries of the
slot's `2^26`): `h` one chunk, `q` three and `Q_SPILL = 9280`, the gate's quotient `(2 - 1/4)`
chunks and `64`, the fourth slot nothing. -/
def slotBound : Bool → Bool → ℕ
  | false, false => 2 ^ 24
  | true, false => 3 * 2 ^ 24 + 9280
  | false, true => 7 * 2 ^ 22 + 64
  | true, true => 0

/-- The limbs a slot holds: `h` and `q` three, the gate's quotient (over `K`) one. -/
def slotLive : Bool → Bool → Fin 4 → Bool
  | false, false, e => decide ((e : ℕ) < 3)
  | true, false, e => decide ((e : ℕ) < 3)
  | false, true, e => decide ((e : ℕ) = 0)
  | true, true, _ => false

/-- The polynomials over `K` the slots' limbs hold. -/
noncomputable def slotPolyK (R : Params.Quotients F) (qGateK : K[X]) :
    Bool → Bool → Fin 4 → K[X]
  | false, false, e => limb4 S R.h₀ e
  | true, false, e => limb4 S R.q e
  | false, true, _ => qGateK
  | true, true, _ => 0

/-- A slot's limb table, on `M` digits (`26` on the instance). -/
noncomputable def slotTable (M : ℕ) (R : Params.Quotients F) (qGateK : K[X]) (κ τ : Bool)
    (e : Fin 4) : (Fin M → Bool) → K :=
  if slotLive κ τ e then tableSupp M (slotPolyK S R qGateK κ τ e) (slotBound κ τ) else fun _ => 0

/-- The limb of two coordinates: `e₀ + 2 e₁`. -/
def limbIdx (e₀ e₁ : Bool) : Fin 4 :=
  ⟨(if e₀ then 1 else 0) + 2 * (if e₁ then 1 else 0), by split_ifs <;> norm_num⟩

theorem limbIdx_ff : limbIdx false false = 0 := by decide
theorem limbIdx_tf : limbIdx true false = 1 := by decide
theorem limbIdx_ft : limbIdx false true = 2 := by decide
theorem limbIdx_tt : limbIdx true true = 3 := by decide

/-- **The quotient table** (`quotient_layout`, `M + 4 = 30` variables over `K` on the instance):
coordinates below `M = 26` a slot's polynomial's coefficients, then two for the slot (`h`, `q`, the
gate's quotient, nothing), then two for the limb. Stated for any `M`, so the proofs below never
see the instance's sizes. -/
noncomputable def quotientTable (M : ℕ) (R : Params.Quotients F) (qGateK : K[X]) :
    (Fin (M + 1 + 1 + 1 + 1) → Bool) → K :=
  quad fun e₀ e₁ => quad fun κ τ => slotTable S M R qGateK κ τ (limbIdx e₀ e₁)

theorem subTable_quotientTable (M : ℕ) (R : Params.Quotients F) (qGateK : K[X])
    (κ τ e₀ e₁ : Bool) :
    subTable (fun b => S.ι (quotientTable S M R qGateK b)) κ τ e₀ e₁ =
      fun b => S.ι (slotTable S M R qGateK κ τ (limbIdx e₀ e₁) b) := by
  funext b
  unfold subTable quotientTable
  dsimp only
  rw [quad_snoc, quad_snoc]

theorem tablePoly_slotTable (M : ℕ) (R : Params.Quotients F) (qGateK : K[X]) (κ τ : Bool)
    (e : Fin 4) (hdeg : (slotPolyK S R qGateK κ τ e).natDegree < slotBound κ τ)
    (hB : slotBound κ τ ≤ 2 ^ M) :
    tablePoly (fun b => S.ι (slotTable S M R qGateK κ τ e b)) =
      if slotLive κ τ e then (slotPolyK S R qGateK κ τ e).map S.ι else 0 := by
  unfold slotTable
  split_ifs
  · rw [tablePoly_map, tableSupp_spec hB (Or.inr hdeg)]
  · simp only [map_zero]
    exact tablePoly_zero

/-- `slotPoly`, unfolded. -/
theorem slotPoly_eq {R2 : Type*} [Field R2] {k : ℕ} (Y : R2)
    (c : (Fin (k + 1 + 1 + 1 + 1) → Bool) → R2) (κ τ : Bool) :
    slotPoly Y c κ τ = tablePoly (subTable c κ τ false false)
      + C Y * tablePoly (subTable c κ τ true false)
      + C (Y ^ 2) * tablePoly (subTable c κ τ false true)
      + C (Y ^ 3) * tablePoly (subTable c κ τ true true) := rfl

/-- The four limb terms of a slot. -/
theorem slotPoly_quotientTable (M : ℕ) (R : Params.Quotients F) (qGateK : K[X]) (κ τ : Bool)
    (hdeg : ∀ e, (slotPolyK S R qGateK κ τ e).natDegree < slotBound κ τ)
    (hB : slotBound κ τ ≤ 2 ^ M) :
    slotPoly S.Y (fun b => S.ι (quotientTable S M R qGateK b)) κ τ =
      (if slotLive κ τ 0 then (slotPolyK S R qGateK κ τ 0).map S.ι else 0)
        + C S.Y * (if slotLive κ τ 1 then (slotPolyK S R qGateK κ τ 1).map S.ι else 0)
        + C (S.Y ^ 2) * (if slotLive κ τ 2 then (slotPolyK S R qGateK κ τ 2).map S.ι else 0)
        + C (S.Y ^ 3) * (if slotLive κ τ 3 then (slotPolyK S R qGateK κ τ 3).map S.ι else 0) := by
  rw [slotPoly_eq]
  simp only [subTable_quotientTable, limbIdx_ff, limbIdx_tf, limbIdx_ft, limbIdx_tt]
  rw [tablePoly_slotTable S M R qGateK κ τ _ (hdeg _) hB,
    tablePoly_slotTable S M R qGateK κ τ _ (hdeg _) hB,
    tablePoly_slotTable S M R qGateK κ τ _ (hdeg _) hB,
    tablePoly_slotTable S M R qGateK κ τ _ (hdeg _) hB]

/-- A slot holding a polynomial in three limbs holds it. -/
theorem slotPoly_three (p : F[X]) :
    (if (0 : ℕ) < 3 then (limb4 S p 0).map S.ι else 0)
        + C S.Y * (if (1 : ℕ) < 3 then (limb4 S p 1).map S.ι else 0)
        + C (S.Y ^ 2) * (if (2 : ℕ) < 3 then (limb4 S p 2).map S.ι else 0)
        + C (S.Y ^ 3) * (if (3 : ℕ) < 3 then (limb4 S p 3).map S.ι else 0) = p := by
  conv_rhs => rw [← S.sum_limbPoly p]
  rw [Fin.sum_univ_three]
  simp [limb4]

end Completeness
