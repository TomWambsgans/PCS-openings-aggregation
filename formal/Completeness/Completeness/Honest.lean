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

end Completeness
