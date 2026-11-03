-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecPiop.Identity

/-!
# `Z_V` is the digit `w_m`

The identity's vanishing polynomial `Z_V = Π_{i<N} (X + ω_i)` (`Circuit.zV`) is what the verifier
evaluates as the digit `w_m(t) = s^m(t)` (`PI2.md` §2 step 1, `c_q = w_m`): on a Cantor basis of
at least `m` vectors, `Z_V` is `QuotientSecurity.digitPoly m` (`zV_eq_digitPoly`), both monic of
degree `2^m`, the digit vanishing at every `ω_i` (`Heap.sq_iterate_omega`), so
`Z_V(t) = w_m(t)` (`zV_eval_eq`).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial QuotientSecurity

variable {F : Type} [Field F] [CharP F 2]

/-- **The digit polynomial `s^k` is monic of degree `2^k`.** -/
theorem digitPoly_monic : ∀ k : ℕ, (digitPoly k : F[X]).Monic ∧ (digitPoly k : F[X]).natDegree = 2 ^ k
  | 0 => ⟨monic_X, by simp [digitPoly]⟩
  | k + 1 => by
    obtain ⟨hm, hd⟩ := digitPoly_monic k
    have hq : ((X : F[X]) ^ 2 + X).Monic := by
      refine Monic.add_of_left (monic_X_pow 2) ?_
      rw [degree_X, degree_X_pow]
      exact_mod_cast (by norm_num : (1 : ℕ) < 2)
    have hqd : ((X : F[X]) ^ 2 + X).natDegree = 2 := by
      rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X, degree_X_pow]; exact_mod_cast
        (by norm_num : (1 : ℕ) < 2)), natDegree_X_pow]
    have h0 : (digitPoly k : F[X]).natDegree ≠ 0 := by rw [hd]; exact (Nat.two_pow_pos k).ne'
    refine ⟨hq.comp hm h0, ?_⟩
    show ((X ^ 2 + X).comp (digitPoly k)).natDegree = 2 ^ (k + 1)
    rw [natDegree_comp, hqd, hd, pow_succ, mul_comm]

namespace Circuit

variable [DecidableEq F] (G : Circuit F)

theorem zV_monic (ω : ℕ → F) : (G.zV ω).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_add_C (ω i)

theorem natDegree_zV (ω : ℕ → F) : (G.zV ω).natDegree = G.N := by
  unfold zV
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C (ω i)]
  simp

/-- **`Z_V` is the digit `w_m`**, on a Cantor basis of at least `m` vectors. -/
theorem zV_eq_digitPoly {n : ℕ} (B : CantorBasis F n) (hn : G.logN ≤ n) :
    G.zV (Heap.omega B) = digitPoly G.logN := by
  obtain ⟨hdm, hdd⟩ := digitPoly_monic (F := F) G.logN
  have hN : G.N ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hroot : ∀ i < G.N, (digitPoly G.logN : F[X]).eval (Heap.omega B i) = 0 := by
    intro i hi
    rw [digitPoly_eval, Heap.sq_iterate_omega B G.logN (by omega),
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (show i < 2 ^ G.logN from hi), Heap.omega_zero]
  have hdvd : G.zV (Heap.omega B) ∣ digitPoly G.logN := by
    have e : G.zV (Heap.omega B) =
        (((range G.N).val.map (Heap.omega B)).map fun a => X - C a).prod := by
      unfold zV
      rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply, sub_eq_add_neg, CharTwo.neg_eq]
    rw [e, Multiset.prod_X_sub_C_dvd_iff_le_roots hdm.ne_zero]
    have hnd : ((range G.N).val.map (Heap.omega B)).Nodup := by
      refine Multiset.Nodup.map_on (fun a ha b hb h => ?_) (range G.N).nodup
      rw [Finset.mem_val, Finset.mem_range] at ha hb
      exact Heap.omega_injOn B (by omega) (by omega) h
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    rw [mem_roots hdm.ne_zero, IsRoot.def]
    exact hroot i (Finset.mem_range.mp hi)
  exact (eq_of_monic_of_dvd_of_natDegree_le (G.zV_monic _) hdm hdvd
    (by rw [hdd, natDegree_zV]; exact le_refl _)).symm

/-- **`Z_V(t) = w_m(t)`**: the verifier's `c_q`. -/
theorem zV_eval_eq {n : ℕ} (B : CantorBasis F n) (hn : G.logN ≤ n) (t : F) :
    (G.zV (Heap.omega B)).eval t = sq^[G.logN] t := by
  rw [zV_eq_digitPoly G B hn, digitPoly_eval]

end Circuit

end RecPiop
