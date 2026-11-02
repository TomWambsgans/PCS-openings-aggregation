-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Heap.Cantor
import Bridge.Claims.Constants

/-!
# The heap at the deployed Cantor basis

The univariate crate computes its basis as `crates/quotient/src/domain.rs` does
(`crates/leanvm_univariate/src/domain.rs`: `beta[0] = 1`, `beta[k + 1]` the solution of
`s(x) = beta[k]` with its low bit clear, in leanVM 42422001's `K`, which is leanerVM's
`LeanVM.Parameters.K`); the statement's `PcsQuotient.Domain.betaAt` is that computation, and
`Bridge.isCantor_statementConsts` proves its first `24` vectors a Cantor basis (by
`QuotientSecurity.deployedBasis`'s kernel-checked words). Nothing is evaluated here: `basis n`
is that basis, cut to `n ≤ 24` vectors and read in `E`, and the generic lemmas of `Heap.Cantor`
apply to it at every such `n`, among them the reference workload's heap of depth `23`
(`root_eq_prod_leaves`). A heap deeper than `24` needs more vectors proved Cantor (the statement
computes `28`, and the Rust `32`).
-/

namespace Heap.Deployed

open Finset QuotientSecurity LeanVM.Parameters

/-- A Cantor basis of `m` vectors, cut to its first `n ≤ m`. -/
def restrict {F : Type*} [Field F] {m : ℕ} (B : CantorBasis F m) (n : ℕ) (h : n ≤ m) :
    CantorBasis F n :=
  ⟨B.β, B.zero, fun k hk ↦ B.succ k (by omega)⟩

/-- **The deployed Cantor basis of `K`**: `betaAt`'s first `n ≤ 24` vectors. -/
def basisK (n : ℕ) (h : n ≤ 24) : CantorBasis K n :=
  restrict (Compose.basisK Bridge.statementConsts Bridge.isCantor_statementConsts) n h

/-- **The deployed Cantor basis, in `E`**: `ofK` of `betaAt`'s first `n ≤ 24` vectors. -/
def basis (n : ℕ) (h : n ≤ 24) : CantorBasis E n :=
  restrict (Compose.basisE Bridge.statementConsts Bridge.isCantor_statementConsts) n h

theorem basisK_β (n : ℕ) (h : n ≤ 24) (k : ℕ) :
    (basisK n h).β k = PcsQuotient.Domain.betaAt k := rfl

theorem basis_β (n : ℕ) (h : n ≤ 24) (k : ℕ) :
    (basis n h).β k = ofK (PcsQuotient.Domain.betaAt k) := rfl

/-- The heap's points are points of `K`: `ω_i` in `E` is `ofK` of `ω_i` in `K` (the crate's
`point_e`). -/
theorem omega_basis (n : ℕ) (h : n ≤ 24) (i : ℕ) :
    omega (basis n h) i = ofK (omega (basisK n h) i) := by
  unfold omega
  rw [show ofK (∑ k ∈ range n, if i.testBit k then (basisK n h).β k else 0) =
      algebraMap K E (∑ k ∈ range n, if i.testBit k then (basisK n h).β k else 0) from rfl,
    map_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  split_ifs
  · rfl
  · exact (map_zero (algebraMap K E)).symm

/-- **The tree lemma at the deployed basis**, at every depth `1 ≤ n ≤ 24`: if
`T(s(x)) = T(x)·T(x + 1)` on `V_n \ V_1`, then `T(1)` is the product of `T` on the leaves. -/
theorem root_eq_prod_leaves {M : Type*} [CommMonoid M] {n : ℕ} (h1 : 1 ≤ n) (h : n ≤ 24)
    {T : E → M}
    (htree : ∀ x ∈ V (basis n h) n, x ∉ V (basis n h) 1 →
      T (QuotientSecurity.sq x) = T x * T (x + 1)) :
    T 1 = ∏ i ∈ Ico (2 ^ (n - 1)) (2 ^ n), T (omega (basis n h) i) :=
  root_eq_prod_leaves_omega (basis n h) h1 htree

/-- The reference workload's heap (`2^23` positions, SPEC §5.2), by application. -/
example {T : E → E}
    (htree : ∀ x ∈ V (basis 23 (by norm_num)) 23, x ∉ V (basis 23 (by norm_num)) 1 →
      T (QuotientSecurity.sq x) = T x * T (x + 1)) :
    T 1 = ∏ i ∈ Ico (2 ^ 22) (2 ^ 23), T (omega (basis 23 (by norm_num)) i) :=
  root_eq_prod_leaves (by norm_num) (by norm_num) htree

end Heap.Deployed
