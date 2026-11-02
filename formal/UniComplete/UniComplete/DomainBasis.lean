-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniStatement.Domain
import PcsQuotient.Domain
import Heap.Cantor

/-!
# The univariate verifier's Cantor basis, as words (milestone 4, the domain facts)

`UniStatement.beta` (`formal/UniStatement/UniStatement/Domain.lean`, `crates/leanvm_univariate/src/domain.rs`'s
`beta`: `β₀ = 1`, `β_{k+1}` the solution of `s(x) = β_k` with its low bit clear, read off the reduced matrix
of `s(x) = x² + x`) is computed, not assumed. Here:

* `beta_lanes`: its `32` words (`betaWords`, by kernel evaluation of `sPivots` and the `31` solves,
  `decide +kernel`, about 5 s; no `native_decide`). The first `28` are the statement's `PcsQuotient.Domain.beta`
  (`beta_getD_eq_betaAt`, also by kernel evaluation; the first `24` are `QuotientSecurity.betaWords`, by
  inspection);
* `beta_zero`, `beta_succ`: the Cantor property `β₀ = 1`, `sK β_{k+1} = β_k` (`k < 31`), checked on the literal
  words (`betaWords_succ`, `31` products in `K`, as `QuotientSecurity.DeployedBasis` does in `F64`);
* `basisK`, `basisE`: hence a `QuotientSecurity.CantorBasis` of `32` vectors in `K` and in `E` (`ofK` of the
  words), so that `Heap.Cantor`'s lemmas apply; `Heap.omega` of them is `UniStatement.point` and
  `UniStatement.pointE` (`omega_basisK`, `omega_basisE`, every index; the verifier's `point` reads the `32`
  low bits of its index, as `omega` does). The consequences used downstream: `pointE` is injective on
  `[0, 2^32)` (`pointE_injOn`), additive in the index's bits (`pointE_xor`), and `s^l(ω_i) = ω_{i >> l}`
  (`sq_iterate_pointE`).

Decision (recorded): the files of this family are plain (non-`module`) Lean files, as the rest of
`UniComplete` (a `module` file cannot import `Heap.Cantor`, which is not one); every definition they read is
`@[expose]`d by `UniStatement`.
-/

namespace UniComplete.Domain

open LeanVM.Parameters UniStatement Finset

/-! ### The words -/

/-- **`UniStatement.beta`'s 32 words** (`β₀ … β₃₁`, `domain.rs`'s `beta` at `BASIS = 32`). -/
def betaWords : List UInt64 :=
  [0x0000000000000001, 0x19c9369f278adc02, 0xa181e7d66f5ff794, 0x5db84357ce785d08,
    0xb973d466f5c9d0ca, 0x521ac889831a075e, 0x033ce8beddc8a656, 0xb5846c4e07b91010,
    0x4087b8cbb37a32ec, 0x00d0d3888c0ae17c, 0xafd5ac70237f2222, 0xe3f5af99cc3aaaf8,
    0x5a1db3b16a0b58b8, 0x09947c54fe7ee248, 0x0e8eaf0e0068f544, 0xa2a113500b4b4f5a,
    0xe96f9805d6ce0bb0, 0x53496f8b5c9edd4c, 0xad325cb6f4ac2a9e, 0x4a8dcf8bd7ede826,
    0xa3e9c552b6434210, 0x5fa92ad9c9bc7ed0, 0xa389f910cd7734de, 0xe916f3dfca4609d8,
    0xf89578714bd28f96, 0x564dda59237a3352, 0xad33bc6cc75aed38, 0x57a3104fcd0e5f34,
    0xb0f502e4cd60039a, 0xeb42e79f91f49f8c, 0x54e5bf3774b3f850, 0xb66864e6ec14b4d2]

/-- **The verifier's Cantor basis, as words**, by kernel evaluation of `sPivots` and `solveS` (about 5 s). -/
theorem beta_lanes : UniStatement.beta.toList.map K.lane = betaWords := by
  decide +kernel

/-- An entry of an array of `K` given by its words. -/
theorem getD_of_lanes {a : Array K} {ws : List UInt64} (h : a.toList.map K.lane = ws) (k : ℕ) :
    a.getD k 0 = K.ofLane (ws.getD k 0) := by
  subst h
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList]
  cases a[k]? <;> rfl

/-- `β_k` is the word `k`. -/
theorem beta_getD (k : ℕ) : UniStatement.beta.getD k 0 = K.ofLane (betaWords.getD k 0) :=
  getD_of_lanes beta_lanes k

/-- The statement's `28` words (`PcsQuotient.Domain.beta`, `crates/quotient`'s `beta()`), the first `28` of
`betaWords`. -/
theorem statementBeta_lanes : PcsQuotient.Domain.beta.toList.map K.lane = betaWords.take 28 := by
  decide +kernel

theorem take_getD : ∀ k : Fin 28, (betaWords.take 28).getD k.val 0 = betaWords.getD k.val 0 := by
  decide

/-- **`β_k`, `k < 28`, is the statement's** (`PcsQuotient.Domain.betaAt`). -/
theorem beta_getD_eq_betaAt {k : ℕ} (hk : k < 28) :
    UniStatement.beta.getD k 0 = PcsQuotient.Domain.betaAt k := by
  rw [beta_getD, PcsQuotient.Domain.betaAt, getD_of_lanes statementBeta_lanes, take_getD ⟨k, hk⟩]

/-! ### The Cantor property, on the words -/

/-- **`s(β_{k+1}) = β_k` on the words** (`31` products in `K`, by the kernel). -/
theorem betaWords_succ : ∀ k : Fin 31,
    sK (K.ofLane (betaWords.getD (k.val + 1) 0)) = K.ofLane (betaWords.getD k.val 0) := by
  decide +kernel

/-- **`β₀ = 1`.** -/
theorem beta_zero : UniStatement.beta.getD 0 0 = 1 := by
  rw [beta_getD]
  decide +kernel

/-- **The Cantor property** `s(β_{k+1}) = β_k`, `k < 31`. -/
theorem beta_succ {k : ℕ} (hk : k < 31) :
    sK (UniStatement.beta.getD (k + 1) 0) = UniStatement.beta.getD k 0 := by
  rw [beta_getD, beta_getD]
  exact betaWords_succ ⟨k, hk⟩

/-! ### The embedding `K → E` -/

theorem embed_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem embed_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem embed_zero : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem embed_one : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem embed_sum {ι : Type*} (s : Finset ι) (f : ι → K) : ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s

/-- `E` has characteristic two. -/
theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

/-! ### The basis -/

/-- **The verifier's Cantor basis of `K`**: `β_k = beta.getD k 0`, `32` vectors. -/
def basisK : QuotientSecurity.CantorBasis K 32 where
  β k := UniStatement.beta.getD k 0
  zero := beta_zero
  succ k hk := beta_succ (by omega)

/-- **The verifier's Cantor basis, in `E`**: `ofK β_k`. -/
def basisE : QuotientSecurity.CantorBasis E 32 where
  β k := ofK (UniStatement.beta.getD k 0)
  zero := by rw [beta_zero, embed_one]
  succ k hk := by
    show ofK _ * ofK _ + ofK _ = ofK _
    rw [← beta_succ (k := k) (by omega), sK, embed_add, embed_mul]

theorem basisK_β (k : ℕ) : basisK.β k = UniStatement.beta.getD k 0 := rfl

theorem basisE_β (k : ℕ) : basisE.β k = ofK (UniStatement.beta.getD k 0) := rfl

/-- A fold that adds `f k` where `p k` is a sum. -/
theorem foldl_ite_eq_sum {M : Type*} [AddCommMonoid M] (p : ℕ → Bool) (f : ℕ → M) (n : ℕ) :
    (List.range n).foldl (fun acc k ↦ if p k then acc + f k else acc) 0 =
      ∑ k ∈ range n, if p k then f k else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs <;> simp

/-- **`Heap.omega` of the basis is the verifier's `point`** (every index). -/
theorem omega_basisK (i : ℕ) : Heap.omega basisK i = point i := by
  unfold point
  rw [foldl_ite_eq_sum]
  rfl

/-- **`Heap.omega` of the basis in `E` is `pointE`** (every index). -/
theorem omega_basisE (i : ℕ) : Heap.omega basisE i = pointE i := by
  rw [pointE, ← omega_basisK, Heap.omega, Heap.omega, embed_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs
  · rfl
  · exact embed_zero.symm

theorem pointE_zero : pointE 0 = 0 := by
  rw [← omega_basisE, Heap.omega_zero]

/-- **Additivity**: `ω_{i xor j} = ω_i + ω_j`. -/
theorem pointE_xor (i j : ℕ) : pointE (i ^^^ j) = pointE i + pointE j := by
  rw [← omega_basisE, ← omega_basisE, ← omega_basisE, Heap.omega_xor]

/-- **`pointE` is injective on `[0, 2^32)`.** -/
theorem pointE_injOn {i j : ℕ} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) (h : pointE i = pointE j) : i = j :=
  Heap.omega_injOn basisE hi hj (by rw [omega_basisE, omega_basisE]; exact h)

theorem pointE_eq_iff {i j : ℕ} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) : pointE i = pointE j ↔ i = j :=
  ⟨pointE_injOn hi hj, fun h ↦ h ▸ rfl⟩

/-- **The digits at a point**: `s^l(ω_i) = ω_{i >> l}`, `i < 2^32` (`Heap.sq_iterate_omega`). -/
theorem sq_iterate_pointE (l : ℕ) {i : ℕ} (hi : i < 2 ^ 32) :
    (fun x : E ↦ x * x + x)^[l] (pointE i) = pointE (i >>> l) := by
  rw [← omega_basisE, ← omega_basisE]
  exact Heap.sq_iterate_omega basisE l hi

end UniComplete.Domain

/-- info: 'UniComplete.Domain.beta_lanes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.beta_lanes

/-- info: 'UniComplete.Domain.beta_getD_eq_betaAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.beta_getD_eq_betaAt

/-- info: 'UniComplete.Domain.beta_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.beta_succ

/-- info: 'UniComplete.Domain.omega_basisE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.omega_basisE

/-- info: 'UniComplete.Domain.sq_iterate_pointE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.sq_iterate_pointE
