-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecStatement.Lemmas.Side
import RecStatement.Lemmas.Coset

/-!
# The verifier's constants are the circuit's

`SpecOf S G B pairOf portOf nz pubOf` says that the arithmetic's constants `S` (`CoreSpec`) are `Spec::of` of
`RecPiop`'s circuit `G`, its points the Cantor basis `B` (`ω = Heap.omega B`):

* the shape: `m = logN`, `r = logW`, `m ≤ n`;
* **the recursion's constants** are the blocks' normalised ones (`NormConsts`, `c_s = Π_{j<s} e_j / e_s`);
* **the pairs** enumerate `G.pairs` (`pairOf`, a bijection from the indices), each with its block's rows' log `s` and
  `Ẑ_s(c_p)`;
* **the groups** partition the pairs' indices (`groups_perm`), a group's pairs of its role, its pull flag the
  pairs' (a pull-less pair is a port's), its formula theirs as a value on any cells (`group_formula`, at the powers of
  `γ` the verifier takes);
* **the public side**: the zero coset is the first `nz = 2^k` ports (tag `N`, `w_k`'s coefficients, their public
  fingerprints zero), the other terms enumerate the other ports (`portOf`), each term's tag `N + j` and its value
  port `j`'s public fingerprint `F_j` (`term_value`), the tags below `2^28`, the walk a permutation of the terms.

This is the transcription's hypothesis: `Spec.of` computes these from the circuit's tables, as the Rust does; that
they are `RecPiop`'s circuit's is the composition's link (the circuit compiler's, `RecCircuit`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-- The empty term. -/
def noTerm : ℕ × LinF F := (0, ⟨[], none⟩)

/-- **The verifier's constants are `G`'s.** -/
structure SpecOf {n : ℕ} (S : CoreSpec F) (G : RecPiop.Circuit F) (B : QuotientSecurity.CantorBasis F n)
    (pairOf : ℕ → Block × ℕ) (portOf : ℕ → ℕ) (nz : ℕ) (pubOf : List F → ℕ → List F) : Prop where
  logN : S.logN = G.logN
  logRow : S.logRow = G.logW
  hn : G.logN ≤ n
  omega : S.ω = Heap.omega B
  c : NormConsts (blockBasis (Heap.omega B) G.logW) S.c (G.logN - G.logW)
  pair_mem : ∀ i < S.pairs.length, pairOf i ∈ G.pairs
  pair_inj : ∀ i < S.pairs.length, ∀ j < S.pairs.length, pairOf i = pairOf j → i = j
  pair_surj : ∀ p ∈ G.pairs, ∃ i < S.pairs.length, pairOf i = p
  pair_s : ∀ i < S.pairs.length, (S.pairs.getD i (0, 0)).1 = (pairOf i).1.logRows
  pair_z : ∀ i < S.pairs.length, (S.pairs.getD i (0, 0)).2 =
    zHat S.c (pairOf i).1.logRows (Heap.omega B (G.pairBase (pairOf i)))
  groups_perm : (S.groups.flatMap (·.pairs)).Perm (List.range S.pairs.length)
  group_role : ∀ g ∈ S.groups, ∀ i ∈ g.pairs, (pairOf i).2 = g.role
  group_pulls : ∀ g ∈ S.groups, ∀ i ∈ g.pairs, g.pulls = !(G.regionRole (pairOf i).1 (pairOf i).2).isPort
  group_formula : ∀ g ∈ S.groups, ∀ i ∈ g.pairs, ∀ (γ : F) (v : ℕ → F),
    g.formula.eval (powersList γ (S.maxGamma + 1)) (fun c ↦ v (c ^^^ g.role)) =
      (G.regionRole (pairOf i).1 (pairOf i).2).value γ (v 0) (fun c ↦ v ((pairOf i).2 ^^^ c))
  walk_perm : S.walk.Perm (List.range S.publicTerms.length)
  coset : (S.zeroCoset = none ∧ nz = 0) ∨
    ∃ k, S.zeroCoset = some (G.N, k, subspaceCoeffsF k) ∧ nz = 2 ^ k ∧ k ≤ G.logN
  nz_le : nz ≤ G.nP
  zero_ports : ∀ j < nz, ∀ (pubs : List F) (γ : F), G.pubFp γ (pubOf pubs) j = 0
  port_mem : ∀ J < S.publicTerms.length, nz ≤ portOf J ∧ portOf J < G.nP
  port_inj : ∀ J < S.publicTerms.length, ∀ J' < S.publicTerms.length, portOf J = portOf J' → J = J'
  port_surj : ∀ j, nz ≤ j → j < G.nP → ∃ J < S.publicTerms.length, portOf J = j
  term_tag : ∀ J < S.publicTerms.length, (S.publicTerms.getD J noTerm).1 = G.N + portOf J
  tags_lt : G.N + G.nP ≤ 2 ^ 28
  term_value : ∀ J < S.publicTerms.length, ∀ (pubs : List F) (γ : F),
    (S.publicTerms.getD J noTerm).2.eval (powersList γ (S.maxGamma + 1)) (fun c ↦ pubs.getD c 0) =
      G.pubFp γ (pubOf pubs) (portOf J)

/-! ## The Cantor basis's points, bit by bit -/

theorem list_range_sum (f : ℕ → F) : ∀ N, ((List.range N).map f).sum = ∑ i ∈ range N, f i
  | 0 => rfl
  | N + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_range_sum f N, Finset.sum_range_succ]; simp

theorem omega_two_pow {n : ℕ} (B : QuotientSecurity.CantorBasis F n) (b : ℕ) :
    Heap.omega B (2 ^ b) = if b < n then B.β b else 0 := by
  unfold Heap.omega
  split_ifs with hb
  · rw [Finset.sum_eq_single b (fun k _ hk ↦ by simp [Ne.symm hk])
      (fun h ↦ absurd (Finset.mem_range.mpr hb) h)]
    simp [Nat.testBit_two_pow_self]
  · refine Finset.sum_eq_zero fun k hk ↦ ?_
    have : b ≠ k := fun h ↦ hb (h ▸ Finset.mem_range.mp hk)
    simp [this]

/-- **`ω_d` from `d`'s bits** below `2^28`: `Σ_{b<28} d_b ω(2^b)`. -/
theorem omega_bits {n : ℕ} (B : QuotientSecurity.CantorBasis F n) {d : ℕ} (hd : d < 2 ^ 28) :
    Heap.omega B d = ((List.range 28).map fun b ↦ if d.testBit b then Heap.omega B (2 ^ b) else 0).sum := by
  rw [list_range_sum]
  simp only [omega_two_pow]
  unfold Heap.omega
  rcases le_total n 28 with h | h
  · have e := Finset.sum_subset (Finset.range_subset_range.mpr h)
      (f := fun b ↦ if d.testBit b then (if b < n then B.β b else 0) else 0) (fun b _ hb' ↦ by
        have : ¬ b < n := fun h' ↦ hb' (Finset.mem_range.mpr h')
        simp [this])
    rw [← e]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    simp [Finset.mem_range.mp hb]
  · have e := Finset.sum_subset (Finset.range_subset_range.mpr h)
      (f := fun k ↦ if d.testBit k then B.β k else 0) (fun k _ hk' ↦ by
        have h28 : ¬ k < 28 := fun h' ↦ hk' (Finset.mem_range.mpr h')
        have : d.testBit k = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [this])
    rw [← e]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    have : b < n := lt_of_lt_of_le (Finset.mem_range.mp hb) h
    simp [this]

end RecStatement
