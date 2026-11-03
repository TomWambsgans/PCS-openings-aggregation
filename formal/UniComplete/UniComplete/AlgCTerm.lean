-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): `eqEval`, `eqKernel`, `boolPoint` and their lemmas
-- (`Protocol/Whir/Complete/Tables.lean`), through `UniComplete.Whir`'s `foldl_foldOnce`.
import UniComplete.AlgCBasis
import Field.F192

/-!
# A term's value on a stack (milestone 4, the algebra of `C1` and the setup: item 1(b))

The verifier states a relation as terms `coefficient · column(point)` (`UniStatement.Term`); a term's value on a
stack (`termEval`) is the pairing of its dense weight (`denseWeight` of the one-term claim) with the stack's words
(`dotK`). Here, for the layouts the verifier builds (`StackLayout.new`) and the stacks the prover places
(`placeStack`, `setupStackOf`):

* **Generic facts** (B0). `dotK_eq_sum`, `dotK_addAt`: the pairing as a sum, and what one `addAt` adds (in range
  `x · s[i]`, out of range nothing). `eqKernel_toList`, `eqKernel_size`, `eqKernel_getD`: the verifier's `eqKernel`
  (an `Array`) is mumbai's (a `List`), its entry `j` is `eq(bits of j, p)`; `sum_eqKernel_mul`,
  `sum_eqKernel_mul_ofK`: pairing a table of `2^|p|` entries with it is `multilinearEval` at `p`.
  `termEval_plain`: a term on a column other than a `q_flock` slot, untwisted, is the sum over the column's blocks
  (`StackLayout.limbs`) of `limbScale k limb · Σ_u eq(p, u) · s[offset + u]`, each block inside the stack.
  `new_eq`: `StackLayout.new cols` is `⟨max (log2Ceil (max W 2)) 15, layBlocks S 0⟩` for a permutation `S` of the
  pieces (`pieceOf`), its blocks laid end to end from `0` (`layBlocks`, offsets the prefix sums of `2^vars`), `W`
  their words (`piecesWords`), all inside `2^vars` (`blocks_inRange`), pairwise disjoint (`blocks_disjoint`).
  `limbs_K`: a column occurring once in `cols`, `eValued = false`, `vars = v`, has one block `(0, v, o)`;
  `limbs_E`: with `eValued = true` its blocks are a permutation of `(0, v, ·), (1, v, ·), (2, v, ·)`.
  `placeStack_block`: `placeStack L data` at word `o + u` of a block `(c, l, v, o)` is `(data c l).getD u 0`.
* **Terms on `C1` and on the setup** (B1): `termEval_c1_table`, `termEval_c1_inverse`, `termEval_c1_memory`,
  `termEval_c1_bytecodeFinal`: `k ·` the multilinear extension of the column's basis-`B` coefficients at the point;
  `termEval_c1_qflockSlot`: `k ·` the multilinear extension of `q_flock`'s words `slot + 256 u`;
  `termEval_setup_address`, `termEval_setup_bytecodeTuple` (the latter at `α ++ p`: `k Σ_s eq(α, s) ·` slot `s`'s
  extension at `p`). `layoutIn_c1`, `layoutIn_setup`: the layouts the verifier states are `c1Layout`, `setupLayout`.
* **An `E`-column** (B2, for `C2`): `termEval_new_E`: limb `l` scaled by `(1, y, y²)` (`limbBasis`), so the term is
  `k ·` the multilinear extension of the column's `E` words (`Primitives.F192.eq_sum_limbs`).

Decisions (recorded): the facts about `StackLayout.new` go through `new_eq` (the sorted pieces are abstracted to a
permutation `S`: nothing depends on `mergeSort` but `mergeSort_perm`); the matcher lambdas of the verifier's code are
never restated, the generic lemmas take the step function with its value on a tuple (`rfl` at the use). `C1`'s
column list is `c1ColsOf` (the text of `layouts`), its names `c1Names` (shape-free, counted by `decide`), its
variables `c1VarsOf` (`c1ColsOf_vars`). No stack and no shape is evaluated.
-/

namespace UniComplete.AlgC

open UniStatement LeanVM.Parameters Finset
open LeanVM.Protocol.EndToEnd (boolPoint)

/-! ### `if` -/

theorem termIte_pos {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem termIte_neg {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

/-! ### Sums -/

theorem termSum_map_range {M : Type*} [AddCommMonoid M] (h : ℕ → M) (n : ℕ) :
    ((List.range n).map h).sum = ∑ k ∈ range n, h k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem termFoldl_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (L : List ℕ) (a : M) :
    L.foldl (fun acc u ↦ acc + f u) a = a + (L.map f).sum := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

/-- `Σ_{j < 16 n} f j = Σ_{q < n} Σ_{s < 16} f (s + 16 q)`. -/
theorem termSum_range_sixteen {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ∑ j ∈ range (16 * n), f j = ∑ q ∈ range n, ∑ s ∈ range 16, f (s + 16 * q)
  | 0 => by simp
  | n + 1 => by
    rw [show 16 * (n + 1) = 16 * n + 16 by ring, Finset.sum_range_add, termSum_range_sixteen f n,
      Finset.sum_range_succ (fun q ↦ ∑ s ∈ range 16, f (s + 16 * q)) n]
    congr 1
    exact Finset.sum_congr rfl fun s _ ↦ by rw [add_comm]

/-! ### The pairing -/

/-- **The pairing as a sum.** -/
theorem dotK_eq_sum (w : Array E) (s : Array K) :
    dotK w s = ∑ u ∈ range w.size, w.getD u 0 * ofK (s.getD u 0) := by
  unfold dotK
  rw [termFoldl_add (fun u ↦ w.getD u 0 * ofK (s.getD u 0)), zero_add, termSum_map_range]

theorem addAt_size (a : Array E) (i : ℕ) (x : E) : (addAt a i x).size = a.size := Array.size_modify

theorem addAt_getD (a : Array E) (i : ℕ) (x : E) (u : ℕ) :
    (addAt a i x).getD u 0 = a.getD u 0 + if i = u ∧ u < a.size then x else 0 := by
  unfold addAt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getD_eq_getD_getElem?]
  by_cases hu : u < a.size
  · rw [Array.getElem?_eq_getElem hu]
    by_cases hi : i = u <;> simp [hi, hu]
  · rw [Array.getElem?_eq_none (by omega)]
    simp [hu]

/-- **One `addAt`**: in range it adds `x · s[i]` to the pairing; out of range nothing. -/
theorem dotK_addAt (W : Array E) (s : Array K) (i : ℕ) (x : E) :
    dotK (addAt W i x) s = dotK W s + if i < W.size then x * ofK (s.getD i 0) else 0 := by
  rw [dotK_eq_sum, dotK_eq_sum, addAt_size]
  simp only [addAt_getD, add_mul, Finset.sum_add_distrib]
  congr 1
  by_cases hi : i < W.size
  · rw [termIte_pos hi, Finset.sum_eq_single i]
    · rw [termIte_pos ⟨rfl, hi⟩]
    · intro b _ hb
      rw [termIte_neg (fun (h : i = b ∧ b < W.size) ↦ hb h.1.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr hi) h
  · rw [termIte_neg hi]
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    rw [termIte_neg (fun (h : i = u ∧ u < W.size) ↦ hi (h.1 ▸ h.2)), zero_mul]

theorem dotK_replicate (n : ℕ) (s : Array K) : dotK (Array.replicate n 0) s = 0 := by
  rw [dotK_eq_sum]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split_ifs <;> simp

/-- **A fold of `addAt`s.** -/
theorem dotK_foldl_addAt (s : Array K) (g : ℕ → ℕ) (f : ℕ → E) (L : List ℕ) (W : Array E) :
    (L.foldl (fun W u ↦ addAt W (g u) (f u)) W).size = W.size ∧
    dotK (L.foldl (fun W u ↦ addAt W (g u) (f u)) W) s =
      dotK W s + (L.map fun u ↦ if g u < W.size then f u * ofK (s.getD (g u) 0) else 0).sum := by
  induction L generalizing W with
  | nil => simp
  | cons x L ih =>
    obtain ⟨h1, h2⟩ := ih (addAt W (g x) (f x))
    rw [List.foldl_cons, h1, h2, addAt_size, dotK_addAt, List.map_cons, List.sum_cons, add_assoc]
    exact ⟨rfl, rfl⟩

/-- **A fold over blocks**, each step adding `h b` to the pairing and keeping the size. -/
theorem dotK_foldl_blocks (s : Array K) (F : Array E → ℕ × ℕ × ℕ → Array E) (h : ℕ × ℕ × ℕ → E)
    (N : ℕ) (bs : List (ℕ × ℕ × ℕ))
    (hF : ∀ W b, b ∈ bs → W.size = N → (F W b).size = N ∧ dotK (F W b) s = dotK W s + h b) :
    ∀ W : Array E, W.size = N → dotK (bs.foldl F W) s = dotK W s + (bs.map h).sum := by
  induction bs with
  | nil => intro W _; simp
  | cons b bs ih =>
    intro W hW
    obtain ⟨h1, h2⟩ := hF W b (List.mem_cons_self ..) hW
    rw [List.foldl_cons, ih (fun W b hb hW ↦ hF W b (List.mem_cons_of_mem _ hb) hW) _ h1, h2,
      List.map_cons, List.sum_cons, add_assoc]

/-! ### The equality kernel and the multilinear extension -/

theorem termEqKernel_toList_gen (p : List E) (a : Array E) :
    (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) a).toList =
      p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) a.toList := by
  induction p generalizing a with
  | nil => rfl
  | cons r p ih => rw [List.foldl_cons, List.foldl_cons, ih]; simp

/-- **The verifier's `eqKernel` is mumbai's.** -/
theorem eqKernel_toList (p : List E) :
    (UniStatement.eqKernel p).toList = LeanVM.Protocol.Verifier.eqKernel p :=
  termEqKernel_toList_gen p #[1]

theorem eqKernel_size (p : List E) : (UniStatement.eqKernel p).size = 2 ^ p.length := by
  rw [← Array.length_toList, eqKernel_toList, LeanVM.Protocol.Whir.Complete.length_eqKernel]

theorem termArray_getD_toList {α : Type} (a : Array α) (j : ℕ) (d : α) : a.getD j d = a.toList.getD j d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **Entry `j` of the equality kernel** is `eq(bits of j, p)`. -/
theorem eqKernel_getD (p : List E) {j : ℕ} (hj : j < 2 ^ p.length) :
    (UniStatement.eqKernel p).getD j 0 = LeanVM.Protocol.Verifier.eqEval (boolPoint p.length j) p := by
  rw [← LeanVM.Protocol.Whir.Complete.getD_eqKernel p j hj, ← eqKernel_toList, termArray_getD_toList]

/-- **Pairing with the equality kernel is the multilinear extension.** -/
theorem sum_eqKernel_mul (p : List E) (a : Array E) (ha : a.size = 2 ^ p.length) :
    ∑ u ∈ range (2 ^ p.length), (UniStatement.eqKernel p).getD u 0 * a.getD u 0 =
      multilinearEval a.toList p := by
  unfold multilinearEval
  rw [Array.toArray_toList, UniComplete.foldl_foldOnce p a ha]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [eqKernel_getD p (Finset.mem_range.mp hu), mul_comm]

theorem termGetD_map_ofK (A : Array K) (u : ℕ) : (A.map ofK).getD u 0 = ofK (A.getD u 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[u]? <;> simp

/-- **The same on a table of `K`**, read in `E`. -/
theorem sum_eqKernel_mul_ofK (p : List E) (A : Array K) (hA : A.size = 2 ^ p.length) :
    ∑ u ∈ range (2 ^ p.length), (UniStatement.eqKernel p).getD u 0 * ofK (A.getD u 0) =
      multilinearEval (A.toList.map ofK) p := by
  rw [← Array.toList_map, ← sum_eqKernel_mul p (A.map ofK) (by rw [Array.size_map, hA])]
  exact Finset.sum_congr rfl fun u _ ↦ by rw [termGetD_map_ofK]

/-! ### A term on a column other than a `q_flock` slot -/

/-- **A block's part of a term's value**: `limbScale k limb · Σ_u eq(p, u) · s[offset + u]`. -/
def blockVal (s : Array K) (pt : List E) (k : E) (b : ℕ × ℕ × ℕ) : E :=
  limbScale k b.1 * ∑ u ∈ range (2 ^ b.2.1),
    (UniStatement.eqKernel ((pt ++ List.replicate b.2.1 0).take b.2.1)).getD u 0 * ofK (s.getD (b.2.2 + u) 0)

theorem ringTwist_ne_zero : ¬ ((0 : ℕ) = ringTwist) := by decide

theorem termGetD_single (pt : List E) : #[pt].getD 0 [] = pt := rfl

/-- **An untwisted term on a column other than a `q_flock` slot**: the sum of its blocks' parts, every block inside
the stack. -/
theorem termEval_plain (L : StackLayout) (s : Array K) (rm : Option (List E)) (column : Column)
    (pt : List E) (k : E) (hcol : ∀ j, column ≠ .qflockSlot j)
    (hin : ∀ b ∈ L.limbs column, b.2.2 + 2 ^ b.2.1 ≤ 2 ^ L.vars) :
    termEval L s rm (term column pt k) = ((L.limbs column).map (blockVal s pt k)).sum := by
  unfold termEval denseWeight termClaim term
  simp only [List.foldl_cons, List.foldl_nil, termGetD_single, ringTwist_ne_zero, ↓reduceIte, sqn]
  rw [dotK_foldl_blocks s _ (blockVal s pt k) (2 ^ L.vars) _ ?_ _ Array.size_replicate, dotK_replicate,
    zero_add]
  intro W b hb hW
  obtain ⟨limb, vars, offset⟩ := b
  have hb' := hin _ hb
  obtain ⟨h1, h2⟩ := dotK_foldl_addAt s (fun u ↦ offset + u)
    (fun u ↦ limbScale k limb * (UniStatement.eqKernel ((pt ++ List.replicate vars 0).take vars)).getD u 0)
    (List.range (2 ^ vars)) W
  refine ⟨h1.trans hW, ?_⟩
  rw [h2]
  congr 1
  rw [blockVal, termSum_map_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  simp only [Finset.mem_range] at hu hb'
  rw [termIte_pos (by omega), mul_assoc]

/-! ### `StackLayout.new`: the blocks end to end -/

/-- A column's pieces (`StackLayout.new`): itself, or its three limbs. -/
def pieceOf (p : Column × ℕ × Bool) : List (Column × ℕ × ℕ) :=
  (List.range (if p.2.2 then 3 else 1)).map fun limb ↦ (p.1, limb, p.2.1)

/-- **Blocks laid end to end** from `o`, in order. -/
def layBlocks : List (Column × ℕ × ℕ) → ℕ → List (Column × ℕ × ℕ × ℕ)
  | [], _ => []
  | (c, l, v) :: rest, o => (c, l, v, o) :: layBlocks rest (o + 2 ^ v)

/-- The words the pieces fill. -/
def piecesWords (ps : List (Column × ℕ × ℕ)) : ℕ := (ps.map fun p ↦ 2 ^ p.2.2).sum

theorem termFoldl_lay
    (F : Array (Column × ℕ × ℕ × ℕ) × ℕ → Column × ℕ × ℕ → Array (Column × ℕ × ℕ × ℕ) × ℕ)
    (hF : ∀ acc c l v, F acc (c, l, v) = (acc.1.push (c, l, v, acc.2), acc.2 + 2 ^ v)) :
    ∀ (ps : List (Column × ℕ × ℕ)) (acc : Array (Column × ℕ × ℕ × ℕ)) (o : ℕ),
      ps.foldl F (acc, o) = ((acc.toList ++ layBlocks ps o).toArray, o + piecesWords ps)
  | [], acc, o => by simp [layBlocks, piecesWords]
  | (c, l, v) :: rest, acc, o => by
    rw [List.foldl_cons, hF, termFoldl_lay F hF rest]
    simp [layBlocks, piecesWords, add_assoc]

theorem termFlatMap_pieces (cols : List (Column × ℕ × Bool)) (f : Column × ℕ × Bool → List (Column × ℕ × ℕ))
    (hf : ∀ c v e, f (c, v, e) = pieceOf (c, v, e)) : cols.flatMap f = cols.flatMap pieceOf := by
  congr 1
  funext p
  obtain ⟨c, v, e⟩ := p
  exact hf c v e

/-- **`StackLayout.new`**: the pieces in some order `S` (a permutation of `pieceOf`'s), laid end to end from `0`,
at least `15` variables. -/
theorem new_eq (cols : List (Column × ℕ × Bool)) :
    ∃ S : List (Column × ℕ × ℕ), S.Perm (cols.flatMap pieceOf) ∧
      StackLayout.new cols = ⟨max (log2Ceil (max (piecesWords S) 2)) 15, layBlocks S 0⟩ := by
  refine ⟨(cols.flatMap pieceOf).mergeSort (fun a b ↦ decide (b.2.2 ≤ a.2.2)), List.mergeSort_perm _ _, ?_⟩
  unfold StackLayout.new
  dsimp only
  rw [termFlatMap_pieces cols _ ?hf, termFoldl_lay _ ?hF]
  · simp
  · intro acc c l v; rfl
  · intro c v e; rfl

theorem le_two_pow_log2Ceil (n : ℕ) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil
  split_ifs with h
  · rw [pow_zero]; exact h
  · have := Nat.lt_log2_self (n := n - 1)
    omega

theorem piecesWords_le (S : List (Column × ℕ × ℕ)) :
    piecesWords S ≤ 2 ^ max (log2Ceil (max (piecesWords S) 2)) 15 :=
  calc piecesWords S ≤ max (piecesWords S) 2 := le_max_left _ _
    _ ≤ 2 ^ log2Ceil (max (piecesWords S) 2) := le_two_pow_log2Ceil _
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)

/-- Every block of `layBlocks S o` lies in `[o, o + words)`. -/
theorem layBlocks_bounds : ∀ (S : List (Column × ℕ × ℕ)) (o : ℕ), ∀ b ∈ layBlocks S o,
    o ≤ b.2.2.2 ∧ b.2.2.2 + 2 ^ b.2.2.1 ≤ o + piecesWords S
  | [], o, b, hb => by simp [layBlocks] at hb
  | (c, l, v) :: rest, o, b, hb => by
    simp only [layBlocks, List.mem_cons] at hb
    have hv := Nat.two_pow_pos v
    rcases hb with rfl | hb
    · simp only [piecesWords, List.map_cons, List.sum_cons]
      omega
    · obtain ⟨h1, h2⟩ := layBlocks_bounds rest (o + 2 ^ v) b hb
      simp only [piecesWords, List.map_cons, List.sum_cons] at h2 ⊢
      omega

/-- **The blocks are pairwise disjoint.** -/
theorem layBlocks_disjoint : ∀ (S : List (Column × ℕ × ℕ)) (o : ℕ), ∀ b₁ ∈ layBlocks S o, ∀ b₂ ∈ layBlocks S o,
    b₁ = b₂ ∨ b₁.2.2.2 + 2 ^ b₁.2.2.1 ≤ b₂.2.2.2 ∨ b₂.2.2.2 + 2 ^ b₂.2.2.1 ≤ b₁.2.2.2
  | [], o, b₁, h₁, _, _ => by simp [layBlocks] at h₁
  | (c, l, v) :: rest, o, b₁, h₁, b₂, h₂ => by
    simp only [layBlocks, List.mem_cons] at h₁ h₂
    rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ((layBlocks_bounds rest (o + 2 ^ v) b₂ h₂).1))
    · exact Or.inr (Or.inr ((layBlocks_bounds rest (o + 2 ^ v) b₁ h₁).1))
    · exact layBlocks_disjoint rest (o + 2 ^ v) b₁ h₁ b₂ h₂

/-- The blocks with their offsets dropped are the pieces, in order. -/
theorem layBlocks_filter_map (column : Column) : ∀ (S : List (Column × ℕ × ℕ)) (o : ℕ),
    ((layBlocks S o).filter (·.1 == column)).map (fun b ↦ (b.2.1, b.2.2.1)) =
      (S.filter (·.1 == column)).map (fun p ↦ (p.2.1, p.2.2))
  | [], _ => rfl
  | (c, l, v) :: rest, o => by
    simp only [layBlocks, List.filter_cons]
    by_cases h : c = column
    · simp [h, layBlocks_filter_map column rest]
    · simp [h, layBlocks_filter_map column rest]

/-- **A block of a column's limbs** is a block of the layout. -/
theorem mem_limbs {L : StackLayout} {column : Column} {b : ℕ × ℕ × ℕ} :
    b ∈ L.limbs column ↔ (column, b.1, b.2.1, b.2.2) ∈ L.blocks := by
  unfold StackLayout.limbs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨c, l, v, o⟩, hm, h⟩
    by_cases hc : c = column
    · subst hc
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact hm
    · simp [hc] at h
  · intro h
    exact ⟨_, h, by simp⟩

theorem termFilterMap_limbs (column : Column) (f : Column × ℕ × ℕ × ℕ → Option (ℕ × ℕ × ℕ))
    (hf : ∀ c l v o, f (c, l, v, o) = if c == column then some (l, v, o) else none) :
    ∀ B : List (Column × ℕ × ℕ × ℕ), (B.filterMap f).map (fun b ↦ (b.1, b.2.1)) =
      (B.filter (·.1 == column)).map (fun b ↦ (b.2.1, b.2.2.1))
  | [] => rfl
  | (c, l, v, o) :: B => by
    rw [List.filterMap_cons, hf, List.filter_cons]
    by_cases h : c = column
    · simp [h, termFilterMap_limbs column f hf B]
    · simp [h, termFilterMap_limbs column f hf B]

/-- **A column's limbs**, their limb and variables: the layout's blocks of the column. -/
theorem limbs_map (L : StackLayout) (column : Column) :
    (L.limbs column).map (fun b ↦ (b.1, b.2.1)) =
      (L.blocks.filter (·.1 == column)).map (fun b ↦ (b.2.1, b.2.2.1)) := by
  unfold StackLayout.limbs
  exact termFilterMap_limbs column _ (fun _ _ _ _ ↦ rfl) L.blocks

theorem flatMap_pieceOf_filter (column : Column) : ∀ cols : List (Column × ℕ × Bool),
    (cols.flatMap pieceOf).filter (·.1 == column) = (cols.filter (·.1 == column)).flatMap pieceOf
  | [] => rfl
  | p :: cols => by
    rw [List.flatMap_cons, List.filter_append, flatMap_pieceOf_filter column cols, List.filter_cons]
    by_cases h : p.1 = column
    · rw [List.filter_eq_self.mpr (fun q hq ↦ ?_)]
      · simp [h]
      · simp only [pieceOf, List.mem_map] at hq
        obtain ⟨_, _, rfl⟩ := hq
        simp [h]
    · rw [List.filter_eq_nil_iff.mpr (fun q hq ↦ ?_)]
      · simp [h]
      · simp only [pieceOf, List.mem_map] at hq
        obtain ⟨_, _, rfl⟩ := hq
        simp [h]

/-- **A column occurring once**, with its variables and kind. -/
theorem filter_fst_singleton {cols : List (Column × ℕ × Bool)} {column : Column} {v : ℕ} {e : Bool}
    (hcount : (cols.map Prod.fst).count column = 1) (hvars : ∀ p ∈ cols, p.1 = column → p.2 = (v, e)) :
    cols.filter (·.1 == column) = [(column, v, e)] := by
  have hmap : (cols.filter (·.1 == column)).map Prod.fst = [column] := by
    have h := List.filter_map (f := Prod.fst) (p := (· == column)) (l := cols)
    rw [List.filter_beq, hcount] at h
    exact h.symm
  obtain ⟨a, ha, ha1⟩ := List.map_eq_singleton_iff.mp hmap
  rw [ha]
  have hmem : a ∈ cols := (List.mem_filter.mp (ha ▸ List.mem_singleton_self a)).1
  have h2 := hvars a hmem ha1
  obtain ⟨a1, a2⟩ := a
  simp only at ha1 h2
  rw [ha1, h2]

/-- The layout's blocks of a column occurring once, their limbs and variables, from the sorted pieces. -/
theorem limbs_map_new {cols : List (Column × ℕ × Bool)} {column : Column} {v : ℕ} {e : Bool}
    (hcount : (cols.map Prod.fst).count column = 1) (hvars : ∀ p ∈ cols, p.1 = column → p.2 = (v, e)) :
    ((StackLayout.new cols).limbs column).map (fun b ↦ (b.1, b.2.1)) |>.Perm
      ((List.range (if e then 3 else 1)).map fun limb ↦ (limb, v)) := by
  obtain ⟨S, hS, hL⟩ := new_eq cols
  rw [limbs_map, hL, layBlocks_filter_map]
  have hf := hS.filter (·.1 == column)
  rw [flatMap_pieceOf_filter, filter_fst_singleton hcount hvars, List.flatMap_singleton] at hf
  have := hf.map (fun p ↦ (p.2.1, p.2.2))
  simpa [pieceOf, List.map_map, Function.comp_def] using this

/-- **Every block of `StackLayout.new cols` is inside its `2^vars` words.** -/
theorem blocks_inRange (cols : List (Column × ℕ × Bool)) :
    ∀ b ∈ (StackLayout.new cols).blocks, b.2.2.2 + 2 ^ b.2.2.1 ≤ 2 ^ (StackLayout.new cols).vars := by
  obtain ⟨S, -, hL⟩ := new_eq cols
  rw [hL]
  intro b hb
  have := (layBlocks_bounds S 0 b hb).2
  have := piecesWords_le S
  simp only at *
  omega

/-- **The blocks of `StackLayout.new cols` are pairwise disjoint.** -/
theorem blocks_disjoint (cols : List (Column × ℕ × Bool)) :
    ∀ b₁ ∈ (StackLayout.new cols).blocks, ∀ b₂ ∈ (StackLayout.new cols).blocks,
      b₁ = b₂ ∨ b₁.2.2.2 + 2 ^ b₁.2.2.1 ≤ b₂.2.2.2 ∨ b₂.2.2.2 + 2 ^ b₂.2.2.1 ≤ b₁.2.2.2 := by
  obtain ⟨S, -, hL⟩ := new_eq cols
  rw [hL]
  exact layBlocks_disjoint S 0

/-- **A `K`-column occurring once has one block** `(0, v, o)`, inside the stack. -/
theorem limbs_K {cols : List (Column × ℕ × Bool)} {column : Column} {v : ℕ}
    (hcount : (cols.map Prod.fst).count column = 1) (hvars : ∀ p ∈ cols, p.1 = column → p.2 = (v, false)) :
    ∃ o, (StackLayout.new cols).limbs column = [(0, v, o)] ∧ o + 2 ^ v ≤ 2 ^ (StackLayout.new cols).vars := by
  have h := limbs_map_new hcount hvars
  simp only [Bool.false_eq_true, ↓reduceIte, List.range_one, List.map_cons, List.map_nil,
    List.perm_singleton] at h
  obtain ⟨b, hb, hb1⟩ := List.map_eq_singleton_iff.mp h
  obtain ⟨l, v', o⟩ := b
  simp only [Prod.mk.injEq] at hb1
  obtain ⟨rfl, rfl⟩ := hb1
  refine ⟨o, hb, ?_⟩
  have hm : (0, v', o) ∈ (StackLayout.new cols).limbs column := by rw [hb]; exact List.mem_singleton_self _
  exact blocks_inRange cols _ (mem_limbs.mp hm)

/-! ### The placed stack -/

theorem termGetD_ge {α : Type} (a : Array α) {p : ℕ} (d : α) (h : a.size ≤ p) : a.getD p d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

theorem termFoldl_set (o : ℕ) (w : Array K) : ∀ (n : ℕ) (S : Array K),
    ((List.range n).foldl (fun s i ↦ s.set! (o + i) (w.getD i 0)) S).size = S.size ∧
    ∀ p, ((List.range n).foldl (fun s i ↦ s.set! (o + i) (w.getD i 0)) S).getD p 0 =
      if o ≤ p ∧ p < o + n ∧ p < S.size then w.getD (p - o) 0 else S.getD p 0
  | 0, S => by
    refine ⟨rfl, fun p ↦ ?_⟩
    rw [termIte_neg (by omega)]
    rfl
  | n + 1, S => by
    obtain ⟨h1, h2⟩ := termFoldl_set o w n S
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, h1], fun p ↦ ?_⟩
    rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, h1]
    by_cases hp : o + n = p
    · subst hp
      by_cases hs : o + n < S.size
      · rw [termIte_pos rfl, termIte_pos hs, termIte_pos ⟨by omega, by omega, hs⟩, Nat.add_sub_cancel_left]
        rfl
      · rw [termIte_pos rfl, termIte_neg hs, termIte_neg (by omega), termGetD_ge S 0 (by omega)]
        rfl
    · rw [termIte_neg hp, ← Array.getD_eq_getD_getElem?, h2 p]
      by_cases hc : o ≤ p ∧ p < o + n ∧ p < S.size
      · rw [termIte_pos hc, termIte_pos (by omega)]
      · rw [termIte_neg hc, termIte_neg (by omega)]

theorem termFoldl_place (data : Column → ℕ → Array K) (F : Array K → Column × ℕ × ℕ × ℕ → Array K)
    (hF : ∀ S c l v o, F S (c, l, v, o) =
      (List.range (2 ^ v)).foldl (fun s i ↦ s.set! (o + i) ((data c l).getD i 0)) S) :
    ∀ (ps : List (Column × ℕ × ℕ)) (o : ℕ) (S : Array K),
      ((layBlocks ps o).foldl F S).size = S.size ∧
      (∀ p, p < o → ((layBlocks ps o).foldl F S).getD p 0 = S.getD p 0) ∧
      (∀ b ∈ layBlocks ps o, ∀ u < 2 ^ b.2.2.1, b.2.2.2 + u < S.size →
        ((layBlocks ps o).foldl F S).getD (b.2.2.2 + u) 0 = (data b.1 b.2.1).getD u 0)
  | [], o, S => ⟨rfl, fun _ _ ↦ rfl, fun b hb ↦ by simp [layBlocks] at hb⟩
  | (c, l, v) :: rest, o, S => by
    have hv := Nat.two_pow_pos v
    obtain ⟨a1, a2⟩ := termFoldl_set o (data c l) (2 ^ v) S
    obtain ⟨s1, p1, q1⟩ := termFoldl_place data F hF rest (o + 2 ^ v) (F S (c, l, v, o))
    rw [hF] at s1 p1 q1
    simp only [layBlocks, List.foldl_cons, hF]
    refine ⟨s1.trans a1, fun p hp ↦ ?_, fun b hb u hu hlt ↦ ?_⟩
    · rw [p1 p (by omega), a2 p, termIte_neg (by omega)]
    · rcases List.mem_cons.mp hb with rfl | hb
      · simp only at hu hlt ⊢
        rw [p1 _ (by omega), a2, termIte_pos ⟨by omega, by omega, hlt⟩, Nat.add_sub_cancel_left]
      · exact q1 b hb u hu (by rw [a1]; exact hlt)

/-- **The placed stack** of `StackLayout.new cols`: `2^vars` words, block `(c, l, v, o)`'s word `o + u` the column's
`u`-th. -/
theorem placeStack_size (cols : List (Column × ℕ × Bool)) (data : Column → ℕ → Array K) :
    (placeStack (StackLayout.new cols) data).size = 2 ^ (StackLayout.new cols).vars := by
  obtain ⟨S, -, hL⟩ := new_eq cols
  rw [hL]
  unfold placeStack
  rw [(termFoldl_place data _ ?hF S 0 _).1, Array.size_replicate]
  case hF => intro _ _ _ _ _; rfl

theorem placeStack_block (cols : List (Column × ℕ × Bool)) (data : Column → ℕ → Array K) :
    ∀ b ∈ (StackLayout.new cols).blocks, ∀ u < 2 ^ b.2.2.1,
      (placeStack (StackLayout.new cols) data).getD (b.2.2.2 + u) 0 = (data b.1 b.2.1).getD u 0 := by
  have hin := blocks_inRange cols
  obtain ⟨S, -, hL⟩ := new_eq cols
  rw [hL] at hin ⊢
  intro b hb u hu
  unfold placeStack
  rw [(termFoldl_place data _ ?hF S 0 _).2.2 b hb u hu (by
    rw [Array.size_replicate]; have := hin b hb; simp only at this ⊢; omega)]
  case hF => intro _ _ _ _ _; rfl

/-! ### A term on a column occurring once -/

theorem termTake_pad (pt : List E) {v : ℕ} (hpt : pt.length = v) : (pt ++ List.replicate v 0).take v = pt := by
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem limbScale_zero (k : E) : limbScale k 0 = k := rfl

/-- **A term on a `K`-column occurring once**, placed by `placeStack`: `k ·` the multilinear extension of its words at
the point. -/
theorem termEval_new_K {cols : List (Column × ℕ × Bool)} {column : Column} {v : ℕ}
    (hcount : (cols.map Prod.fst).count column = 1) (hvars : ∀ p ∈ cols, p.1 = column → p.2 = (v, false))
    (hcol : ∀ j, column ≠ .qflockSlot j) (data : Column → ℕ → Array K) {A : Array K} (hA : data column 0 = A)
    (hsize : A.size = 2 ^ v) {pt : List E} (hpt : pt.length = v) (rm : Option (List E)) (k : E) :
    termEval (StackLayout.new cols) (placeStack (StackLayout.new cols) data) rm (term column pt k) =
      k * multilinearEval (A.toList.map ofK) pt := by
  obtain ⟨o, hlimbs, hin⟩ := limbs_K hcount hvars
  rw [termEval_plain _ _ rm column pt k hcol (by rw [hlimbs]; simpa using hin), hlimbs]
  have hb : (column, 0, v, o) ∈ (StackLayout.new cols).blocks :=
    mem_limbs.mp (by rw [hlimbs]; exact List.mem_singleton_self _)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, blockVal, limbScale_zero,
    termTake_pad pt hpt]
  congr 1
  rw [← sum_eqKernel_mul_ofK pt A (by rw [hsize, hpt]), hpt]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [placeStack_block cols data _ hb u (Finset.mem_range.mp hu), hA]

/-- **A term on an `E`-column occurring once** (its three limbs placed by `placeStack`, `limbWords`): `k ·` the
multilinear extension of its `E` words at the point (limb `l` scaled by `y^l`, `limbBasis`). -/
theorem termEval_new_E {cols : List (Column × ℕ × Bool)} {column : Column} {v : ℕ}
    (hcount : (cols.map Prod.fst).count column = 1) (hvars : ∀ p ∈ cols, p.1 = column → p.2 = (v, true))
    (hcol : ∀ j, column ≠ .qflockSlot j) (data : Column → ℕ → Array K) {D : Array E}
    (hD : ∀ l < 3, data column l = limbWords D l) (hsize : D.size = 2 ^ v) {pt : List E} (hpt : pt.length = v)
    (rm : Option (List E)) (k : E) :
    termEval (StackLayout.new cols) (placeStack (StackLayout.new cols) data) rm (term column pt k) =
      k * multilinearEval D.toList pt := by
  have hperm := limbs_map_new hcount hvars
  simp only [↓reduceIte] at hperm
  have hmem : ∀ b ∈ (StackLayout.new cols).limbs column, b.1 < 3 ∧ b.2.1 = v := by
    intro b hb
    have := hperm.subset (List.mem_map_of_mem (f := fun b ↦ (b.1, b.2.1)) hb)
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at this
    obtain ⟨l, hl, h1, h2⟩ := this
    exact ⟨h1 ▸ hl, h2.symm⟩
  have hin : ∀ b ∈ (StackLayout.new cols).limbs column, b.2.2 + 2 ^ b.2.1 ≤ 2 ^ (StackLayout.new cols).vars :=
    fun b hb ↦ blocks_inRange cols _ (mem_limbs.mp hb)
  rw [termEval_plain _ _ rm column pt k hcol hin]
  -- each block's part depends on its limb only
  let h : ℕ → E := fun l ↦ limbScale k l * ∑ u ∈ range (2 ^ v),
    (UniStatement.eqKernel pt).getD u 0 * ofK ((limbWords D l).getD u 0)
  have hblock : ∀ b ∈ (StackLayout.new cols).limbs column,
      blockVal (placeStack (StackLayout.new cols) data) pt k b = h b.1 := by
    intro b hb
    obtain ⟨hl, hv⟩ := hmem b hb
    obtain ⟨l, v', o⟩ := b
    simp only at hl hv
    subst hv
    have hb' := mem_limbs.mp hb
    simp only [blockVal, h, termTake_pad pt hpt]
    refine congrArg (limbScale k l * ·) (Finset.sum_congr rfl fun u hu ↦ ?_)
    rw [placeStack_block cols data _ hb' u (Finset.mem_range.mp hu), hD l hl]
  rw [List.map_congr_left hblock, show (fun b : ℕ × ℕ × ℕ ↦ h b.1) =
      (fun x : ℕ × ℕ ↦ h x.1) ∘ (fun b ↦ (b.1, b.2.1)) from rfl, ← List.map_map,
    (hperm.map _).sum_eq]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, h]
  rw [← sum_eqKernel_mul pt D (by rw [hsize, hpt]), hpt, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' : u < D.size := by rw [hsize]; exact Finset.mem_range.mp hu
  have hl : ∀ l (hl : l < 3), (limbWords D l).getD u 0 = (D.getD u 0).limb ⟨l, hl⟩ := by
    intro l hl
    rw [limbWords, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hu']
    simp [hl]
  have hl0 : (limbWords D 0).getD u 0 = Primitives.F192.limb (D.getD u 0) 0 := hl 0 (by norm_num)
  have hl1 : (limbWords D 1).getD u 0 = Primitives.F192.limb (D.getD u 0) 1 := hl 1 (by norm_num)
  have hl2 : (limbWords D 2).getD u 0 = Primitives.F192.limb (D.getD u 0) 2 := hl 2 (by norm_num)
  rw [hl0, hl1, hl2]
  have hY : limbBasis.getD 1 0 = Primitives.F192.Y := rfl
  have hY2 : limbBasis.getD 2 0 = Primitives.F192.Y ^ 2 := by
    show UniStatement.eNew 0 0 1 = Primitives.F192.Y ^ 2
    decide +kernel
  have hx : D.getD u 0 = ofK (Primitives.F192.limb (D.getD u 0) 0) +
      ofK (Primitives.F192.limb (D.getD u 0) 1) * Primitives.F192.Y +
      ofK (Primitives.F192.limb (D.getD u 0) 2) * Primitives.F192.Y ^ 2 :=
    Primitives.F192.eq_sum_limbs (D.getD u 0)
  simp only [limbScale, ↓reduceIte, show (1 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 0 by norm_num, hY, hY2]
  conv_rhs => rw [hx]
  ring

/-! ### `C1` -/

/-- **`C1`'s columns** (the text of `layouts`). -/
def c1ColsOf (shape : Shape) : List (Column × ℕ × Bool) :=
  let heights := shape.heights
  [(.qflock, heights.getD opBlake2s 0 + 8, false)] ++
    tables.flatMap (fun t ↦
      let h := heights.getD t.opcode 0
      (List.range t.width).map (fun c ↦ (Column.table t.opcode c, h, false)) ++
        [(.inverse t.opcode, h, false)]) ++
    (List.range 4).map (fun k ↦ (Column.memory k, shape.logMemory, false)) ++
    [(.bytecodeFinal, shape.logBytecode, false)]

theorem c1Layout_eq (shape : Shape) : c1Layout shape = StackLayout.new (c1ColsOf shape) := rfl

/-- **`C1`'s column names**, independent of the shape. -/
def c1Names : List Column :=
  [.qflock] ++ tables.flatMap (fun t ↦ (List.range t.width).map (fun c ↦ Column.table t.opcode c) ++
    [.inverse t.opcode]) ++ (List.range 4).map Column.memory ++ [.bytecodeFinal]

/-- A `C1` column's variables. -/
def c1VarsOf (shape : Shape) : Column → ℕ
  | .qflock => shape.heights.getD opBlake2s 0 + 8
  | .table t _ => shape.heights.getD t 0
  | .inverse t => shape.heights.getD t 0
  | .memory _ => shape.logMemory
  | .bytecodeFinal => shape.logBytecode
  | _ => 0

theorem c1ColsOf_eq_map (shape : Shape) :
    c1ColsOf shape = c1Names.map fun col ↦ (col, c1VarsOf shape col, false) := by
  simp [c1ColsOf, c1Names, List.map_flatMap, Function.comp_def, c1VarsOf]

theorem c1ColsOf_fst (shape : Shape) : (c1ColsOf shape).map Prod.fst = c1Names := by
  rw [c1ColsOf_eq_map, List.map_map]
  exact List.map_id _

theorem c1ColsOf_vars (shape : Shape) {column : Column} :
    ∀ p ∈ c1ColsOf shape, p.1 = column → p.2 = (c1VarsOf shape column, false) := by
  rw [c1ColsOf_eq_map]
  intro p hp h
  obtain ⟨col, -, rfl⟩ := List.mem_map.mp hp
  subst h
  rfl

theorem tables_width_le : ∀ t < 6, (tables.getD t default).width ≤ 37 := by decide

theorem c1Names_count_table' : ∀ t < 6, ∀ c < 37, c < (tables.getD t default).width →
    c1Names.count (.table t c) = 1 := by decide +kernel

theorem c1Names_count_table {t c : ℕ} (ht : t < 6) (hc : c < (tables.getD t default).width) :
    c1Names.count (.table t c) = 1 :=
  c1Names_count_table' t ht c (lt_of_lt_of_le hc (tables_width_le t ht)) hc

theorem c1Names_count_inverse' : ∀ t < 6, c1Names.count (.inverse t) = 1 := by decide +kernel

theorem c1Names_count_memory' : ∀ k < 4, c1Names.count (.memory k) = 1 := by decide +kernel

theorem c1Names_count_bytecodeFinal : c1Names.count .bytecodeFinal = 1 := by decide +kernel

theorem c1Names_count_qflock : c1Names.count .qflock = 1 := by decide +kernel

theorem termCount_c1 (shape : Shape) {column : Column} (h : c1Names.count column = 1) :
    ((c1ColsOf shape).map Prod.fst).count column = 1 := by
  rw [c1ColsOf_fst]; exact h

theorem inverseColumn_size (tr : Trace) (t : ℕ) : (inverseColumn tr t).size = 2 ^ tr.height t := by
  unfold inverseColumn
  exact Array.size_ofFn

theorem termEval_c1_of {tr : Trace} {column : Column} (hcount : c1Names.count column = 1)
    (hcol : ∀ j, column ≠ .qflockSlot j) {A : Array K} (hA : c1Words tr column 0 = A)
    (hsize : A.size = 2 ^ c1VarsOf tr.shape column) {pt : List E} (hpt : pt.length = c1VarsOf tr.shape column)
    (rm : Option (List E)) (k : E) :
    termEval (c1Layout tr.shape) (c1Stack tr) rm (term column pt k) = k * multilinearEval (A.toList.map ofK) pt := by
  unfold c1Stack
  rw [c1Layout_eq]
  exact termEval_new_K (termCount_c1 tr.shape hcount) (c1ColsOf_vars tr.shape) hcol (c1Words tr) hA hsize hpt rm k

/-- **A term on a table's column**, `C1`. -/
theorem termEval_c1_table (tr : Trace) (rm : Option (List E)) {t c : ℕ} (ht : t < 6)
    (hc : c < (tables.getD t default).width) (hsize : (tr.column t c).size = 2 ^ tr.height t)
    {pt : List E} (hpt : pt.length = tr.height t) (k : E) :
    termEval (c1Layout tr.shape) (c1Stack tr) rm (term (.table t c) pt k) =
      k * multilinearEval ((bCoefficients (tr.height t) (tr.column t c)).toList.map ofK) pt :=
  termEval_c1_of (c1Names_count_table ht hc) (fun _ h ↦ Column.noConfusion h)
    (A := bCoefficients (tr.height t) (tr.column t c)) rfl (by rw [bCoefficients_size, hsize]; rfl) hpt rm k

/-- **A term on a table's counter-inverse column** `z_T`, `C1`. -/
theorem termEval_c1_inverse (tr : Trace) (rm : Option (List E)) {t : ℕ} (ht : t < 6)
    {pt : List E} (hpt : pt.length = tr.height t) (k : E) :
    termEval (c1Layout tr.shape) (c1Stack tr) rm (term (.inverse t) pt k) =
      k * multilinearEval ((bCoefficients (tr.height t) (inverseColumn tr t)).toList.map ofK) pt :=
  termEval_c1_of (c1Names_count_inverse' t ht) (fun _ h ↦ Column.noConfusion h)
    (A := bCoefficients (tr.height t) (inverseColumn tr t)) rfl
    (by rw [bCoefficients_size, inverseColumn_size]; rfl) hpt rm k

/-- **A term on a memory column** (limb `k < 3`, or the final counts `k = 3`), `C1`. -/
theorem termEval_c1_memory (tr : Trace) (rm : Option (List E)) {m : ℕ} (hm : m < 4)
    (hsize : (tr.memory.getD m #[]).size = 2 ^ tr.shape.logMemory)
    {pt : List E} (hpt : pt.length = tr.shape.logMemory) (k : E) :
    termEval (c1Layout tr.shape) (c1Stack tr) rm (term (.memory m) pt k) =
      k * multilinearEval ((bCoefficients tr.shape.logMemory (tr.memory.getD m #[])).toList.map ofK) pt :=
  termEval_c1_of (c1Names_count_memory' m hm) (fun _ h ↦ Column.noConfusion h)
    (A := bCoefficients tr.shape.logMemory (tr.memory.getD m #[])) rfl
    (by rw [bCoefficients_size, hsize]; rfl) hpt rm k

/-- **A term on the bytecode's final counts**, `C1`. -/
theorem termEval_c1_bytecodeFinal (tr : Trace) (rm : Option (List E))
    (hsize : tr.bytecodeFinal.size = 2 ^ tr.shape.logBytecode)
    {pt : List E} (hpt : pt.length = tr.shape.logBytecode) (k : E) :
    termEval (c1Layout tr.shape) (c1Stack tr) rm (term .bytecodeFinal pt k) =
      k * multilinearEval ((bCoefficients tr.shape.logBytecode tr.bytecodeFinal).toList.map ofK) pt :=
  termEval_c1_of c1Names_count_bytecodeFinal (fun _ h ↦ Column.noConfusion h)
    (A := bCoefficients tr.shape.logBytecode tr.bytecodeFinal) rfl
    (by rw [bCoefficients_size, hsize]; rfl) hpt rm k

/-- **A term on `q_flock`'s slot `slot`** (`slot < 256`) at a point of BLAKE2S's `h_B` coordinates, `C1`: `k ·` the
multilinear extension of the words `slot + 256 u`, `u < 2^h_B`. -/
theorem termEval_c1_qflockSlot (tr : Trace) (rm : Option (List E)) {slot : ℕ} (hslot : slot < 256)
    {pt : List E} (hpt : pt.length = tr.height 5) (k : E) :
    termEval (c1Layout tr.shape) (c1Stack tr) rm (term (.qflockSlot slot) pt k) =
      k * multilinearEval ((List.range (2 ^ tr.height 5)).map fun u ↦ ofK (tr.qflock.getD (slot + 256 * u) 0))
        pt := by
  obtain ⟨o, hlimbs, hin⟩ := limbs_K (cols := c1ColsOf tr.shape) (column := .qflock)
    (termCount_c1 tr.shape c1Names_count_qflock) (c1ColsOf_vars tr.shape)
  have hb : (Column.qflock, 0, tr.height 5 + 8, o) ∈ (StackLayout.new (c1ColsOf tr.shape)).blocks :=
    mem_limbs.mp (by rw [hlimbs]; exact List.mem_singleton_self _)
  unfold termEval denseWeight termClaim term c1Stack
  rw [c1Layout_eq]
  simp only [List.foldl_cons, List.foldl_nil, termGetD_single, hlimbs]
  obtain ⟨-, h2⟩ := dotK_foldl_addAt (placeStack (StackLayout.new (c1ColsOf tr.shape)) (c1Words tr))
    (fun u ↦ o + slot + 256 * u) (fun u ↦ limbScale k 0 * (UniStatement.eqKernel pt).getD u 0)
    (List.range (UniStatement.eqKernel pt).size) (Array.replicate (2 ^ (StackLayout.new (c1ColsOf tr.shape)).vars) 0)
  rw [h2, dotK_replicate, zero_add, termSum_map_range, eqKernel_size, hpt, Array.size_replicate,
    ← sum_eqKernel_mul (a := ((List.range (2 ^ tr.height 5)).map fun u ↦ ofK (tr.qflock.getD (slot + 256 * u) 0)).toArray)
      pt (by simp [hpt]), hpt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.mp hu
  have hw : slot + 256 * u < 2 ^ (tr.height 5 + 8) := by
    rw [pow_add]; norm_num; omega
  have hin' : o + 2 ^ (tr.height 5 + 8) ≤ 2 ^ (StackLayout.new (c1ColsOf tr.shape)).vars := hin
  have hst := placeStack_block (c1ColsOf tr.shape) (c1Words tr) _ hb (slot + 256 * u) hw
  simp only at hst
  have hcw : c1Words tr .qflock 0 = tr.qflock := rfl
  have hget : ((List.range (2 ^ tr.height 5)).map fun u ↦ ofK (tr.qflock.getD (slot + 256 * u) 0)).toArray.getD u 0 =
      ofK (tr.qflock.getD (slot + 256 * u) 0) := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hu']
    rfl
  rw [termIte_pos (by omega), show o + slot + 256 * u = o + (slot + 256 * u) by ring, hst, hcw, limbScale_zero,
    hget]
  ring

/-- **The layouts the verifier states** are `C1`'s and the setup's, whatever `C2`'s columns. -/
theorem layoutIn_c1 (shape : Shape) (cols : List (Column × ℕ × Bool)) :
    layoutIn (layouts shape cols) .c1 = c1Layout shape := rfl

theorem layoutIn_setup (shape : Shape) (cols : List (Column × ℕ × Bool)) :
    layoutIn (layouts shape cols) .setup = setupLayout shape := rfl

/-! ### The setup -/

/-- **The setup's columns** (the text of `layouts`). -/
def setupColsOf (shape : Shape) : List (Column × ℕ × Bool) :=
  [(.bytecodeTuple, shape.logBytecode + 4, false), (.address, shape.logMemory, false)]

theorem setupLayout_eq (shape : Shape) : setupLayout shape = StackLayout.new (setupColsOf shape) := rfl

theorem setup_limbs (shape : Shape) :
    (∃ o₁, (setupLayout shape).limbs .bytecodeTuple = [(0, shape.logBytecode + 4, o₁)] ∧
      o₁ + 2 ^ (shape.logBytecode + 4) ≤ 2 ^ (setupLayout shape).vars) ∧
    (∃ o₂, (setupLayout shape).limbs .address = [(0, shape.logMemory, o₂)] ∧
      o₂ + 2 ^ shape.logMemory ≤ 2 ^ (setupLayout shape).vars) := by
  rw [setupLayout_eq]
  have hfst : (setupColsOf shape).map Prod.fst = [Column.bytecodeTuple, Column.address] := rfl
  refine ⟨limbs_K (by rw [hfst]; decide) ?_, limbs_K (by rw [hfst]; decide) ?_⟩
  · intro p hp h
    simp only [setupColsOf, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rfl
    · exact absurd h (by simp)
  · intro p hp h
    simp only [setupColsOf, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact absurd h (by simp)
    · rfl

/-- **The setup stack's word `w`**: the tuple block's, the addresses' block's, or zero. -/
theorem setupStackOf_getD (tr : Trace) {o₁ o₂ : ℕ}
    (h₁ : (setupLayout tr.shape).limbs .bytecodeTuple = [(0, tr.shape.logBytecode + 4, o₁)])
    (h₂ : (setupLayout tr.shape).limbs .address = [(0, tr.shape.logMemory, o₂)]) {w : ℕ}
    (hw : w < 2 ^ (setupLayout tr.shape).vars) :
    (setupStackOf tr).getD w 0 =
      if o₁ ≤ w ∧ w < o₁ + 2 ^ (tr.shape.logBytecode + 4) then
        (bCoefficients tr.shape.logBytecode (tr.slots.getD ((w - o₁) % 16) #[])).getD ((w - o₁) / 16) 0
      else if o₂ ≤ w ∧ w < o₂ + 2 ^ tr.shape.logMemory then
        (bCoefficients tr.shape.logMemory (addressColumn tr.shape.logMemory)).getD (w - o₂) 0
      else 0 := by
  unfold setupStackOf
  simp only [h₁, h₂, List.headD_cons]
  rw [E2ECompleteness.getD_ofFn' _ hw]
  split_ifs
  · rw [E2ECompleteness.getD_ofFn' _ (Nat.mod_lt _ (by norm_num))]
  · rfl
  · rfl

/-- The setup's two blocks are disjoint. -/
theorem setup_disjoint (shape : Shape) {o₁ o₂ : ℕ}
    (h₁ : (setupLayout shape).limbs .bytecodeTuple = [(0, shape.logBytecode + 4, o₁)])
    (h₂ : (setupLayout shape).limbs .address = [(0, shape.logMemory, o₂)]) :
    o₁ + 2 ^ (shape.logBytecode + 4) ≤ o₂ ∨ o₂ + 2 ^ shape.logMemory ≤ o₁ := by
  have hb₁ := mem_limbs.mp (h₁ ▸ List.mem_singleton_self (0, shape.logBytecode + 4, o₁))
  have hb₂ := mem_limbs.mp (h₂ ▸ List.mem_singleton_self (0, shape.logMemory, o₂))
  rw [setupLayout_eq] at hb₁ hb₂
  rcases blocks_disjoint _ _ hb₁ _ hb₂ with h | h | h
  · simp at h
  · exact Or.inl h
  · exact Or.inr h

/-- **A term on the memory's addresses**, setup. -/
theorem termEval_setup_address (tr : Trace) (rm : Option (List E)) {pt : List E}
    (hpt : pt.length = tr.shape.logMemory) (k : E) :
    termEval (setupLayout tr.shape) (setupStackOf tr) rm (term .address pt k) =
      k * multilinearEval ((bCoefficients tr.shape.logMemory (addressColumn tr.shape.logMemory)).toList.map ofK)
        pt := by
  obtain ⟨⟨o₁, h₁, hin₁⟩, ⟨o₂, h₂, hin₂⟩⟩ := setup_limbs tr.shape
  have hdis := setup_disjoint tr.shape h₁ h₂
  rw [termEval_plain _ _ rm _ pt k (fun _ h ↦ Column.noConfusion h) (by rw [h₂]; simpa using hin₂), h₂]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, blockVal, limbScale_zero,
    termTake_pad pt hpt]
  congr 1
  rw [← sum_eqKernel_mul_ofK pt _ (by rw [bCoefficients_size, hpt]; exact Array.size_ofFn), hpt]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.mp hu
  rw [setupStackOf_getD tr h₁ h₂ (by omega), termIte_neg (by omega), termIte_pos ⟨by omega, by omega⟩,
    Nat.add_sub_cancel_left]

theorem termBound_mul_add {n m s q : ℕ} (hs : s < 2 ^ n) (hq : q < 2 ^ m) : s + 2 ^ n * q < 2 ^ (n + m) := by
  calc s + 2 ^ n * q < 2 ^ n + 2 ^ n * q := by omega
    _ = 2 ^ n * (q + 1) := by ring
    _ ≤ 2 ^ n * 2 ^ m := Nat.mul_le_mul_left _ hq
    _ = 2 ^ (n + m) := (pow_add _ _ _).symm

/-- **The equality kernel of a concatenation** is the product of the two kernels. -/
theorem eqKernel_append_getD (a p : List E) {s q : ℕ} (hs : s < 2 ^ a.length) (hq : q < 2 ^ p.length) :
    (UniStatement.eqKernel (a ++ p)).getD (s + 2 ^ a.length * q) 0 =
      (UniStatement.eqKernel a).getD s 0 * (UniStatement.eqKernel p).getD q 0 := by
  rw [eqKernel_getD (a ++ p) (by rw [List.length_append]; exact termBound_mul_add hs hq), List.length_append,
    LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ hs,
    LeanVM.Protocol.Whir.Complete.eqEval_append _ _ _ _ (LeanVM.Protocol.Whir.Complete.length_boolPoint _ _),
    eqKernel_getD a hs, eqKernel_getD p hq]

/-- **A term on the bytecode's tuples** at `α ++ p`, setup: `k Σ_s eq(α, s) ·` slot `s`'s multilinear extension at
`p` (slot `s` of coefficient `j` at word `s + 16 j`). -/
theorem termEval_setup_bytecodeTuple (tr : Trace) (rm : Option (List E)) {alphas pt : List E}
    (ha : alphas.length = 4) (hpt : pt.length = tr.shape.logBytecode)
    (hslots : ∀ s < 16, (tr.slots.getD s #[]).size = 2 ^ tr.shape.logBytecode) (k : E) :
    termEval (setupLayout tr.shape) (setupStackOf tr) rm (term .bytecodeTuple (alphas ++ pt) k) =
      k * ∑ s ∈ range 16, (UniStatement.eqKernel alphas).getD s 0 *
        multilinearEval ((bCoefficients tr.shape.logBytecode (tr.slots.getD s #[])).toList.map ofK) pt := by
  obtain ⟨⟨o₁, h₁, hin₁⟩, ⟨o₂, h₂, hin₂⟩⟩ := setup_limbs tr.shape
  have hlen : (alphas ++ pt).length = tr.shape.logBytecode + 4 := by rw [List.length_append, ha, hpt]; ring
  rw [termEval_plain _ _ rm _ _ k (fun _ h ↦ Column.noConfusion h) (by rw [h₁]; simpa using hin₁), h₁]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, blockVal, limbScale_zero,
    termTake_pad _ hlen]
  refine congrArg (k * ·) ?_
  have h16 : 2 ^ (tr.shape.logBytecode + 4) = 16 * 2 ^ tr.shape.logBytecode := by
    rw [pow_succ, pow_succ, pow_succ, pow_succ]; ring
  rw [h16, termSum_range_sixteen, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs' := Finset.mem_range.mp hs
  rw [← sum_eqKernel_mul_ofK pt _ (by rw [bCoefficients_size, hslots s hs', hpt]), hpt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  have hq' := Finset.mem_range.mp hq
  have hj : s + 16 * q < 2 ^ (tr.shape.logBytecode + 4) := by
    rw [pow_add]; norm_num; omega
  have hk := eqKernel_append_getD alphas pt (s := s) (q := q) (by rw [ha]; norm_num; exact hs')
    (by rw [hpt]; exact hq')
  rw [ha, show (2 : ℕ) ^ 4 = 16 by norm_num] at hk
  rw [hk, setupStackOf_getD tr h₁ h₂ (by omega), termIte_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left,
    show (s + 16 * q) % 16 = s by omega, show (s + 16 * q) / 16 = q by omega]
  ring

end UniComplete.AlgC

/-! ### Axioms -/

/-- info: 'UniComplete.AlgC.termEval_new_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_new_K

/-- info: 'UniComplete.AlgC.termEval_new_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_new_E

/-- info: 'UniComplete.AlgC.termEval_c1_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_c1_table

/-- info: 'UniComplete.AlgC.termEval_c1_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_c1_inverse

/-- info: 'UniComplete.AlgC.termEval_c1_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_c1_memory

/-- info: 'UniComplete.AlgC.termEval_c1_bytecodeFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_c1_bytecodeFinal

/-- info: 'UniComplete.AlgC.termEval_c1_qflockSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_c1_qflockSlot

/-- info: 'UniComplete.AlgC.termEval_setup_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_setup_address

/-- info: 'UniComplete.AlgC.termEval_setup_bytecodeTuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.AlgC.termEval_setup_bytecodeTuple
