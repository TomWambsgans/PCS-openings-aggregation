-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.BatchProofWeight

/-!
# The batching sumcheck's honest rounds (`batchRound`) and the verifier's claims

The prover's round `j` (`batchRound`) sends `q(0)` and the `X²` coefficient of
`q(X) = Σ_k λ^k Σ_i W_k(X, i) C_k(X, i) + λ^n M(X)`, over its current (folded) tables, zero-extended: a table of
one entry is `(1 + X)` times it (`foldE`'s partner past the end is zero), and the matrices' product `Σ G L̂ ŝ` over
their first `k + 6` variables, then `(1 + X)` times its value. The verifier (`sumcheck … 3 (replicate vars none)`,
`roundPoly`) reads `c0`, `c2`, derives `c1 = claim + c2`, and goes to `c0 + c1 r + c2 r²`. Here, as pure functions
of the challenges:

* **`batchRound_eq`**: `batchRound` is "send `batchQ0`, send `batchQ2`, draw `r`, `batchNext`".
* **`batch_round`**: if the verifier's claim is the running sum `batchClaim λ j st` (the batched pairings of the
  current tables, plus `λ^n` times the matrices' part: their product sum before their last round, their value
  after), the verifier's next claim is the running sum of the next state. Per pair (`dotE_foldE`): the round's
  `(a, b)` give `Σ fold(w) fold(c) = a + (Σ w c + b) r + b r²` (characteristic two); the matrices' product
  (`prod3_foldE`): the same, given that the `X³` coefficient `Σ dG dL dS` vanishes, which holds when `L̂` depends
  on the low `k − j` bits only and `ŝ` on the others (`LowDep`, `HighDep`, kept by the folds).
* **`batch_rounds`**: over `vars` rounds from the target, the verifier's last claim is
  `Σ_k λ^k W̃_k(r) C̃_k(r) Π_{j ≥ vars_k} (1 + r_j)² + λ^n G̃(r) L̃(r) S̃(r) Π_{j ≥ k+6} (1 + r_j)` (`terminalOf`), each
  table's multilinear extension at the point's first coordinates (`tableEval`, low first): a table of `2^d` entries
  folds to its extension at `r_{<d}` (`foldE_run`), then gains `(1 + r_j)` a round. The two zero extensions of a
  stack's pair give the square; the matrices' one (`eq(·, 0)` on the batch's other variables) a single power.

Decisions: the tables' sizes are hypotheses (`BatchWF`): each stack's weight and words `2^{d_k}` entries, `d_k ≤ vars`;
the matrices' three tables `2^{k+6}` entries with `k + 6 ≤ vars` and the structure above (`LowDep`, `HighDep`;
`BatchProof`'s `PendingShape` states it of Flock's tables). The challenges are any list (`rs`): the Fiat–Shamir draws
are the synchronisation layer's (`BatchProofSync`).
-/

open LeanVM.Parameters
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.Verifier (eqEval)
open Finset

namespace UniComplete

open UniStatement (Combined StackLayout Column)

theorem two_eq_zero_E' : (2 : E) = 0 := LeanVM.Protocol.Whir.Complete.two_eq_zero_E

/-! ## Powers -/

theorem epowAux_eq : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    UniStatement.epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, h => by
    obtain rfl : n = 0 := by simpa using h
    simp [UniStatement.epowAux]
  | fuel + 1, base, out, n, h => by
    unfold UniStatement.epowAux
    have h' : n / 2 < 2 ^ fuel := by rw [pow_succ] at h; omega
    by_cases h0 : n = 0
    · subst h0; simp
    · rw [ite_neg h0, epowAux_eq fuel _ _ _ h']
      by_cases h1 : n % 2 = 1
      · rw [ite_pos h1]
        conv_rhs => rw [show n = 2 * (n / 2) + 1 by omega]
        rw [pow_succ, pow_mul, sq]
        ring
      · rw [ite_neg h1]
        conv_rhs => rw [show n = 2 * (n / 2) by omega]
        rw [pow_mul, sq]

/-- `E::pow` is the power. -/
theorem epow_eq_pow (x : E) (n : ℕ) : UniStatement.epow x n = x ^ n := by
  unfold UniStatement.epow
  rw [epowAux_eq _ _ _ _ Nat.lt_log2_self, one_mul]

/-! ## Pairings, weighted sums -/

/-- The pairing `Σ_i w_i c_i` over the first table's entries. -/
def dotE (w c : Array E) : E := ∑ i ∈ range w.size, w.getD i 0 * c.getD i 0

/-- The product sum `Σ_i g_i l_i s_i` over the first table's entries. -/
def prod3 (g l s : Array E) : E := ∑ i ∈ range g.size, g.getD i 0 * l.getD i 0 * s.getD i 0

/-- The weighted sum `Σ_k λ^k x_k`. -/
def wsum (lambda : E) : List E → E
  | [] => 0
  | x :: xs => x + lambda * wsum lambda xs

theorem wsum_comb (lambda r : E) {α : Type} (f g h : α → E) : ∀ L : List α,
    wsum lambda (L.map f) + (wsum lambda (L.map g) + wsum lambda (L.map h)) * r + wsum lambda (L.map h) * r ^ 2 =
      wsum lambda (L.map fun x ↦ f x + (g x + h x) * r + h x * r ^ 2)
  | [] => by simp [wsum]
  | x :: L => by
    simp only [List.map_cons, wsum]
    rw [← wsum_comb lambda r f g h L]
    ring

theorem wsum_congr (lambda : E) {α : Type} (f g : α → E) (L : List α) (h : ∀ x ∈ L, f x = g x) :
    wsum lambda (L.map f) = wsum lambda (L.map g) := by
  rw [List.map_congr_left h]

theorem foldl_pair_add (f g : ℕ → E) : ∀ (n : ℕ) (a b : E),
    (List.range n).foldl (fun acc i ↦ (acc.1 + f i, acc.2 + g i)) (a, b) =
      (a + ∑ i ∈ range n, f i, b + ∑ i ∈ range n, g i)
  | 0, a, b => by simp
  | n + 1, a, b => by
    rw [List.range_succ, List.foldl_append, foldl_pair_add f g n, List.foldl_cons, List.foldl_nil,
      sum_range_succ, sum_range_succ, add_assoc, add_assoc]

/-- A sum over `N` entries, zero past them, by pairs. -/
theorem sum_pairs (f : ℕ → E) (N : ℕ) (hf : ∀ i, N ≤ i → f i = 0) :
    ∑ i ∈ range N, f i = ∑ i ∈ range ((N + 1) / 2), (f (2 * i) + f (2 * i + 1)) := by
  rw [← sum_range_two_mul f ((N + 1) / 2)]
  rcases Nat.even_or_odd' N with ⟨h, rfl | rfl⟩
  · rw [show (2 * h + 1) / 2 = h by omega]
  · rw [show (2 * h + 1 + 1) / 2 = h + 1 by omega, show 2 * (h + 1) = 2 * h + 1 + 1 by ring,
      sum_range_succ f (2 * h + 1), hf _ (by omega), add_zero]

theorem getD_ge (v : Array E) {i : ℕ} (h : v.size ≤ i) : v.getD i 0 = 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-! ## Folds -/

theorem foldE_size (v : Array E) (r : E) : (foldE v r).size = (v.size + 1) / 2 := by simp [foldE]

theorem foldE_getD (v : Array E) (r : E) {i : ℕ} (hi : i < (v.size + 1) / 2) :
    (foldE v r).getD i 0 = v.getD (2 * i) 0 + r * (v.getD (2 * i) 0 + v.getD (2 * i + 1) 0) := by
  unfold foldE
  rw [E2ECompleteness.getD_ofFn' _ hi]

theorem roundSums_eq (w c : Array E) : roundSums w c =
    (∑ i ∈ range ((w.size + 1) / 2), w.getD (2 * i) 0 * c.getD (2 * i) 0,
      ∑ i ∈ range ((w.size + 1) / 2),
        (w.getD (2 * i) 0 + w.getD (2 * i + 1) 0) * (c.getD (2 * i) 0 + c.getD (2 * i + 1) 0)) := by
  unfold roundSums
  dsimp only
  rw [foldl_pair_add, zero_add, zero_add]

theorem productRound_eq (g l s : Array E) : productRound g l s =
    (∑ i ∈ range (g.size / 2), g.getD (2 * i) 0 * l.getD (2 * i) 0 * s.getD (2 * i) 0,
      ∑ i ∈ range (g.size / 2),
        (g.getD (2 * i) 0 * (l.getD (2 * i) 0 + l.getD (2 * i + 1) 0) * (s.getD (2 * i) 0 + s.getD (2 * i + 1) 0) +
          (g.getD (2 * i) 0 + g.getD (2 * i + 1) 0) * l.getD (2 * i) 0 * (s.getD (2 * i) 0 + s.getD (2 * i + 1) 0) +
          (g.getD (2 * i) 0 + g.getD (2 * i + 1) 0) * (l.getD (2 * i) 0 + l.getD (2 * i + 1) 0) * s.getD (2 * i) 0)) := by
  unfold productRound
  dsimp only
  rw [foldl_pair_add, zero_add, zero_add]

/-- **A pair's round**: the folded pairing is the verifier's quadratic at `r` (characteristic two). -/
theorem pair_identity (w0 w1 c0 c1 r : E) :
    (w0 + r * (w0 + w1)) * (c0 + r * (c0 + c1)) =
      w0 * c0 + (w0 * c0 + w1 * c1 + (w0 + w1) * (c0 + c1)) * r + (w0 + w1) * (c0 + c1) * r ^ 2 := by
  rw [← sub_eq_zero]
  ring_nf
  simp [two_eq_zero_E']

/-- **A product's round**: the folded product is the verifier's quadratic at `r` plus `(r + r³)` times the `X³`
coefficient. -/
theorem triple_identity (g0 g1 l0 l1 s0 s1 r : E) :
    (g0 + r * (g0 + g1)) * (l0 + r * (l0 + l1)) * (s0 + r * (s0 + s1)) =
      g0 * l0 * s0 + ((g0 * l0 * s0 + g1 * l1 * s1) +
        (g0 * (l0 + l1) * (s0 + s1) + (g0 + g1) * l0 * (s0 + s1) + (g0 + g1) * (l0 + l1) * s0)) * r +
        (g0 * (l0 + l1) * (s0 + s1) + (g0 + g1) * l0 * (s0 + s1) + (g0 + g1) * (l0 + l1) * s0) * r ^ 2 +
        (r ^ 3 + r) * ((g0 + g1) * (l0 + l1) * (s0 + s1)) := by
  rw [← sub_eq_zero]
  ring_nf
  simp [two_eq_zero_E']

/-- **The pair's round on the tables**: `Σ fold(w) fold(c) = a + (Σ w c + b) r + b r²`, `(a, b)` the round's sums. -/
theorem dotE_foldE (w c : Array E) (h : w.size = c.size) (r : E) :
    dotE (foldE w r) (foldE c r) =
      (roundSums w c).1 + (dotE w c + (roundSums w c).2) * r + (roundSums w c).2 * r ^ 2 := by
  rw [roundSums_eq]
  unfold dotE
  dsimp only
  rw [foldE_size, sum_pairs (fun i ↦ w.getD i 0 * c.getD i 0) w.size (fun i hi ↦ by rw [getD_ge w hi, zero_mul])]
  simp only [add_mul, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [foldE_getD w r hi', foldE_getD c r (by rw [← h]; exact hi'), pair_identity]
  ring

/-- **The product's round on the tables**, its `X³` coefficient zero. -/
theorem prod3_foldE (g l s : Array E) (hl : l.size = g.size) (hs : s.size = g.size) (heven : 2 ∣ g.size)
    (hcubic : ∑ i ∈ range (g.size / 2), (g.getD (2 * i) 0 + g.getD (2 * i + 1) 0) *
      (l.getD (2 * i) 0 + l.getD (2 * i + 1) 0) * (s.getD (2 * i) 0 + s.getD (2 * i + 1) 0) = 0) (r : E) :
    prod3 (foldE g r) (foldE l r) (foldE s r) =
      (productRound g l s).1 + (prod3 g l s + (productRound g l s).2) * r + (productRound g l s).2 * r ^ 2 := by
  rw [productRound_eq]
  unfold prod3
  dsimp only
  have hh : (g.size + 1) / 2 = g.size / 2 := by omega
  rw [foldE_size, hh, sum_pairs (fun i ↦ g.getD i 0 * l.getD i 0 * s.getD i 0) g.size
      (fun i hi ↦ by rw [getD_ge g hi, zero_mul, zero_mul]), hh]
  simp only [add_mul, sum_mul, ← sum_add_distrib]
  rw [← sub_eq_zero, ← sum_sub_distrib]
  calc _ = ∑ i ∈ range (g.size / 2), (r ^ 3 + r) * ((g.getD (2 * i) 0 + g.getD (2 * i + 1) 0) *
          (l.getD (2 * i) 0 + l.getD (2 * i + 1) 0) * (s.getD (2 * i) 0 + s.getD (2 * i + 1) 0)) := by
        refine sum_congr rfl fun i hi ↦ ?_
        have hi' : i < (g.size + 1) / 2 := by rw [hh]; exact mem_range.mp hi
        rw [foldE_getD g r hi', foldE_getD l r (by rw [hl]; exact hi'), foldE_getD s r (by rw [hs]; exact hi'),
          triple_identity]
        ring
    _ = 0 := by rw [← mul_sum, hcubic, mul_zero]

/-! ## The matrices' tables: `L̂` on the low bits, `ŝ` on the high ones -/

/-- **The table depends only on its index's low `a` bits** (`L̂(x)` at `x + 2^k y`, `a = k`). -/
def LowDep (v : Array E) (a : ℕ) : Prop := ∀ i < v.size, v.getD i 0 = v.getD (i % 2 ^ a) 0

/-- **The table depends only on its index's bits from `a` up** (`ŝ(y)` at `x + 2^k y`, `a = k`). -/
def HighDep (v : Array E) (a : ℕ) : Prop := ∀ i < v.size, v.getD i 0 = v.getD (2 ^ a * (i / 2 ^ a)) 0

theorem lowDep_zero_pair {v : Array E} (h : LowDep v 0) (i : ℕ) (hi : 2 * i + 1 < v.size) :
    v.getD (2 * i) 0 + v.getD (2 * i + 1) 0 = 0 := by
  rw [h (2 * i) (by omega), h (2 * i + 1) hi]
  simp only [pow_zero, Nat.mod_one]
  exact add_self_E _

theorem div_two_pow_succ (i a : ℕ) : (2 * i + 1) / 2 ^ (a + 1) = i / 2 ^ a := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul]
  congr 1
  omega

theorem div_two_pow_succ' (i a : ℕ) : 2 * i / 2 ^ (a + 1) = i / 2 ^ a := by
  rw [pow_succ', Nat.mul_div_mul_left _ _ (by norm_num)]

theorem highDep_pair {v : Array E} {a : ℕ} (h : HighDep v (a + 1)) (i : ℕ) (hi : 2 * i + 1 < v.size) :
    v.getD (2 * i) 0 + v.getD (2 * i + 1) 0 = 0 := by
  rw [h (2 * i) (by omega), h (2 * i + 1) hi, div_two_pow_succ, div_two_pow_succ']
  exact add_self_E _

/-- **The `X³` coefficient vanishes**: in every pair either `L̂`'s or `ŝ`'s entries agree. -/
theorem cubic_zero (g l s : Array E) (a : ℕ) (hl : l.size = g.size) (hs : s.size = g.size)
    (hL : a = 0 → LowDep l 0) (hS : 0 < a → HighDep s a) :
    ∑ i ∈ range (g.size / 2), (g.getD (2 * i) 0 + g.getD (2 * i + 1) 0) *
      (l.getD (2 * i) 0 + l.getD (2 * i + 1) 0) * (s.getD (2 * i) 0 + s.getD (2 * i + 1) 0) = 0 := by
  refine sum_eq_zero fun i hi ↦ ?_
  have hi' : 2 * i + 1 < g.size := by have := mem_range.mp hi; omega
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [lowDep_zero_pair (hL rfl) i (by omega), mul_zero, zero_mul]
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [highDep_pair (hS ha) i (by omega), mul_zero]

theorem mod_two_pow_succ (i a : ℕ) : (2 * i + 1) % 2 ^ (a + 1) = 2 * (i % 2 ^ a) + 1 := by
  have hM : 0 < 2 ^ a := by positivity
  have e : 2 * i + 1 = (2 * (i % 2 ^ a) + 1) + 2 ^ (a + 1) * (i / 2 ^ a) := by
    conv_lhs => rw [← Nat.mod_add_div i (2 ^ a)]
    rw [pow_succ']
    ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mod_lt i hM
  rw [pow_succ']
  omega

theorem mod_two_pow_succ' (i a : ℕ) : 2 * i % 2 ^ (a + 1) = 2 * (i % 2 ^ a) := by
  rw [pow_succ', Nat.mul_mod_mul_left]

theorem lowDep_fold {v : Array E} {a : ℕ} (h : LowDep v (a + 1)) (heven : 2 ∣ v.size) (r : E) :
    LowDep (foldE v r) a := by
  intro i hi
  rw [foldE_size] at hi
  have hm : i % 2 ^ a < (v.size + 1) / 2 := lt_of_le_of_lt (Nat.mod_le _ _) hi
  rw [foldE_getD v r hi, foldE_getD v r hm, h (2 * i) (by omega), h (2 * i + 1) (by omega),
    mod_two_pow_succ, mod_two_pow_succ']

theorem lowDep_fold_zero {v : Array E} (h : LowDep v 0) (heven : 2 ∣ v.size) (r : E) :
    LowDep (foldE v r) 0 := by
  intro i hi
  rw [foldE_size] at hi
  have h0 : 0 < (v.size + 1) / 2 := by omega
  simp only [pow_zero, Nat.mod_one]
  rw [foldE_getD v r hi, foldE_getD v r h0, h (2 * i) (by omega), h (2 * i + 1) (by omega), h (2 * 0 + 1) (by omega)]
  simp only [pow_zero, Nat.mod_one, mul_zero]

theorem highDep_fold {v : Array E} {a : ℕ} (h : HighDep v (a + 1)) (heven : 2 ∣ v.size) (r : E) :
    HighDep (foldE v r) a := by
  intro i hi
  rw [foldE_size] at hi
  have hmi : 2 ^ a * (i / 2 ^ a) ≤ i := Nat.mul_div_le i (2 ^ a)
  have hm' : 2 ^ a * (i / 2 ^ a) < (v.size + 1) / 2 := lt_of_le_of_lt hmi hi
  have hc : 2 ^ a * (i / 2 ^ a) / 2 ^ a = i / 2 ^ a := Nat.mul_div_cancel_left _ (by positivity)
  rw [foldE_getD v r hi, foldE_getD v r hm', h (2 * i) (by omega), h (2 * i + 1) (by omega),
    h (2 * (2 ^ a * (i / 2 ^ a))) (by omega), h (2 * (2 ^ a * (i / 2 ^ a)) + 1) (by omega),
    div_two_pow_succ, div_two_pow_succ', div_two_pow_succ, div_two_pow_succ', hc]

/-! ## The rounds as pure functions -/

/-- The round's message (`batchRound`'s text): `q(0)`, and `q`'s `X²` coefficient. -/
def batchMsg (lambda : E) (j : ℕ) (st : BatchState) : E × E :=
  let n := st.tabs.length
  let (q0, q2, _) := (st.weights.zip st.tabs).foldl (fun (acc : E × E × E) (w, c) ↦
    let (a, b) := roundSums w c
    (acc.1 + acc.2.2 * a, acc.2.1 + acc.2.2 * b, acc.2.2 * lambda)) (0, 0, 1)
  let scale := UniStatement.epow lambda n
  match st.matrices with
    | some p => if j < p.rounds then
        let (a, b) := productRound p.g p.l p.s
        (q0 + scale * a, q2 + scale * b)
      else (q0 + scale * st.matrixValue, q2)
    | none => (q0, q2)

/-- The state after round `j` at the challenge `r` (`batchRound`'s text). -/
def batchNext (j : ℕ) (st : BatchState) (r : E) : BatchState :=
  let matrices := st.matrices.map fun p ↦
    if j < p.rounds then { p with g := foldE p.g r, l := foldE p.l r, s := foldE p.s r } else p
  let matrixValue := match st.matrices, matrices with
    | some p, some p' =>
      if j < p.rounds then (if j + 1 = p.rounds then p'.g.getD 0 0 * p'.l.getD 0 0 * p'.s.getD 0 0 else 0)
      else st.matrixValue * (1 + r)
    | _, _ => 0
  ⟨st.weights.map (foldE · r), st.tabs.map (foldE · r), matrices, matrixValue, st.point ++ [r]⟩

/-- **The round, unfolded**: send the message, draw `r`, the next state. -/
theorem batchRound_eq {m : Type → Type} [Monad m] (H : List UInt8 → m LeanVM.Protocol.Digest) (lambda : E)
    (j : ℕ) (st : BatchState) :
    batchRound H lambda j st = (do
      sendScalar (batchMsg lambda j st).1
      sendScalar (batchMsg lambda j st).2
      let r ← sampleW H
      pure (batchNext j st r)) := rfl

/-- The matrices' `q(0)` at round `j`: their product's before their last round, their value after. -/
def matrixQ0 (j : ℕ) (st : BatchState) : E :=
  match st.matrices with
  | some p => if j < p.rounds then (productRound p.g p.l p.s).1 else st.matrixValue
  | none => 0

/-- The matrices' `X²` coefficient at round `j`. -/
def matrixQ2 (j : ℕ) (st : BatchState) : E :=
  match st.matrices with
  | some p => if j < p.rounds then (productRound p.g p.l p.s).2 else 0
  | none => 0

theorem foldl_triple (lambda : E) (f : E × E × E → Array E × Array E → E × E × E)
    (hf : ∀ acc x, f acc x = (acc.1 + acc.2.2 * (roundSums x.1 x.2).1, acc.2.1 + acc.2.2 * (roundSums x.1 x.2).2,
      acc.2.2 * lambda)) :
    ∀ (L : List (Array E × Array E)) (a b s : E), L.foldl f (a, b, s) =
      (a + s * wsum lambda (L.map fun wc ↦ (roundSums wc.1 wc.2).1),
        b + s * wsum lambda (L.map fun wc ↦ (roundSums wc.1 wc.2).2), s * lambda ^ L.length)
  | [], a, b, s => by simp [wsum]
  | x :: L, a, b, s => by
    rw [List.foldl_cons, hf, foldl_triple lambda f hf L]
    simp only [List.map_cons, wsum, List.length_cons, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

/-- **The message**: the weighted round sums, and the matrices' at `λ^n`. -/
theorem batchMsg_eq (lambda : E) (j : ℕ) (st : BatchState) :
    batchMsg lambda j st =
      (wsum lambda ((st.weights.zip st.tabs).map fun wc ↦ (roundSums wc.1 wc.2).1) +
          lambda ^ st.tabs.length * matrixQ0 j st,
        wsum lambda ((st.weights.zip st.tabs).map fun wc ↦ (roundSums wc.1 wc.2).2) +
          lambda ^ st.tabs.length * matrixQ2 j st) := by
  unfold batchMsg
  rw [foldl_triple lambda _ (fun _ _ ↦ rfl) _ 0 0 1]
  simp only [zero_add, one_mul, epow_eq_pow]
  unfold matrixQ0 matrixQ2
  rcases st.matrices with _ | p
  · simp
  · dsimp only
    split_ifs <;> simp

/-- The verifier's claim after a round (`roundPoly 3 claim none`, then `polyEval` at `r`). -/
def claimStep (claim q0 q2 r : E) : E := UniStatement.polyEval [q0, claim + UniStatement.esum [q2], q2] r

theorem claimStep_eq (claim q0 q2 r : E) : claimStep claim q0 q2 r = q0 + (claim + q2) * r + q2 * r ^ 2 := by
  simp only [claimStep, UniStatement.polyEval, UniStatement.esum, List.foldl_cons, List.foldl_nil,
    List.foldr_cons, List.foldr_nil]
  ring

/-- The matrices' part of the running claim at round `j`: their product sum before their last round, their value
after. -/
def matrixPart (j : ℕ) (st : BatchState) : E :=
  match st.matrices with
  | some p => if j < p.rounds then prod3 p.g p.l p.s else st.matrixValue
  | none => 0

/-- **The running claim** at round `j`: the batched pairings of the current tables, the matrices' at `λ^n`. -/
def batchClaim (lambda : E) (j : ℕ) (st : BatchState) : E :=
  wsum lambda ((st.weights.zip st.tabs).map fun wc ↦ dotE wc.1 wc.2) + lambda ^ st.tabs.length * matrixPart j st

/-- **The state's shape at round `j`**: as many weights as tables, each pair of one size; before the matrices'
last round, their three tables of `2^(rounds − j)` entries, `L̂` on the low `k − j` bits, `ŝ` on the others. -/
structure RoundWF (k j : ℕ) (st : BatchState) : Prop where
  length : st.weights.length = st.tabs.length
  sizes : ∀ wc ∈ st.weights.zip st.tabs, wc.1.size = wc.2.size
  matrices : ∀ t, st.matrices = some t → j < t.rounds →
    t.g.size = 2 ^ (t.rounds - j) ∧ t.l.size = 2 ^ (t.rounds - j) ∧ t.s.size = 2 ^ (t.rounds - j) ∧
      (k - j = 0 → LowDep t.l 0) ∧ (0 < k - j → LowDep t.l (k - j) ∧ HighDep t.s (k - j))

theorem prod3_one (g l s : Array E) (h : g.size = 1) :
    prod3 g l s = g.getD 0 0 * l.getD 0 0 * s.getD 0 0 := by
  simp [prod3, h]

/-- **One round**: from the running claim, the verifier's next claim is the next state's running claim. -/
theorem batch_round (lambda r : E) (k j : ℕ) (st : BatchState) (hwf : RoundWF k j st) :
    claimStep (batchClaim lambda j st) (batchMsg lambda j st).1 (batchMsg lambda j st).2 r =
      batchClaim lambda (j + 1) (batchNext j st r) := by
  rw [batchMsg_eq lambda j st, claimStep_eq]
  unfold batchClaim
  have hw : (batchNext j st r).weights = st.weights.map (foldE · r) := rfl
  have ht : (batchNext j st r).tabs = st.tabs.map (foldE · r) := rfl
  rw [hw, ht, List.length_map, List.zip_map, List.map_map]
  have hpairs : wsum lambda ((st.weights.zip st.tabs).map fun wc ↦ (roundSums wc.1 wc.2).1) +
      (wsum lambda ((st.weights.zip st.tabs).map fun wc ↦ dotE wc.1 wc.2) +
        wsum lambda ((st.weights.zip st.tabs).map fun wc ↦ (roundSums wc.1 wc.2).2)) * r +
      wsum lambda ((st.weights.zip st.tabs).map fun wc ↦ (roundSums wc.1 wc.2).2) * r ^ 2 =
      wsum lambda ((st.weights.zip st.tabs).map
        ((fun wc ↦ dotE wc.1 wc.2) ∘ Prod.map (fun x ↦ foldE x r) fun x ↦ foldE x r)) := by
    rw [wsum_comb]
    refine wsum_congr _ _ _ _ fun wc hwc ↦ ?_
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    rw [dotE_foldE wc.1 wc.2 (hwf.sizes wc hwc)]
  have hmat : matrixQ0 j st + (matrixPart j st + matrixQ2 j st) * r + matrixQ2 j st * r ^ 2 =
      matrixPart (j + 1) (batchNext j st r) := by
    unfold matrixQ0 matrixQ2 matrixPart batchNext
    rcases hm : st.matrices with _ | t
    · simp
    · simp only [Option.map_some]
      by_cases hj : j < t.rounds
      · obtain ⟨hg, hl, hs, hL0, hLS⟩ := hwf.matrices t hm hj
        have heven : 2 ∣ t.g.size := by
          rw [hg]
          exact dvd_pow_self 2 (by omega)
        simp only [hj, ite_true]
        have hcubic := cubic_zero t.g t.l t.s (k - j) (by rw [hl, hg]) (by rw [hs, hg]) hL0
          (fun h ↦ (hLS h).2)
        rw [← prod3_foldE t.g t.l t.s (by rw [hl, hg]) (by rw [hs, hg]) heven hcubic r]
        by_cases hj1 : j + 1 < t.rounds
        · simp only [hj1, ite_true]
        · rw [prod3_one _ _ _ (by rw [foldE_size, hg, show t.rounds - j = 1 by omega]; norm_num)]
          simp only [show j + 1 = t.rounds by omega, lt_self_iff_false, ite_true, ite_false]
      · simp only [hj, ite_false, show ¬ j + 1 < t.rounds by omega]
        ring
  rw [← hpairs, ← hmat]
  ring

/-- **The shape is kept** by a round. -/
theorem batch_round_wf (r : E) (k j : ℕ) (st : BatchState) (hwf : RoundWF k j st) :
    RoundWF k (j + 1) (batchNext j st r) := by
  refine ⟨by simp [batchNext, hwf.length], fun wc hwc ↦ ?_, fun t ht hj ↦ ?_⟩
  · simp only [batchNext, List.zip_map, List.mem_map] at hwc
    obtain ⟨x, hx, rfl⟩ := hwc
    simp [foldE_size, hwf.sizes x hx]
  · simp only [batchNext] at ht
    rcases hm : st.matrices with _ | t0
    · rw [hm] at ht; simp at ht
    · rw [hm] at ht
      simp only [Option.map_some, Option.some.injEq] at ht
      have hj0 : j < t0.rounds := by
        by_contra h
        rw [ite_neg h] at ht
        subst ht
        omega
      rw [ite_pos hj0] at ht
      subst ht
      obtain ⟨hg, hl, hs, hL0, hLS⟩ := hwf.matrices t0 hm hj0
      dsimp only at hj ⊢
      have hsz : ∀ v : Array E, v.size = 2 ^ (t0.rounds - j) → (foldE v r).size = 2 ^ (t0.rounds - (j + 1)) := by
        intro v hv
        rw [foldE_size, hv, show t0.rounds - j = t0.rounds - (j + 1) + 1 by omega, pow_succ]
        omega
      have hev : ∀ v : Array E, v.size = 2 ^ (t0.rounds - j) → 2 ∣ v.size := fun v hv ↦ by
        rw [hv]; exact dvd_pow_self 2 (by omega)
      refine ⟨hsz _ hg, hsz _ hl, hsz _ hs, fun h0 ↦ ?_, fun hpos ↦ ?_⟩
      · rcases Nat.eq_zero_or_pos (k - j) with h | h
        · exact lowDep_fold_zero (hL0 h) (hev _ hl) r
        · have := (hLS h).1
          rw [show k - j = 0 + 1 by omega] at this
          exact lowDep_fold this (hev _ hl) r
      · obtain ⟨hL, hS⟩ := hLS (by omega)
        rw [show k - j = k - (j + 1) + 1 by omega] at hL hS
        exact ⟨lowDep_fold hL (hev _ hl) r, highDep_fold hS (hev _ hs) r⟩

/-! ## The rounds -/

/-- The states through the rounds `j, j + 1, …` at the challenges `rs`. -/
def batchRun : ℕ → List E → BatchState → BatchState
  | _, [], st => st
  | j, r :: rs, st => batchRun (j + 1) rs (batchNext j st r)

/-- The verifier's claims through the rounds on the prover's messages, at the challenges `rs`. -/
def claimRun (lambda : E) : ℕ → List E → BatchState → E → E
  | _, [], _, c => c
  | j, r :: rs, st, c =>
    claimRun lambda (j + 1) rs (batchNext j st r) (claimStep c (batchMsg lambda j st).1 (batchMsg lambda j st).2 r)

/-- **The rounds keep the running claim**. -/
theorem claimRun_eq (lambda : E) (k : ℕ) : ∀ (rs : List E) (j : ℕ) (st : BatchState), RoundWF k j st →
    claimRun lambda j rs st (batchClaim lambda j st) = batchClaim lambda (j + rs.length) (batchRun j rs st)
  | [], j, st, _ => by simp [claimRun, batchRun]
  | r :: rs, j, st, hwf => by
    simp only [claimRun, batchRun, List.length_cons]
    rw [batch_round lambda r k j st hwf, claimRun_eq lambda k rs (j + 1) _ (batch_round_wf r k j st hwf),
      show j + 1 + rs.length = j + (rs.length + 1) by omega]

theorem batchRun_weights : ∀ (rs : List E) (j : ℕ) (st : BatchState),
    (batchRun j rs st).weights = st.weights.map (fun w ↦ rs.foldl foldE w)
  | [], _, st => by simp [batchRun]
  | r :: rs, j, st => by
    rw [batchRun, batchRun_weights rs]
    show (st.weights.map (foldE · r)).map _ = _
    simp [List.map_map, Function.comp_def]

theorem batchRun_tabs : ∀ (rs : List E) (j : ℕ) (st : BatchState),
    (batchRun j rs st).tabs = st.tabs.map (fun w ↦ rs.foldl foldE w)
  | [], _, st => by simp [batchRun]
  | r :: rs, j, st => by
    rw [batchRun, batchRun_tabs rs]
    show (st.tabs.map (foldE · r)).map _ = _
    simp [List.map_map, Function.comp_def]

/-- Past the matrices' rounds their tables stay, and their value gains `(1 + r)` a round. -/
theorem batchRun_after (t : PendingTables) : ∀ (rs : List E) (j : ℕ) (st : BatchState), st.matrices = some t →
    t.rounds ≤ j →
    (batchRun j rs st).matrices = some t ∧
      (batchRun j rs st).matrixValue = st.matrixValue * (rs.map (1 + ·)).prod
  | [], _, st, h, _ => by simp [batchRun, h]
  | r :: rs, j, st, h, hj => by
    have hn : (batchNext j st r).matrices = some t := by
      simp [batchNext, h, show ¬ j < t.rounds by omega]
    have hv : (batchNext j st r).matrixValue = st.matrixValue * (1 + r) := by
      simp [batchNext, h, show ¬ j < t.rounds by omega]
    rw [batchRun]
    obtain ⟨h1, h2⟩ := batchRun_after t rs (j + 1) _ hn (by omega)
    refine ⟨h1, ?_⟩
    rw [h2, hv, List.map_cons, List.prod_cons]
    ring

/-- **The matrices' rounds**: from round `j`, `m = rounds − j ≥ 1` rounds left, the tables fold `m` times, and the
value is then their product times `(1 + r)` a round. -/
theorem batchRun_matrices : ∀ (rs : List E) (j : ℕ) (st : BatchState) (t : PendingTables),
    st.matrices = some t → j < t.rounds → t.rounds - j ≤ rs.length →
    (batchRun j rs st).matrices = some ⟨(rs.take (t.rounds - j)).foldl foldE t.g,
      (rs.take (t.rounds - j)).foldl foldE t.l, (rs.take (t.rounds - j)).foldl foldE t.s, t.rounds⟩ ∧
    (batchRun j rs st).matrixValue = ((rs.take (t.rounds - j)).foldl foldE t.g).getD 0 0 *
      ((rs.take (t.rounds - j)).foldl foldE t.l).getD 0 0 * ((rs.take (t.rounds - j)).foldl foldE t.s).getD 0 0 *
      ((rs.drop (t.rounds - j)).map (1 + ·)).prod
  | [], _, _, _, _, hj, hm => by simp at hm; omega
  | r :: rs, j, st, t, h, hj, hm => by
    have hn : (batchNext j st r).matrices = some ⟨foldE t.g r, foldE t.l r, foldE t.s r, t.rounds⟩ := by
      simp [batchNext, h, hj]
    rw [batchRun]
    by_cases hj1 : j + 1 = t.rounds
    · have hv : (batchNext j st r).matrixValue =
          (foldE t.g r).getD 0 0 * (foldE t.l r).getD 0 0 * (foldE t.s r).getD 0 0 := by
        simp [batchNext, h, hj, hj1]
      obtain ⟨h1, h2⟩ := batchRun_after _ rs (j + 1) _ hn (by dsimp only; omega)
      rw [h1, h2, hv, show t.rounds - j = 0 + 1 by omega]
      simp
    · obtain ⟨h1, h2⟩ := batchRun_matrices rs (j + 1) _ ⟨foldE t.g r, foldE t.l r, foldE t.s r, t.rounds⟩ hn
        (by dsimp only; omega) (by dsimp only; simp at hm; omega)
      dsimp only at h1 h2
      rw [h1, h2, show t.rounds - j = t.rounds - (j + 1) + 1 by omega, List.take_succ_cons, List.drop_succ_cons]
      simp only [List.foldl_cons, and_self]

/-! ## The tables at the end -/

/-- A table's multilinear extension at a point (low coordinate first, `multilinearEval`). -/
def tableEval (v : Array E) (pt : List E) : E := UniStatement.multilinearEval v.toList pt

/-- The zero extension's factor past `d` variables: `Π_{j ≥ d} (1 + r_j)`. -/
def extOf (r : List E) (d : ℕ) : E := ((r.drop d).map (1 + ·)).prod

theorem foldE_eq_foldOnce (v : Array E) (r : E) (h : 2 ∣ v.size) : foldE v r = UniStatement.foldOnce v r := by
  apply Array.ext
  · rw [foldE_size, foldOnce_size]; omega
  · intro i _ _
    simp [foldE, UniStatement.foldOnce]

theorem foldE_run_pow : ∀ (pt : List E) (v : Array E), v.size = 2 ^ pt.length →
    pt.foldl foldE v = pt.foldl UniStatement.foldOnce v ∧ (pt.foldl foldE v).size = 1
  | [], v, h => ⟨rfl, by simpa using h⟩
  | r :: pt, v, h => by
    have hd : 2 ∣ v.size := by rw [h, List.length_cons, pow_succ]; exact Dvd.intro_left _ rfl
    have hs : (UniStatement.foldOnce v r).size = 2 ^ pt.length := by
      rw [foldOnce_size, h, List.length_cons, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [List.foldl_cons, List.foldl_cons, foldE_eq_foldOnce v r hd]
    exact foldE_run_pow pt _ hs

theorem foldE_run_one : ∀ (rs : List E) (v : Array E), v.size = 1 →
    (rs.foldl foldE v).size = 1 ∧ (rs.foldl foldE v).getD 0 0 = v.getD 0 0 * (rs.map (1 + ·)).prod
  | [], v, h => ⟨h, by simp⟩
  | r :: rs, v, h => by
    have hs : (foldE v r).size = 1 := by rw [foldE_size, h]
    have hg : (foldE v r).getD 0 0 = v.getD 0 0 * (1 + r) := by
      rw [foldE_getD v r (by rw [h]; norm_num), getD_ge v (i := 2 * 0 + 1) (by rw [h])]
      simp only [mul_zero, add_zero]
      ring
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldE_run_one rs _ hs
    refine ⟨h1, ?_⟩
    rw [h2, hg, List.map_cons, List.prod_cons]
    ring

/-- **A table of `2^d` entries folded by `rs`** (`d ≤ |rs|`): one entry, its multilinear extension at `r_{<d}`
times `Π_{j ≥ d} (1 + r_j)`. -/
theorem foldE_run (v : Array E) (d : ℕ) (hv : v.size = 2 ^ d) (rs : List E) (hd : d ≤ rs.length) :
    (rs.foldl foldE v).size = 1 ∧ (rs.foldl foldE v).getD 0 0 = tableEval v (rs.take d) * extOf rs d := by
  have hl : (rs.take d).length = d := by simp [hd]
  obtain ⟨h1, h2⟩ := foldE_run_pow (rs.take d) v (by rw [hl, hv])
  have hsplit : rs.foldl foldE v = (rs.drop d).foldl foldE ((rs.take d).foldl foldE v) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [hsplit]
  obtain ⟨h3, h4⟩ := foldE_run_one (rs.drop d) _ h2
  refine ⟨h3, ?_⟩
  rw [h4, h1]
  simp [tableEval, UniStatement.multilinearEval, extOf]

/-! ## The honest sumcheck -/

/-- **The batch's tables**: each stack's weight and words of `2^d` entries, `d ≤ vars`; the matrices' three tables of
`2^rounds` entries, `1 ≤ rounds ≤ vars`, `L̂` on the low `k` bits and `ŝ` on the others. -/
structure BatchWF (k vars : ℕ) (pairs : List (Array E × Array E × ℕ)) (tables : Option PendingTables) : Prop where
  pairs : ∀ p ∈ pairs, p.1.size = 2 ^ p.2.2 ∧ p.2.1.size = 2 ^ p.2.2 ∧ p.2.2 ≤ vars
  tables : ∀ t, tables = some t → 0 < t.rounds ∧ t.rounds ≤ vars ∧ t.g.size = 2 ^ t.rounds ∧
    t.l.size = 2 ^ t.rounds ∧ t.s.size = 2 ^ t.rounds ∧ (k = 0 → LowDep t.l 0) ∧ (0 < k → LowDep t.l k ∧ HighDep t.s k)

/-- The prover's state before the rounds (`proveStreamWith`'s step 9). -/
def initState (pairs : List (Array E × Array E × ℕ)) (tables : Option PendingTables) : BatchState :=
  ⟨pairs.map (·.1), pairs.map (·.2.1), tables, 0, []⟩

/-- **The sumcheck's target**: `Σ_k λ^k Σ_u W_k C_k + λ^n Σ G L̂ ŝ`. -/
def targetOf (lambda : E) (pairs : List (Array E × Array E × ℕ)) (tables : Option PendingTables) : E :=
  wsum lambda (pairs.map fun p ↦ dotE p.1 p.2.1) + lambda ^ pairs.length *
    (match tables with
      | some t => prod3 t.g t.l t.s
      | none => 0)

/-- **The sumcheck's terminal**: `Σ_k λ^k W̃_k(r) C̃_k(r) Π_{j ≥ d_k} (1 + r_j)² + λ^n G̃ L̃ S̃(r) Π_{j ≥ rounds} (1 + r_j)`. -/
def terminalOf (lambda : E) (pairs : List (Array E × Array E × ℕ)) (tables : Option PendingTables) (r : List E) : E :=
  wsum lambda (pairs.map fun p ↦ tableEval p.1 (r.take p.2.2) * tableEval p.2.1 (r.take p.2.2) * extOf r p.2.2 ^ 2) +
    lambda ^ pairs.length *
      (match tables with
        | some t => tableEval t.g (r.take t.rounds) * tableEval t.l (r.take t.rounds) *
            tableEval t.s (r.take t.rounds) * extOf r t.rounds
        | none => 0)

theorem initState_wf (k vars : ℕ) (pairs : List (Array E × Array E × ℕ)) (tables : Option PendingTables)
    (hwf : BatchWF k vars pairs tables) : RoundWF k 0 (initState pairs tables) := by
  refine ⟨by simp [initState], fun wc hwc ↦ ?_, fun t ht _ ↦ ?_⟩
  · simp only [initState, List.zip_map', List.mem_map] at hwc
    obtain ⟨p, hp, rfl⟩ := hwc
    obtain ⟨h1, h2, -⟩ := hwf.pairs p hp
    simp [h1, h2]
  · obtain ⟨-, -, hg, hl, hs, hL0, hLS⟩ := hwf.tables t ht
    simp only [Nat.sub_zero]
    exact ⟨hg, hl, hs, hL0, hLS⟩

theorem targetOf_eq (lambda : E) (k vars : ℕ) (pairs : List (Array E × Array E × ℕ))
    (tables : Option PendingTables) (hwf : BatchWF k vars pairs tables) :
    targetOf lambda pairs tables = batchClaim lambda 0 (initState pairs tables) := by
  unfold targetOf batchClaim matrixPart initState
  dsimp only
  rw [List.zip_map', List.map_map, List.length_map]
  congr 2
  rcases tables with _ | t
  · rfl
  · dsimp only
    rw [ite_pos (hwf.tables t rfl).1]

/-- **The honest batching sumcheck**: over `vars` rounds at any challenges `rs`, from the target, the verifier's last
claim on the prover's messages is the terminal. -/
theorem batch_rounds (lambda : E) (k vars : ℕ) (pairs : List (Array E × Array E × ℕ))
    (tables : Option PendingTables) (hwf : BatchWF k vars pairs tables) (rs : List E) (hrs : rs.length = vars) :
    claimRun lambda 0 rs (initState pairs tables) (targetOf lambda pairs tables) = terminalOf lambda pairs tables rs := by
  rw [targetOf_eq lambda k vars pairs tables hwf, claimRun_eq lambda k rs 0 _ (initState_wf k vars pairs tables hwf),
    zero_add]
  have hw : (batchRun 0 rs (initState pairs tables)).weights = pairs.map fun p ↦ rs.foldl foldE p.1 := by
    rw [batchRun_weights]
    simp [initState, List.map_map, Function.comp_def]
  have ht : (batchRun 0 rs (initState pairs tables)).tabs = pairs.map fun p ↦ rs.foldl foldE p.2.1 := by
    rw [batchRun_tabs]
    simp [initState, List.map_map, Function.comp_def]
  have hzip : ((batchRun 0 rs (initState pairs tables)).weights.zip (batchRun 0 rs (initState pairs tables)).tabs).map
      (fun wc ↦ dotE wc.1 wc.2) = pairs.map fun p ↦ dotE (rs.foldl foldE p.1) (rs.foldl foldE p.2.1) := by
    rw [hw, ht, List.zip_map', List.map_map]
    rfl
  have hlen : (batchRun 0 rs (initState pairs tables)).tabs.length = pairs.length := by
    rw [ht, List.length_map]
  have hpairs : wsum lambda (pairs.map fun p ↦ dotE (rs.foldl foldE p.1) (rs.foldl foldE p.2.1)) =
      wsum lambda (pairs.map fun p ↦
        tableEval p.1 (rs.take p.2.2) * tableEval p.2.1 (rs.take p.2.2) * extOf rs p.2.2 ^ 2) := by
    refine wsum_congr _ _ _ _ fun p hp ↦ ?_
    obtain ⟨h1, h2, h3⟩ := hwf.pairs p hp
    obtain ⟨s1, g1⟩ := foldE_run p.1 p.2.2 h1 rs (by omega)
    obtain ⟨-, g2⟩ := foldE_run p.2.1 p.2.2 h2 rs (by omega)
    simp only [dotE, s1, range_one, sum_singleton, g1, g2]
    ring
  have hmat : matrixPart rs.length (batchRun 0 rs (initState pairs tables)) =
      (match tables with
        | some t => tableEval t.g (rs.take t.rounds) * tableEval t.l (rs.take t.rounds) *
            tableEval t.s (rs.take t.rounds) * extOf rs t.rounds
        | none => 0) := by
    rcases tables with _ | t
    · have hnone : ∀ (rs : List E) (j : ℕ) (st : BatchState), st.matrices = none →
          (batchRun j rs st).matrices = none := by
        intro rs
        induction rs with
        | nil => intro j st h; simpa [batchRun] using h
        | cons r rs ih => intro j st h; exact ih (j + 1) _ (by simp [batchNext, h])
      simp [matrixPart, hnone rs 0 (initState pairs none) rfl]
    · obtain ⟨h0, hR, hg, hl, hs, -, -⟩ := hwf.tables t rfl
      obtain ⟨h1, h2⟩ := batchRun_matrices rs 0 (initState pairs (some t)) t rfl h0 (by omega)
      have hev : ∀ v : Array E, v.size = 2 ^ t.rounds →
          ((rs.take t.rounds).foldl foldE v).getD 0 0 = tableEval v (rs.take t.rounds) := by
        intro v hv
        obtain ⟨-, e⟩ := foldE_run v t.rounds hv (rs.take t.rounds) (by simp; omega)
        rw [e, List.take_take, min_self]
        simp [extOf, List.drop_eq_nil_of_le (by simp : (rs.take t.rounds).length ≤ t.rounds)]
      unfold matrixPart
      rw [h1]
      dsimp only
      rw [ite_neg (by omega), h2, Nat.sub_zero, hev _ hg, hev _ hl, hev _ hs]
      rfl
  unfold batchClaim terminalOf
  rw [hzip, hlen, hpairs, hmat]

end UniComplete

/-- info: 'UniComplete.batch_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.batch_rounds

/-- info: 'UniComplete.batch_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.batch_round
