-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.FlockProverRing

/-!
# The honest rounds keep the verifier's claim: the zerocheck's and the lincheck's sumchecks are complete

The prover tracks the verifier's claim (`roundPoly`'s arithmetic) through its rounds. Here, for any challenges:

* **`zcRounds_complete`**: if the zerocheck's claim is `Σ_i eq(r, i) (a_i b_i + c_i)` over tables of `2^|r|` entries,
  then after the eq-factored rounds (low variable first) `v_a`, `v_b` are the folded tables' values and the last claim
  is `v_a v_b + ĉ` (`ĉ` the folded `c`): each round's `(c1, c2)` with the verifier's
  `c0 = claim + r (c1 + c2)` is the quadratic `Σ_i eq(r_{>j}, i) (a b' + c)(X, i)` (`zc_round_claim`, characteristic
  two);
* **`lcRounds_complete`**: if the lincheck's claim is `Σ_i w_i z_i` over tables of `2^(n + j)` entries, after `n`
  rounds (high variable first) the last claim is `Σ_{i < 2^j} w'_i z'_i` of the folded tables
  (`lc_round_claim`: `c0 + (claim + c2) X + c2 X²` is `Σ w'(X) z'(X)`).
-/

namespace UniComplete.FlockP

open UniStatement UniStatement.Flock LeanVM.Parameters Finset

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- Pairs of sums as one fold. -/
theorem foldl_pair_sum (n : ℕ) (f g : ℕ → E) :
    (List.range n).foldl (fun (acc : E × E) i ↦ (acc.1 + f i, acc.2 + g i)) (0, 0) =
      (∑ i ∈ range n, f i, ∑ i ∈ range n, g i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [sum_range_succ]

theorem polyEval_three (p0 p1 p2 x : E) : polyEval [p0, p1, p2] x = p0 + p1 * x + p2 * x ^ 2 := by
  simp only [polyEval, List.foldr_cons, List.foldr_nil]
  ring

theorem foldE_size' (v : Array E) (x : E) : (foldE v x).size = (v.size + 1) / 2 := by
  simp [foldE]

theorem foldE_getD' (v : Array E) (x : E) {i : ℕ} (hi : i < (v.size + 1) / 2) :
    (foldE v x).getD i 0 = v.getD (2 * i) 0 + x * (v.getD (2 * i) 0 + v.getD (2 * i + 1) 0) := by
  rw [foldE, E2ECompleteness.getD_ofFn' _ hi]

/-! ## The rounds' identities, over any ring of characteristic two

Stated over a generic commutative ring with `2 = 0` and instantiated at `E`: the kernel checks the `ring` proofs once,
abstractly (over `E` itself, numerals in its `ring` certificates made the kernel's check time out). -/

/-- **The eq-factored round's identity**: `claim + r0 (c1 + c2) + c1 x + c2 x²` is the folded tables' sum. -/
theorem zc_claim_generic {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (n : ℕ) (r0 x : R)
    (e e' a0 a1 b0 b1 c0 c1 fa fb fc : ℕ → R)
    (he : ∀ i < n, e' i = e i) (hfa : ∀ i < n, fa i = a0 i + x * (a0 i + a1 i))
    (hfb : ∀ i < n, fb i = b0 i + x * (b0 i + b1 i)) (hfc : ∀ i < n, fc i = c0 i + x * (c0 i + c1 i)) :
    (∑ i ∈ range n, ((1 + r0) * e i * (a0 i * b0 i + c0 i) + r0 * e i * (a1 i * b1 i + c1 i))) +
          r0 * (∑ i ∈ range n, e' i * (a0 i * (b0 i + b1 i) + (a0 i + a1 i) * b0 i + (c0 i + c1 i)) +
            ∑ i ∈ range n, e' i * ((a0 i + a1 i) * (b0 i + b1 i))) +
        (∑ i ∈ range n, e' i * (a0 i * (b0 i + b1 i) + (a0 i + a1 i) * b0 i + (c0 i + c1 i))) * x +
      (∑ i ∈ range n, e' i * ((a0 i + a1 i) * (b0 i + b1 i))) * x ^ 2 =
    ∑ i ∈ range n, e i * (fa i * fb i + fc i) := by
  simp only [mul_sum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [he i hi', hfa i hi', hfb i hi', hfc i hi']
  linear_combination (r0 * e i * (2 * a0 i * b0 i + c0 i + a1 i * b1 i + c1 i + a0 i * b1 i + a1 i * b0 i)) * h2

/-- **The lincheck round's identity**: `c0 + (claim + c2) x + c2 x²` is the folded tables' sum. -/
theorem lc_claim_generic {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (n : ℕ) (x : R)
    (w0 w1 w1' z0 z1 z1' fw fz : ℕ → R) (hw1 : ∀ i < n, w1' i = w1 i) (hz1 : ∀ i < n, z1' i = z1 i)
    (hfw : ∀ i < n, fw i = (1 + x) * w0 i + x * w1 i) (hfz : ∀ i < n, fz i = (1 + x) * z0 i + x * z1 i) :
    ∑ i ∈ range n, w0 i * z0 i +
        (∑ i ∈ range n, w0 i * z0 i + ∑ i ∈ range n, w1' i * z1' i +
          ∑ i ∈ range n, (w0 i + w1 i) * (z0 i + z1 i)) * x +
      (∑ i ∈ range n, (w0 i + w1 i) * (z0 i + z1 i)) * x ^ 2 =
    ∑ i ∈ range n, fw i * fz i := by
  simp only [mul_sum, sum_mul, ← sum_add_distrib, add_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [hw1 i hi', hz1 i hi', hfw i hi', hfz i hi']
  linear_combination (x * w1 i * z1 i) * h2

/-! ## The zerocheck's rounds -/

/-- `zcRound` as its two sums. -/
theorem zcRound_eq (eqRest a b c : Array E) :
    zcRound eqRest a b c =
      (∑ i ∈ range eqRest.size, eqRest.getD i 0 * (a.getD (2 * i) 0 * (b.getD (2 * i) 0 + b.getD (2 * i + 1) 0) +
          (a.getD (2 * i) 0 + a.getD (2 * i + 1) 0) * b.getD (2 * i) 0 + (c.getD (2 * i) 0 + c.getD (2 * i + 1) 0)),
        ∑ i ∈ range eqRest.size, eqRest.getD i 0 * ((a.getD (2 * i) 0 + a.getD (2 * i + 1) 0) *
          (b.getD (2 * i) 0 + b.getD (2 * i + 1) 0))) :=
  foldl_pair_sum _ _ _

theorem polyEval_cons2 (p0 p1 p2 x : E) : polyEval ([p0] ++ [p1, p2]) x = p0 + p1 * x + p2 * x ^ 2 := by
  rw [List.singleton_append, polyEval_three]

theorem esum_two (c1 c2 : E) : esum [c1, c2] = c1 + c2 := by
  simp only [esum, List.foldl_cons, List.foldl_nil, zero_add]

/-- The eq-factored round's identity, the claim's eq weights given as functions. -/
theorem zc_claim_generic' {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (n : ℕ) (r0 x : R)
    (e e' E0 E1 a0 a1 b0 b1 c0 c1 fa fb fc : ℕ → R) (hE0 : ∀ i < n, E0 i = (1 + r0) * e i)
    (hE1 : ∀ i < n, E1 i = r0 * e i)
    (he : ∀ i < n, e' i = e i) (hfa : ∀ i < n, fa i = a0 i + x * (a0 i + a1 i))
    (hfb : ∀ i < n, fb i = b0 i + x * (b0 i + b1 i)) (hfc : ∀ i < n, fc i = c0 i + x * (c0 i + c1 i)) :
    (∑ i ∈ range n, (E0 i * (a0 i * b0 i + c0 i) + E1 i * (a1 i * b1 i + c1 i))) +
          r0 * (∑ i ∈ range n, e' i * (a0 i * (b0 i + b1 i) + (a0 i + a1 i) * b0 i + (c0 i + c1 i)) +
            ∑ i ∈ range n, e' i * ((a0 i + a1 i) * (b0 i + b1 i))) +
        (∑ i ∈ range n, e' i * (a0 i * (b0 i + b1 i) + (a0 i + a1 i) * b0 i + (c0 i + c1 i))) * x +
      (∑ i ∈ range n, e' i * ((a0 i + a1 i) * (b0 i + b1 i))) * x ^ 2 =
    ∑ i ∈ range n, e i * (fa i * fb i + fc i) := by
  simp only [mul_sum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  rw [hE0 i hi', hE1 i hi', he i hi', hfa i hi', hfb i hi', hfc i hi']
  linear_combination (r0 * e i * (2 * a0 i * b0 i + c0 i + a1 i * b1 i + c1 i + a0 i * b1 i + a1 i * b0 i)) * h2

/-- **One eq-factored round keeps the claim**: from `claim = Σ_i eq(r0 :: rest, i) (a b + c)_i`, the verifier's
`polyEval ([claim + r0 (c1 + c2)] ++ [c1, c2]) x` is `Σ_i eq(rest, i) (a' b' + c')_i` of the tables folded at `x`. -/
theorem zc_round_claim (r0 : E) (rest : List E) (claim x : E) (a b c : Array E)
    (ha : a.size = 2 ^ (rest.length + 1)) (hb : b.size = 2 ^ (rest.length + 1)) (hc : c.size = 2 ^ (rest.length + 1))
    (hclaim : claim = ∑ i ∈ range (2 ^ (rest.length + 1)),
      eqB (r0 :: rest) i * (a.getD i 0 * b.getD i 0 + c.getD i 0)) :
    polyEval ([claim + r0 * esum [(zcRound (eqKernel rest) a b c).1, (zcRound (eqKernel rest) a b c).2]] ++
        [(zcRound (eqKernel rest) a b c).1, (zcRound (eqKernel rest) a b c).2]) x =
      ∑ i ∈ range (2 ^ rest.length),
        eqB rest i * ((foldE a x).getD i 0 * (foldE b x).getD i 0 + (foldE c x).getD i 0) := by
  have hhalf : ∀ (v : Array E), v.size = 2 ^ (rest.length + 1) → (v.size + 1) / 2 = 2 ^ rest.length := by
    intro v hv; rw [hv, pow_succ]; omega
  rw [zcRound_eq, eqKernel_size, hclaim, pow_succ', UniComplete.sum_range_two_mul, polyEval_cons2, esum_two]
  exact zc_claim_generic' two_eq_zero_E (2 ^ rest.length) r0 x (fun i ↦ eqB rest i)
    (fun i ↦ (eqKernel rest).getD i 0) (fun i ↦ eqB (r0 :: rest) (2 * i)) (fun i ↦ eqB (r0 :: rest) (2 * i + 1))
    (fun i ↦ a.getD (2 * i) 0) (fun i ↦ a.getD (2 * i + 1) 0)
    (fun i ↦ b.getD (2 * i) 0) (fun i ↦ b.getD (2 * i + 1) 0) (fun i ↦ c.getD (2 * i) 0)
    (fun i ↦ c.getD (2 * i + 1) 0) (fun i ↦ (foldE a x).getD i 0) (fun i ↦ (foldE b x).getD i 0)
    (fun i ↦ (foldE c x).getD i 0) (fun i _ ↦ eqB_cons_even r0 rest i) (fun i _ ↦ eqB_cons_odd r0 rest i)
    (fun i hi ↦ eqKernel_getD _ hi)
    (fun i hi ↦ foldE_getD' a x (by rw [hhalf a ha]; exact hi))
    (fun i hi ↦ foldE_getD' b x (by rw [hhalf b hb]; exact hi))
    (fun i hi ↦ foldE_getD' c x (by rw [hhalf c hc]; exact hi))

/-- **The zerocheck's rounds are complete**: from `claim = Σ_i eq(r, i) (a b + c)_i` (tables of `2^|r|` entries),
`v_a`, `v_b` are the folded tables' values and the last claim is `v_a v_b + ĉ`. -/
theorem zcRounds_complete (H : List UInt8 → Id LeanVM.Protocol.Digest) :
    ∀ (r : List E) (claim : E) (a b c : Array E) (w : Wr),
      a.size = 2 ^ r.length → b.size = 2 ^ r.length → c.size = 2 ^ r.length →
      claim = ∑ i ∈ range (2 ^ r.length), eqB r i * (a.getD i 0 * b.getD i 0 + c.getD i 0) →
      ((zcRounds H r claim a b c).run w).1.va = (((zcRounds H r claim a b c).run w).1.chi.foldl foldE a).getD 0 0 ∧
      ((zcRounds H r claim a b c).run w).1.vb = (((zcRounds H r claim a b c).run w).1.chi.foldl foldE b).getD 0 0 ∧
      ((zcRounds H r claim a b c).run w).1.running =
        ((zcRounds H r claim a b c).run w).1.va * ((zcRounds H r claim a b c).run w).1.vb +
          (((zcRounds H r claim a b c).run w).1.chi.foldl foldE c).getD 0 0
  | [], claim, a, b, c, w, _, _, _, hclaim => by
    refine ⟨rfl, rfl, ?_⟩
    show claim = a.getD 0 0 * b.getD 0 0 + c.getD 0 0
    rw [hclaim]
    simp
  | r0 :: rest, claim, a, b, c, w, ha, hb, hc, hclaim => by
    have hhalf : ∀ (v : Array E), v.size = 2 ^ (rest.length + 1) → (foldE v (0 : E)).size = 2 ^ rest.length := by
      intro v hv; rw [foldE_size', hv, pow_succ]; omega
    have hsz : ∀ (v : Array E) (x : E), v.size = 2 ^ (rest.length + 1) → (foldE v x).size = 2 ^ rest.length := by
      intro v x hv; rw [foldE_size', hv, pow_succ]; omega
    simp only [List.length_cons] at ha hb hc hclaim
    simp only [zcRounds, run_bind_id, run_pure_id, List.foldl_cons]
    exact zcRounds_complete H rest _ _ _ _ _ (hsz a _ ha) (hsz b _ hb) (hsz c _ hc)
      (zc_round_claim r0 rest claim _ a b c ha hb hc hclaim)


/-! ## The lincheck's rounds -/

/-- `lcRound` as its two sums. -/
theorem lcRound_eq (w z : Array E) :
    lcRound w z = (∑ i ∈ range (w.size / 2), w.getD i 0 * z.getD i 0,
      ∑ i ∈ range (w.size / 2), (w.getD i 0 + w.getD (i + w.size / 2) 0) * (z.getD i 0 + z.getD (i + w.size / 2) 0)) :=
  foldl_pair_sum _ _ _

/-- **One lincheck round keeps the claim**: from `claim = Σ_i w_i z_i`, the verifier's
`polyEval ([c0, claim + c2] ++ [c2]) x` is `Σ_i w'_i z'_i` of the tables folded (high variable) at `x`. -/
theorem lc_round_claim (claim x : E) (w z : Array E) (m : ℕ) (hw : w.size = 2 ^ (m + 1)) (hz : z.size = 2 ^ (m + 1))
    (hclaim : claim = ∑ i ∈ range (2 ^ (m + 1)), w.getD i 0 * z.getD i 0) :
    polyEval ([(lcRound w z).1, claim + esum [(lcRound w z).2]] ++ [(lcRound w z).2]) x =
      ∑ i ∈ range (2 ^ m), (foldHigh w x).getD i 0 * (foldHigh z x).getD i 0 := by
  have hw2 : w.size / 2 = 2 ^ m := by rw [hw, pow_succ]; omega
  have hz2 : z.size / 2 = 2 ^ m := by rw [hz, pow_succ]; omega
  rw [lcRound_eq, hclaim, hw2, show (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m by ring, sum_range_add]
  simp only [esum, List.foldl_cons, List.foldl_nil, zero_add, List.cons_append, List.nil_append, polyEval_three]
  exact lc_claim_generic two_eq_zero_E (2 ^ m) x (fun i ↦ w.getD i 0) (fun i ↦ w.getD (i + 2 ^ m) 0)
    (fun i ↦ w.getD (2 ^ m + i) 0) (fun i ↦ z.getD i 0) (fun i ↦ z.getD (i + 2 ^ m) 0)
    (fun i ↦ z.getD (2 ^ m + i) 0) (fun i ↦ (foldHigh w x).getD i 0) (fun i ↦ (foldHigh z x).getD i 0)
    (fun i _ ↦ by rw [add_comm]) (fun i _ ↦ by rw [add_comm])
    (fun i hi ↦ by rw [foldHigh_getD w x (by rw [hw2]; exact hi), hw2])
    (fun i hi ↦ by rw [foldHigh_getD z x (by rw [hz2]; exact hi), hz2])

/-- **The lincheck's rounds are complete**: from `claim = Σ_i w_i z_i` (tables of `2^(n + j)` entries), the last claim
is `Σ_{i < 2^j} w'_i z'_i` of the tables folded by the round challenges. -/
theorem lcRounds_complete (H : List UInt8 → Id LeanVM.Protocol.Digest) :
    ∀ (n j : ℕ) (claim : E) (wt z : Array E) (w : Wr), wt.size = 2 ^ (n + j) → z.size = 2 ^ (n + j) →
      claim = ∑ i ∈ range (2 ^ (n + j)), wt.getD i 0 * z.getD i 0 →
      ((lcRounds H n claim wt z).run w).1.claim =
        ∑ i ∈ range (2 ^ j), (((lcRounds H n claim wt z).run w).1.challenges.foldl foldHigh wt).getD i 0 *
          (((lcRounds H n claim wt z).run w).1.challenges.foldl foldHigh z).getD i 0
  | 0, j, claim, wt, z, w, _, _, hclaim => by
    simp only [zero_add] at hclaim
    exact hclaim
  | n + 1, j, claim, wt, z, w, hw, hz, hclaim => by
    have hm : n + 1 + j = (n + j) + 1 := by ring
    rw [hm] at hw hz hclaim
    have hsz : ∀ (v : Array E) (x : E), v.size = 2 ^ ((n + j) + 1) → (foldHigh v x).size = 2 ^ (n + j) := by
      intro v x hv; rw [foldHigh_size, hv, pow_succ]; omega
    simp only [lcRounds, run_bind_id, run_pure_id, List.foldl_cons]
    exact lcRounds_complete H n j _ _ _ _ (hsz wt _ hw) (hsz z _ hz)
      (lc_round_claim claim _ wt z (n + j) hw hz hclaim)

end UniComplete.FlockP
