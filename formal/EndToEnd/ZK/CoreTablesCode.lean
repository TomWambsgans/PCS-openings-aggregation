-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `stackWordFast`, `encKAt`, `novelAt`, `vanishingAt`, `normVanishingAt`
-- (`Statement/Prover/Ntt.lean`, `Statement/Prover/Code.lean`), `stackWord`, `blockK`,
-- `vanishingAt_succ`, `bitsEquiv` (`lean_vm/LeanVM/Protocol/Whir/Complete/Encoding.lean`,
-- `Subspace.lean`, `NovelBasis.lean`).
import ZK.CoreSpec
import Bridge.Setup

/-!
# The codewords' rows and the leaves' bytes (`CodeW`, `CodeQ`, `RowBytes`)

The joint model writes a secret table's leaf at the position `p` as the row `rowAt (codeAt ℓ p) T`:
lane `l`'s entry `Σ_y X_y(F64(p)) · T l y`, `X_y` the novel basis of `formal/QuotientSecurity`
(`novel`, `subW`, `subRoot`: the verifier's recurrence `W_{k+1} = W_k² + W_k(v_k) W_k` at
`v_k = F64(2^k)`), as the 64-word image `leafWords` (the absent lanes' zeros, then the lanes from
the last). The statement's WHIR prover commits mumbai's word `stackWordFast μ 1 A` of the stack
array `A`: by `Bridge.Setup.stackWordFast_eq_columnOf` mumbai's `stackWord`, leaf `p` the 64 lanes'
encodings `encKAt (μ − 6)` at `K.ofBits p`, from the last lane. Here:

* `vanishingAt_eq`: mumbai's `W_i` (the product over the subspace) is `subW` at the words
  (`vanishingAt_succ` is the verifier's recurrence); `novelAt_eq`: mumbai's `X_y` is `novel`;
* `encKAt_eq`: an encoding at `p` is the novel basis at `F64(p)` against the message's entries
  (cube points read as numbers, `bitsEquiv`);
* **`leafWords_code`**: for a stack `T` read off an array `A` of at most `n · 2^ℓ` entries
  (`n ≤ 64` lanes of `2^ℓ`, `ℓ = μ − 6`), the model's leaf is the WHIR word's, at every position;
* **`codeW`**, **`codeQ`**: the witness (`μ = 25`, `40` lanes) and quotient (`μ = 28`, `63` lanes)
  instances; **`rowBytes_eq`**: a leaf's bytes are its image's words, little-endian.
-/

open Polynomial QuotientSecurity QuotientSecurity.Hiding
open LeanVM.Parameters LeanVM.Prover
open QuotientZk.Instance
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## Mumbai's novel basis is the model's -/

/-- **Mumbai's subspace polynomial is the model's**, at the words `v_k = F64(2^k)`. -/
theorem vanishingAt_eq (i : ℕ) (a : K) :
    LeanVM.Protocol.Whir.vanishingAt i a = (subW wordsK.v i).eval a := by
  induction i generalizing a with
  | zero =>
    simp [LeanVM.Protocol.Whir.vanishingAt, subW_zero]
  | succ i ih =>
    rw [LeanVM.Protocol.Whir.vanishingAt_succ, subW_succ_eval, ih, ih]
    rfl

/-- Mumbai's normalized subspace polynomial. -/
theorem normVanishingAt_eq (i : ℕ) (a : K) :
    LeanVM.Protocol.Whir.normVanishingAt i a = (subRoot wordsK.v i)⁻¹ * (subW wordsK.v i).eval a := by
  rw [LeanVM.Protocol.Whir.normVanishingAt, vanishingAt_eq, vanishingAt_eq, mul_comm]
  rfl

/-- **Mumbai's novel basis is the model's**: `X_y(a)` for `y < 2^κ`, `κ ≤ 64`. -/
theorem novelAt_eq {κ y : ℕ} (hκ : κ ≤ 64) (hy : y < 2 ^ κ) (a : K) :
    LeanVM.Protocol.Whir.novelAt y a = (novel wordsK.v κ y).eval a := by
  rw [LeanVM.Protocol.Whir.novelAt, novel, eval_prod, Finset.prod_filter]
  symm
  rw [Finset.prod_subset (Finset.range_subset_range.mpr hκ)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [Polynomial.eval_mul, Polynomial.eval_C, normVanishingAt_eq]
    · rfl
  · intro i _ hi
    have hi' : κ ≤ i := by simpa using hi
    have : y.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hi'))
    simp [this]

/-- **An encoding at `p` is the novel basis at `F64(p)`** against the message's entries. -/
theorem encKAt_eq {κ : ℕ} (hκ : κ ≤ 64) (g : ℕ → K) (p : ℕ) :
    LeanVM.Protocol.Whir.Complete.encKAt κ (fun u => g (LeanVM.Protocol.Whir.bitsToNat u)) p =
      ∑ y : Fin (2 ^ κ), (novel wordsK.v κ y).eval (F64.ofNat p) * g y := by
  unfold LeanVM.Protocol.Whir.Complete.encKAt
  refine Fintype.sum_equiv (LeanVM.Protocol.Whir.bitsEquiv κ) _ _ fun u => ?_
  rw [LeanVM.Protocol.Whir.bitsEquiv_val,
    novelAt_eq hκ (LeanVM.Protocol.Whir.bitsToNat_lt u), mul_comm]
  rfl

/-! ## A row of the model is a leaf of the WHIR word -/

/-- Lane `l`'s entry of the model's row at `p`: the encoding of the lane's block of the array. -/
theorem rowAt_code {n ℓ N : ℕ} (hN : N = 2 ^ ℓ) (hℓ : ℓ ≤ 64) (T : Fin n → Fin (2 ^ ℓ) → K)
    (A : Array K) (hT : ∀ l y, T l y = A.getD ((l : ℕ) * N + y) 0) (l : Fin n) (p : ℕ) :
    QuotientZk.Deployed.rowAt (codeAt deployedRep ℓ p) T l =
      LeanVM.Protocol.Whir.Complete.encKAt ℓ
        (fun x => A.getD (LeanVM.Protocol.Whir.bitsToNat x + 2 ^ ℓ * (l : ℕ)) 0) p := by
  subst hN
  rw [encKAt_eq hℓ (fun i => A.getD (i + 2 ^ ℓ * (l : ℕ)) 0)]
  unfold QuotientZk.Deployed.rowAt codeAt
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hT, add_comm, mul_comm (l : ℕ)]
  rfl

/-- `64` lanes, the first `n` of them a row's entries and the others zero, in reverse. -/
theorem reverse_map_range {n : ℕ} (hn : n ≤ 64) (row : Fin n → K) (f : ℕ → K)
    (hf : ∀ u (hu : u < n), f u = row ⟨u, hu⟩) (hz : ∀ u, n ≤ u → u < 64 → f u = 0) :
    ((List.range 64).map f).reverse = List.replicate (64 - n) 0 ++ (List.ofFn row).reverse := by
  have h : (List.range 64).map f = List.ofFn row ++ List.replicate (64 - n) 0 := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_append, List.length_ofFn,
        List.length_replicate]
      omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getElem_append]
      split_ifs with hi
      · simp only [List.length_ofFn] at hi
        rw [List.getElem_ofFn]
        exact hf i hi
      · simp only [List.length_ofFn, not_lt] at hi
        rw [List.getElem_replicate]
        exact hz i hi (by simpa using h1)
  rw [h, List.reverse_append, List.reverse_replicate]

/-- **The model's leaf is the WHIR word's**: for a stack `T` of `n ≤ 64` lanes of `2^ℓ` read off an
array `A` of at most `n · 2^ℓ` entries, at every position `p`, with `ℓ = μ − 6`. -/
theorem leafWords_code {n ℓ μ N : ℕ} (hμ : μ - 6 = ℓ) (h6 : 6 ≤ μ) (h64 : μ ≤ 64) (hn : n ≤ 64)
    (hN : N = 2 ^ ℓ) (T : Fin n → Fin (2 ^ ℓ) → K) (A : Array K)
    (hT : ∀ l y, T l y = A.getD ((l : ℕ) * N + y) 0) (hA : A.size ≤ n * N) (p : ℕ) :
    Render.leafWords (QuotientZk.Deployed.rowAt (codeAt deployedRep ℓ p) T) =
      stackWordFast μ 1 A p := by
  subst hμ hN
  have hsplit : ∀ x u : ℕ, x < 2 ^ (μ - 6) → u < 64 → x + 2 ^ (μ - 6) * u < 2 ^ μ := by
    intro x u hx hu
    have e : 2 ^ μ = 2 ^ (μ - 6) * 64 := by
      rw [show (64 : ℕ) = 2 ^ 6 from rfl, ← pow_add]
      congr 1
      omega
    rw [e]
    calc x + 2 ^ (μ - 6) * u < 2 ^ (μ - 6) + 2 ^ (μ - 6) * u := by omega
      _ = 2 ^ (μ - 6) * (u + 1) := by ring
      _ ≤ 2 ^ (μ - 6) * 64 := Nat.mul_le_mul_left _ hu
  rw [Bridge.Setup.stackWordFast_eq_columnOf μ 1 h6 h64 A]
  unfold Render.leafWords LeanVM.Protocol.Whir.Complete.stackWord
  symm
  refine reverse_map_range hn _ _ (fun u hu => ?_) (fun u hu1 hu2 => ?_)
  · rw [rowAt_code rfl (by omega) T A hT ⟨u, hu⟩ p]
    refine congrArg (fun g => LeanVM.Protocol.Whir.Complete.encKAt (μ - 6) g p) (funext fun x => ?_)
    show (Bridge.Setup.columnOf μ A).values.getD _ 0 = _
    rw [Bridge.Setup.columnOf_getD μ A
      (hsplit _ u (LeanVM.Protocol.Whir.bitsToNat_lt x) (by omega))]
  · unfold LeanVM.Protocol.Whir.Complete.encKAt
    refine Finset.sum_eq_zero fun x _ => ?_
    show (Bridge.Setup.columnOf μ A).values.getD _ 0 * _ = 0
    rw [Bridge.Setup.columnOf_getD μ A
      (hsplit _ u (LeanVM.Protocol.Whir.bitsToNat_lt x) hu2)]
    have hge : A.size ≤ LeanVM.Protocol.Whir.bitsToNat x + 2 ^ (μ - 6) * u :=
      calc A.size ≤ n * 2 ^ (μ - 6) := hA
        _ ≤ u * 2 ^ (μ - 6) := Nat.mul_le_mul_right _ hu1
        _ ≤ _ := by rw [mul_comm]; omega
    rw [show A.getD (LeanVM.Protocol.Whir.bitsToNat x + 2 ^ (μ - 6) * u) 0 = 0 by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge], zero_mul]

/-! ## The deployed instances -/

/-- **The witness codeword's rows** (`40` lanes of `2^19`, `μ = 25`), at every position. -/
theorem codeW : CodeW := by
  intro T A hT hA p _
  exact leafWords_code (n := Lw.lanes.length) (μ := 25) (by rw [logLane_W]) (by norm_num)
    (by norm_num) (by rw [lanes_W]; norm_num) (by rw [logLane_W]) T A hT
    (by rw [hA, lanes_W]) p

/-- **The quotient codeword's rows** (`63` lanes of `2^22`, `μ = 28`), at every position. -/
theorem codeQ : CodeQ := by
  intro T A hT hA p _
  exact leafWords_code (n := Lq.lanes.length) (μ := 28) (by rw [logLane_Q]) (by norm_num)
    (by norm_num) (by rw [lanes_Q]; norm_num) (by rw [logLane_Q]) T A hT
    (by rw [hA, lanes_Q]) p

/-! ## The leaves' bytes -/

theorem flatMap_lane (L : List K) :
    (L.map K.lane).flatMap LeanVM.Protocol.KeccakHash.wordBytes =
      L.flatMap LeanVM.Protocol.KeccakHash.kBytes := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.flatMap_cons, ih, LeanVM.Protocol.KeccakHash.kBytes]

/-- **A leaf's bytes are its image's words**, little-endian. -/
theorem rowBytes_eq : RowBytes := by
  intro n row _
  unfold rowBytes Render.leafWords
  rw [← flatMap_lane]
  congr 1
  rw [List.map_append, List.map_replicate, List.map_reverse, List.map_ofFn]
  rfl

end PcsQuotient.EndToEnd.Core
