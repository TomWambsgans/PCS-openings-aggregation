-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Semantics
import Mathlib.FieldTheory.Finite.Basic

/-!
# What the blocks of `reduce` compute

The loops of `Program.lean`, read in the field: the chain `w_k = sq^[k] t` (`wChain_spec`), the
folds and maps (`foldO_spec`, `mapO_spec`), `x^(2^n)` (`squareN_spec`), the inversion by the norm
(`inverse_spec`: it is `x⁻¹`, `0` at `0`, as `F192::inv` and `protocol::inverse`), the prefix
products and the batch inversion (`prefixes_spec`, `backInv_spec`), and a row's cells
(`cell_spec`).
-/

set_option linter.unusedSectionVars false

namespace Implementation

open Program Emitted QuotientSecurity

variable {F : Type} [Field F] [CharP F 2] {limbs : F ≃ QuotientRpm.Limbs}
variable {H : List UInt8 → Vector UInt8 32} {idx cd : List UInt8}
variable (hF : IsF192 limbs)
include hF

local notation "V" => val limbs H idx cd
local notation "MUL" => mul_spec (H := H) (idx := idx) (cd := cd) hF
local notation "ADD" => add_spec (H := H) (idx := idx) (cd := cd) hF
local notation "CNST" => cnst_spec (H := H) (idx := idx) (cd := cd) hF

theorem wChain_spec (t : Nat) : ∀ n, Spec (wChain t n) fun ws =>
    ws.length = n + 1 ∧ ∀ k < n + 1, V (ws.getD k 0) = sq^[k] (V t)
  | 0 => Spec.some ⟨rfl, fun k hk => by
      obtain rfl : k = 0 := by omega
      simp⟩
  | n + 1 => by
    unfold wChain
    apply Spec.bind
    refine (wChain_spec t n).weaken fun ws hws => ?_
    obtain ⟨hlen, hw⟩ := hws
    apply Spec.bind
    refine (MUL _ _).weaken fun s hs => ?_
    apply Spec.bind
    refine (ADD _ _).weaken fun w' hw' => ?_
    apply Spec.pure
    have hlast : ws.getLastD 0 = ws.getD n 0 := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, hlen]
      simp
    refine ⟨by simp [hlen], fun k hk => ?_⟩
    by_cases hkn : k < n + 1
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hw k hkn
    · obtain rfl : k = n + 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [hw', hs, hlast, hw n (by omega), Function.iterate_succ_apply']
      rfl

theorem foldO_spec {f : Nat → Nat → Option Nat} (g : F → Nat → F) (ks : List Nat)
    (hf : ∀ acc, ∀ k ∈ ks, Spec (f acc k) fun r => V r = g (V acc) k) :
    ∀ acc : Nat, Spec (foldO f acc ks) fun r => V r = ks.foldl g (V acc) := by
  induction ks with
  | nil => exact fun acc => Spec.some rfl
  | cons k ks ih =>
    intro acc
    unfold foldO
    apply Spec.bind
    refine (hf acc k List.mem_cons_self).weaken fun acc' h' => ?_
    refine (ih (fun a j hj => hf a j (List.mem_cons_of_mem _ hj)) acc').weaken fun r hr => ?_
    rw [hr, h']
    rfl

theorem mapO_spec {f : Nat → Option Nat} (g : Nat → F) (ks : List Nat)
    (hf : ∀ k ∈ ks, Spec (f k) fun r => V r = g k) :
    Spec (mapO f ks) fun rs => rs.map V = ks.map g := by
  induction ks with
  | nil => exact Spec.some rfl
  | cons k ks ih =>
    unfold mapO
    apply Spec.bind
    refine (hf k List.mem_cons_self).weaken fun r hr => ?_
    apply Spec.bind
    refine (ih fun j hj => hf j (List.mem_cons_of_mem _ hj)).weaken fun rs hrs => ?_
    apply Spec.pure
    simp [hr, hrs]

theorem squareN_spec (x : Nat) : ∀ n, Spec (squareN x n) fun r => V r = V x ^ 2 ^ n
  | 0 => Spec.some (by simp)
  | n + 1 => by
    unfold squareN
    apply Spec.bind
    refine (squareN_spec x n).weaken fun y hy => ?_
    refine (MUL _ _).weaken fun r hr => ?_
    rw [hr, hy, ← pow_add, pow_succ]
    ring_nf

omit hF in
theorem exp_round (k : Nat) : ((2 ^ k - 1) * 2 ^ k + (2 ^ k - 1)) * 2 + 1 = 2 ^ (2 * k + 1) - 1 := by
  have h2 : 2 ^ (2 * k + 1) = 2 * (2 ^ k * 2 ^ k) := by ring
  rw [h2]
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ k = j + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  rw [hj, Nat.add_sub_cancel]
  have : 2 * ((j + 1) * (j + 1)) = (j * (j + 1) + j) * 2 + 1 + 1 := by ring
  omega

theorem invRound_spec (norm : Nat) (p : Nat × Nat) (hp : V p.1 = V norm ^ (2 ^ p.2 - 1)) :
    Spec (invRound norm p) fun q => q.2 = 2 * p.2 + 1 ∧ V q.1 = V norm ^ (2 ^ q.2 - 1) := by
  unfold invRound
  apply Spec.bind
  refine (squareN_spec (H := H) (idx := idx) (cd := cd) hF _ _).weaken fun sh hsh => ?_
  apply Spec.bind
  refine (MUL _ _).weaken fun o ho => ?_
  apply Spec.bind
  refine (MUL _ _).weaken fun s hs => ?_
  apply Spec.bind
  refine (MUL _ _).weaken fun o' ho' => ?_
  apply Spec.pure
  refine ⟨rfl, ?_⟩
  rw [ho', hs, ho, hsh, hp, ← exp_round p.2]
  ring

theorem invRounds_spec (norm : Nat) (n : Nat) : ∀ (p : Nat × Nat), V p.1 = V norm ^ (2 ^ p.2 - 1) →
    Spec (invRounds norm n p) fun q => q.2 = (fun k => 2 * k + 1)^[n] p.2 ∧
      V q.1 = V norm ^ (2 ^ q.2 - 1) := by
  induction n with
  | zero => exact fun p hp => Spec.some ⟨rfl, hp⟩
  | succ n ih =>
    intro p hp
    unfold invRounds
    apply Spec.bind
    refine (invRound_spec (H := H) (idx := idx) (cd := cd) hF norm p hp).weaken fun q hq => ?_
    refine (ih q hq.2).weaken fun r hr => ⟨?_, hr.2⟩
    rw [hr.1, hq.1, Function.iterate_succ_apply]

theorem prefixes_spec : ∀ (ds : List Nat) (acc : Nat), Spec (prefixes acc ds) fun ps =>
    ps.length = ds.length + 1 ∧
      ∀ i ≤ ds.length, V (ps.getD i 0) = V acc * ((ds.take i).map V).prod
  | [], acc => Spec.some ⟨rfl, fun i hi => by
      obtain rfl : i = 0 := by simpa using hi
      simp⟩
  | d :: ds, acc => by
    unfold prefixes
    apply Spec.bind
    refine (MUL _ _).weaken fun acc' h' => ?_
    apply Spec.bind
    refine (prefixes_spec ds acc').weaken fun ps hps => ?_
    apply Spec.pure
    obtain ⟨hlen, hp⟩ := hps
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.prod_cons]
      rw [hp i (by simpa using hi), h', mul_assoc]

/-- The batch inversion: from the last, `inverses[i] = running · prefix[i]`, `running ·= d_i`. -/
theorem backInv_spec (pre den : Nat → Nat) (P : Nat → F)
    (hP : ∀ i, P (i + 1) = P i * V (den i)) (n : Nat) :
    ∀ (running : Nat), (∀ i < n, V (pre i) = P i) → V running = (P n)⁻¹ → P n ≠ 0 →
      Spec (backInv running ((List.range n).reverse.map fun i => (pre i, den i))) fun r =>
        r.length = n ∧ ∀ i < n, V (r.reverse.getD i 0) = (V (den i))⁻¹ := by
  induction n with
  | zero => exact fun _ _ _ _ => Spec.some ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro running hpre hr hn
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons]
    unfold backInv
    have hd : V (den n) ≠ 0 := by rw [hP] at hn; exact right_ne_zero_of_mul hn
    have hpn : P n ≠ 0 := by rw [hP] at hn; exact left_ne_zero_of_mul hn
    apply Spec.bind
    refine (MUL _ _).weaken fun inv hinv => ?_
    apply Spec.bind
    refine (MUL _ _).weaken fun r' hr' => ?_
    apply Spec.bind
    refine (ih r' (fun i hi => hpre i (by omega)) ?_ hpn).weaken fun tail ht => ?_
    · rw [hr', hr, hP, mul_inv, mul_assoc, inv_mul_cancel₀ hd, mul_one]
    · apply Spec.pure
      obtain ⟨hlen, htail⟩ := ht
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      rw [List.reverse_cons]
      by_cases hin : i < n
      · rw [List.getD_append _ _ _ _ (by simp [hlen, hin])]
        exact htail i hin
      · obtain rfl : i = n := by omega
        rw [List.getD_append_right _ _ _ _ (by simp [hlen]), List.length_reverse, hlen,
          Nat.sub_self]
        simp only [List.getD_cons_zero]
        rw [hinv, hr, hpre i (by omega), hP, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hpn,
          one_mul]

/-- **A cell of the row of `t`**: `a_0 + (t + shift) a_1 + w_1' (a_2 + (t + shift) a_3)`, with
`w_1' = w_1` or `w_1 + 1`. -/
theorem cell_spec (L : Leaves) (hone : V L.one = 1) (w1 shift : Nat) (second : Bool) :
    Spec (cell L w1 shift second) fun r => V r =
      V (L.a.getD 0 0) + (V L.t + elem limbs shift) * V (L.a.getD 1 0) +
        (if second then V w1 + 1 else V w1) *
          (V (L.a.getD 2 0) + (V L.t + elem limbs shift) * V (L.a.getD 3 0)) := by
  unfold cell
  apply Spec.bind
  refine (CNST _).weaken fun sh hsh => ?_
  apply Spec.bind
  refine (ADD _ _).weaken fun first hfirst => ?_
  apply Spec.bind
  refine Spec.weaken (P := fun snd => V snd = if second then V w1 + 1 else V w1) ?_ fun snd hsnd => ?_
  · unfold secondOf
    cases second
    · exact Spec.some rfl
    · exact (ADD _ _).weaken fun r hr => by rw [hr, hone]; rfl
  apply Spec.bind
  refine (MUL _ _).weaken fun m1 hm1 => ?_
  apply Spec.bind
  refine (ADD _ _).weaken fun s1 hs1 => ?_
  apply Spec.bind
  refine (MUL _ _).weaken fun m3 hm3 => ?_
  apply Spec.bind
  refine (ADD _ _).weaken fun s3 hs3 => ?_
  apply Spec.bind
  refine (MUL _ _).weaken fun m2 hm2 => ?_
  refine (ADD _ _).weaken fun r hr => ?_
  rw [hr, hs1, hm1, hm2, hsnd, hs3, hm3, hfirst, hsh]

variable [Fintype F]

/-- **The inversion is `x⁻¹`**: `m · N^(2^64 - 2)` with `N = x m`, `m = x^(2^64) x^(2^128)`, in a
field of `2^192` elements where `frobE` is `x^(2^64)`. -/
theorem inverse_spec (hfr : FrobOK limbs) (x : Nat) : Spec (inverse x) fun r => V r = (V x)⁻¹ := by
  unfold inverse
  apply Spec.bind
  refine (frob_spec (H := H) (idx := idx) (cd := cd) hF hfr _).weaken fun f1 hf1 => ?_
  apply Spec.bind
  refine (frob_spec (H := H) (idx := idx) (cd := cd) hF hfr _).weaken fun f2 hf2 => ?_
  apply Spec.bind
  refine (MUL _ _).weaken fun m hm => ?_
  apply Spec.bind
  refine (MUL _ _).weaken fun norm hnorm => ?_
  apply Spec.bind
  refine (invRounds_spec (H := H) (idx := idx) (cd := cd) hF norm 5 (norm, 1) (by simp)).weaken fun p hp => ?_
  apply Spec.bind
  refine (MUL _ _).weaken fun s hs => ?_
  refine (MUL _ _).weaken fun r hr => ?_
  obtain ⟨hp2, hp1⟩ := hp
  have h63 : p.2 = 63 := by rw [hp2]; rfl
  rw [h63] at hp1
  set a := V x
  have hmv : V m = a ^ 2 ^ 64 * a ^ 2 ^ 128 := by
    rw [hm, hf2, hf1, ← pow_mul]; norm_num
  have hNv : V norm = a ^ (1 + 2 ^ 64 + 2 ^ 128) := by
    rw [hnorm, hmv, pow_add, pow_add, pow_one]; ring
  rw [hr, hs, hp1, hmv, hNv]
  by_cases ha : a = 0
  · rw [ha]; simp
  · have hcard : a ^ (2 ^ 192 - 1) = 1 := by
      rw [← card_eq limbs]; exact FiniteField.pow_card_sub_one_eq_one a ha
    have hN : (a ^ (1 + 2 ^ 64 + 2 ^ 128)) ^ (2 ^ 64 - 1) = 1 := by
      rw [← pow_mul, ← hcard]; norm_num
    have hsq : (a ^ (1 + 2 ^ 64 + 2 ^ 128)) ^ (2 ^ 63 - 1) * (a ^ (1 + 2 ^ 64 + 2 ^ 128)) ^ (2 ^ 63 - 1)
        = (a ^ (1 + 2 ^ 64 + 2 ^ 128))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_add, ← pow_succ, ← hN]
      norm_num
    have hm0 : a ^ 2 ^ 64 * a ^ 2 ^ 128 ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ ha)
    have he : a ^ (1 + 2 ^ 64 + 2 ^ 128) = a * (a ^ 2 ^ 64 * a ^ 2 ^ 128) := by
      rw [pow_add, pow_add, pow_one]; ring
    rw [hsq, he, mul_inv, mul_comm a⁻¹, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]

end Implementation
