-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.FlockProverTerminal
import UniComplete.FlockProverTower

/-!
# The ring relation is true of `q_flock`: `FlockRingHolds`

**`flockRingHolds`**: for the honest prover in tower order (`Slices.tower`), every skip, every `log_n`, every
writer (any challenges),
`Σ_u Φ(eq(point, u)) q_flock[u] = towerTarget s map`, `Φ = towerRingMap · map` the ring switch's map in tower order
and `s` the slices the prover sent. The steps:

* `towerRingMap_eq`: the verifier's `towerRingMap v map` is `phiT` (the staged map, stage `0` first) of `map`'s
  `map.length` challenges;
* `foldl_foldHigh_getD`: the lincheck's folds, high variable first, leave the witness's extension in the slot bits
  at `chi_in' = rounds.reverse`; so the honest slices are `s_y = Σ_u eq(point, u) bit_y(q_flock[u])`
  (`slices_eq`, `point = chi_in' ++ chi_rest`);
* the copied `towerTarget_eq` (`Σ_i x^i Φ(s_i)`), `Φ` additive and `GF(2)`-homogeneous (`phiT_sum`, a bit is `0` or
  `1`), and a word its bits packed by the powers of `x` (`ofK_eq_sum_cellBit`): `Σ_i x^i Φ(s_i) = Σ_u Φ(eq(p, u))
  q(u)` (`ringHolds_pure`).
-/

namespace UniComplete.FlockP

open UniStatement UniStatement.Flock LeanVM.Parameters Finset
open Tower (phiT phiT_sum phiT_zero stage towerTarget_eq sqn_eq ofK_eq_sum_cellBit)

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The map -/

/-- One step of `towerRingMap`. -/
def ringStep (v : E) (fj : E × ℕ) : E := v + fj.1 * sqn v (2 ^ fj.2)

/-- **`towerRingMap` is the staged map** `Φ_{<|map|}` (stage `0` first). -/
theorem towerRingMap_eq (v : E) (map : List E) :
    towerRingMap v map = phiT (fun n ↦ map.getD n 0) map.length v := by
  have key : ∀ n ≤ map.length, ((map.take n).zip (List.range n)).foldl ringStep v =
      phiT (fun i ↦ map.getD i 0) n v := by
    intro n
    induction n with
    | zero => intro _; simp [phiT]
    | succ n ih =>
      intro hn
      have hlt : n < map.length := by omega
      rw [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some, List.range_succ,
        List.zip_append (by rw [List.length_take, List.length_range]; omega), List.foldl_append,
        ih (by omega)]
      simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, ringStep]
      rw [phiT, stage, sqn_eq, List.getD_eq_getElem _ _ hlt]
  have := key map.length le_rfl
  rw [List.take_length] at this
  rw [← this]
  rfl

/-! ## The slices -/

/-- A high fold's entry: `(1 + x) v[i] + x v[i + half]`. -/
theorem foldHigh_getD (v : Array E) (x : E) {i : ℕ} (hi : i < v.size / 2) :
    (foldHigh v x).getD i 0 = (1 + x) * v.getD i 0 + x * v.getD (i + v.size / 2) 0 := by
  rw [foldHigh, E2ECompleteness.getD_ofFn' _ hi]
  ring

/-- **The high folds are the extension in the top variables**: folding `v` (`2^(m + j)` entries) by `xs` (`m`
challenges, the top variable first) leaves at `y < 2^j` the sum `Σ_h eq(xs.reverse, h) v[y + 2^j h]`. -/
theorem foldl_foldHigh_getD : ∀ (xs : List E) (j : ℕ) (v : Array E), v.size = 2 ^ (xs.length + j) →
    ∀ y < 2 ^ j, (xs.foldl foldHigh v).getD y 0 =
      ∑ h ∈ range (2 ^ xs.length), eqB xs.reverse h * v.getD (y + 2 ^ j * h) 0
  | [], j, v, _, y, _ => by simp
  | x :: xs, j, v, hv, y, hy => by
    have hhalf : v.size / 2 = 2 ^ (xs.length + j) := by
      rw [hv, List.length_cons, show xs.length + 1 + j = (xs.length + j) + 1 by ring, pow_succ,
        Nat.mul_div_cancel _ (by norm_num)]
    rw [List.foldl_cons, foldl_foldHigh_getD xs j (foldHigh v x) (by rw [foldHigh_size, hhalf]) y hy,
      List.length_cons, List.reverse_cons, pow_succ, show 2 ^ xs.length * 2 = 2 ^ (xs.length + 1) by ring,
      sum_split xs.length 1]
    simp only [show (2 : ℕ) ^ 1 = 2 by rfl, sum_range_succ, range_one, sum_singleton]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun h hh ↦ ?_
    have hh' := mem_range.mp hh
    have hlen : xs.reverse.length = xs.length := List.length_reverse
    have hyh : y + 2 ^ j * h < v.size / 2 := by
      rw [hhalf, pow_add, mul_comm (2 ^ xs.length)]
      calc y + 2 ^ j * h < 2 ^ j + 2 ^ j * h := by omega
        _ = 2 ^ j * (h + 1) := by ring
        _ ≤ 2 ^ j * 2 ^ xs.length := Nat.mul_le_mul_left _ hh'
    have hA : ∀ b, eqB (xs.reverse ++ [x]) (h + 2 ^ xs.length * b) = eqB xs.reverse h * eqB [x] b := by
      intro b
      have := eqB_append xs.reverse [x] (x := h) (by rw [hlen]; exact hh') b
      rwa [hlen] at this
    have e0 : eqB [x] 0 = 1 + x := by
      have := eqB_cons_even x [] 0
      simpa using this
    have e1 : eqB [x] 1 = x := by
      have := eqB_cons_odd x [] 0
      simpa using this
    rw [hA 0, hA 1, foldHigh_getD v x hyh, hhalf, e0, e1]
    simp only [mul_zero, add_zero, mul_one]
    rw [show y + 2 ^ j * h + 2 ^ (xs.length + j) = y + 2 ^ j * (h + 2 ^ xs.length) by rw [pow_add]; ring]
    ring

/-- The lincheck's witness at a position, as `q_flock`'s bits. -/
theorem lincheckWitness_getD (q : Array K) (chiRest : List E) {y jin : ℕ} (hy : y < 64) (hjin : jin < 2 ^ 8) :
    (lincheckWitness q chiRest).getD (y + 2 ^ 6 * jin) 0 =
      ∑ t ∈ range (2 ^ chiRest.length), eqB chiRest t * Lv42.Protocol.cellBit (q.getD (jin + 256 * t) 0) y := by
  have hi : y + 2 ^ 6 * jin < 2 ^ blake2sR1csLogSize := by
    unfold blake2sR1csLogSize
    calc y + 2 ^ 6 * jin < 2 ^ 6 + 2 ^ 6 * jin := by omega
      _ = 2 ^ 6 * (jin + 1) := by ring
      _ ≤ 2 ^ 6 * 2 ^ 8 := Nat.mul_le_mul_left _ hjin
      _ = 2 ^ 14 := by norm_num
  rw [lincheckWitness, E2ECompleteness.getD_ofFn' _ hi]
  simp only
  rw [sumTo_eq, eqKernel_size]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [eqKernel_getD _ (mem_range.mp ht), zAt]
  have e1 : (y + 2 ^ 6 * jin) / 64 = jin := by
    rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by simpa using hy),
      zero_add]
  have e2 : (y + 2 ^ 6 * jin) % 64 = y := by
    rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simpa using hy)]
  rw [e1, e2]

/-- **The honest slices**: `s_y = Σ_u eq(chi_in' ++ chi_rest, u) bit_y(q_flock[u])`. -/
theorem slices_eq (q : Array K) (chiRest xs : List E) (hxs : xs.length = 8) {y : ℕ} (hy : y < 64) :
    (xs.foldl foldHigh (lincheckWitness q chiRest)).getD y 0 =
      ∑ u ∈ range (2 ^ (xs.reverse ++ chiRest).length), eqB (xs.reverse ++ chiRest) u *
        Lv42.Protocol.cellBit (q.getD u 0) y := by
  have hsize : (lincheckWitness q chiRest).size = 2 ^ (xs.length + 6) := by
    simp [lincheckWitness, hxs, blake2sR1csLogSize]
  rw [foldl_foldHigh_getD xs 6 _ hsize y (by simpa using hy)]
  have hsplit := sum_eqB_split xs.reverse chiRest (fun u ↦ Lv42.Protocol.cellBit (q.getD u 0) y)
  rw [List.length_reverse, hxs] at hsplit
  rw [List.length_append, List.length_reverse, hxs, ← hsplit]
  refine sum_congr rfl fun jin hjin ↦ ?_
  rw [lincheckWitness_getD q chiRest hy (mem_range.mp hjin), show (2 : ℕ) ^ 8 = 256 by rfl]

/-! ## The ring claim -/

/-- `Φ` of a bit times a value. -/
theorem phiT_cellBit (f : ℕ → E) (n : ℕ) (a : K) (i : ℕ) (e : E) :
    phiT f n (e * Lv42.Protocol.cellBit a i) = phiT f n e * Lv42.Protocol.cellBit a i := by
  unfold Lv42.Protocol.cellBit
  split
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, phiT_zero]

/-- **The ring claim of the honest slices**, for any challenges: `Σ_u Φ(eq(p, u)) q(u) = towerTarget s map`. -/
theorem ringHolds_pure (q : Array K) (chiRest xs map : List E) (hxs : xs.length = 8) (hmap : map.length = 6) :
    ∑ u ∈ range (2 ^ (xs.reverse ++ chiRest).length),
        towerRingMap ((eqKernel (xs.reverse ++ chiRest)).getD u 0) map * ofK (q.getD u 0) =
      towerTarget (xs.foldl foldHigh (lincheckWitness q chiRest)).toList map := by
  set p := xs.reverse ++ chiRest with hp
  set f : ℕ → E := fun n ↦ map.getD n 0 with hf
  have hsz : (xs.foldl foldHigh (lincheckWitness q chiRest)).size = 64 := by
    refine foldl_foldHigh_size _ 6 _ ?_
    simp [lincheckWitness, hxs, blake2sR1csLogSize]
  rw [towerTarget_eq]
  -- The right side: `Σ_i x^i Φ(s_i)`, each slice the sum of the words' bits against `eq`.
  have hs : ∀ i ∈ range 64, ofK (g ^ i) * phiT f 6 ((xs.foldl foldHigh (lincheckWitness q chiRest)).toList.getD i 0)
      = ∑ u ∈ range (2 ^ p.length), ofK (g ^ i) * (phiT f 6 (eqB p u) * Lv42.Protocol.cellBit (q.getD u 0) i) := by
    intro i hi
    rw [toList_getD, slices_eq q chiRest xs hxs (mem_range.mp hi), phiT_sum, mul_sum]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [phiT_cellBit]
  rw [sum_congr rfl hs, sum_comm]
  refine sum_congr rfl fun u hu ↦ ?_
  rw [eqKernel_getD _ (mem_range.mp hu), towerRingMap_eq, hmap, ofK_eq_sum_cellBit, mul_sum,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ ofK (g ^ i) * (phiT f 6 (eqB p u) * Lv42.Protocol.cellBit (q.getD u 0) i))]
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-! ## The honest prover -/

/-- The end's run: with the slices `s`, the ring switch's map and target. -/
theorem ringEndW_eq (H : List UInt8 → Id LeanVM.Protocol.Digest) (variant : Variant) (s : List E) (w : Wr) :
    ((ringEndW H variant s).run w).1 = .ring ((samplesW H ringMapShifts.length).run w).1
      (if variant.slices = .tower then towerTarget s ((samplesW H ringMapShifts.length).run w).1
        else polyEval (s.map fun value ↦ ringMap value ((samplesW H ringMapShifts.length).run w).1) gen) := by
  simp only [ringEndW, run_bind_id, run_pure_id]

variable (H : List UInt8 → Id LeanVM.Protocol.Digest)

/-! ## The honest prover -/

theorem flockProve_end (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) :
    ((flockProve H logN variant q).run w).1.end_ =
      ((endW H variant ((frontW H logN variant q).run w).1.1.slices).run ((frontW H logN variant q).run w).2).1 := by
  simp only [flockProve, run_bind_id, run_pure_id, assemble]

theorem flockProve_point (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) :
    ((flockProve H logN variant q).run w).1.point = ((frontW H logN variant q).run w).1.1.point := by
  simp only [flockProve, run_bind_id, run_pure_id, assemble]

theorem endW_some (variant : Variant) (s : List E) (w : Wr) :
    ((endW H variant (some s)).run w).1 = ((ringEndW H variant s).run w).1 := rfl

theorem flockProve_ring (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (ht : variant.slices = .tower) :
    ((flockProve H logN variant q).run w).1.end_ =
      .ring ((samplesW H ringMapShifts.length).run ((frontW H logN variant q).run w).2).1
        (towerTarget ((frontW H logN variant q).run w).1.2
          ((samplesW H ringMapShifts.length).run ((frontW H logN variant q).run w).2).1) := by
  have hc : variant.slices ≠ .claim := by rw [ht]; decide
  rw [flockProve_end, frontW_slices H logN variant q w hc, endW_some, ringEndW_eq, if_pos ht]

/-- **`FlockRingHolds` of the honest prover** in tower order (`Slices.tower`): at a pure Keccak-256, every
`log_n`, every skip, every writer (any challenges). -/
theorem flockRingHolds (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (ht : variant.slices = .tower) :
    FlockRingHolds ((flockProve H logN variant q).run w).1 q := by
  have hmap : ((samplesW H ringMapShifts.length).run ((frontW H logN variant q).run w).2).1.length = 6 := by
    rw [samplesW_length]; rfl
  unfold FlockRingHolds
  rw [flockProve_ring H logN variant q w ht, flockProve_point]
  generalize ((samplesW H ringMapShifts.length).run ((frontW H logN variant q).run w).2).1 = map at hmap ⊢
  show ∑ u ∈ range (2 ^ ((frontW H logN variant q).run w).1.1.point.length),
      towerRingMap ((eqKernel ((frontW H logN variant q).run w).1.1.point).getD u 0) map * ofK (q.getD u 0) =
    towerTarget ((frontW H logN variant q).run w).1.2 map
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW_eq H logN variant q w
  have hlen : lc.challenges.length = 8 := by rw [hlc, lcRounds_length]; rfl
  have hz : lc.z = lc.challenges.foldl foldHigh (lcWitnessOf variant.skip q zc) := by rw [hlc, lcRounds_z]
  rw [hfr]
  show ∑ u ∈ range (2 ^ (lc.challenges.reverse ++ (zc.2.1.drop (packing - variant.skip)).drop lincheckRounds).length),
      towerRingMap ((eqKernel (lc.challenges.reverse ++
        (zc.2.1.drop (packing - variant.skip)).drop lincheckRounds)).getD u 0) map * ofK (q.getD u 0) =
    towerTarget lc.z.toList map
  rw [hz]
  exact ringHolds_pure q _ lc.challenges map hlen hmap

end UniComplete.FlockP
