-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.Prefix

/-!
# The bad family catches, given the code's evaluators

`Catches (flockProg κ) (flockBad κ)` is `FlockSound`'s deterministic theorem (`flock_front`) on the
transcript: a completed transcript whose ring claim holds of the column and whose pending claim is
its sum has a satisfied relation, or one of its challenges is in its bad set.

**What it needs of the code** (`Tx`, from the evaluator transcription, another branch): the
evaluators the verifier calls equal the cube forms of `FlockSound`:

* `fixed`: `fixed_challenges` are leanVM's fixed coordinates (`fixedPt`);
* `epow`: `E::pow` is the power;
* `interp`: the skip's `lagrange_interpolate` at `z` is `interp` over `skipNodes 3`;
* `target`: the ring switch's target in tower order is `Σ_cy x^cy Φ_tower(s_cy)`;
* `ring`: the ring claim's weight (`towerCoefficients` on the 64 twists) is `Φ_tower(eq(p, ·))`
  against the column;
* `claim`: `Pending::new`'s claim is `r_lc` plus the terminal's two known terms;
* `sum`: the pending sum (`Pending.G`, `Pending.L` on the setup stacks) is the matrices' part against
  the slices.

Each is stated for every input (the lists the code reads being `List.ofFn` of the cube forms'
functions). **`catches_of_tx`** proves `Catches` from them; **`flockSound_of_tx`** is then the
interface's `FlockSound κ`.

The rest is here: the transcript's shape (`Fits`, from `DoneFits`), the decoded rounds' consistency
(`sc_consistent`, from `decode_consistent`), the code's result as the run's (`outOf_parse`: the
point, the map, the slices, `r_lc`), and each bad event of `Front.Bad` as a hit of `flockBad`
(`hit_of_bad`, by the prefix property).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-! ## The transcript's shape -/

theorem doneFits_rd : ∀ {rs : List Compose.RoundSpec} {done : Done}, DoneFits rs done →
    done.length = rs.length ∧ ∀ a (h : a < rs.length),
      (rd done a).1.2.length = rs[a].nv ∧ (rd done a).2.length = rs[a].ns + 1
  | [], [], _ => ⟨rfl, fun _ h ↦ absurd h (by simp)⟩
  | _ :: _, (_, _) :: _, h => by
    obtain ⟨hm, hc, hd⟩ := h
    obtain ⟨hl, hr⟩ := doneFits_rd hd
    refine ⟨by simp [hl], fun a ha ↦ ?_⟩
    cases a with
    | zero => exact ⟨hm.2, hc⟩
    | succ a => exact hr a (by simpa using ha)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem flockRounds_length (κ : ℕ) : (flockRounds κ).length = 23 + κ := by
  simp only [flockRounds, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate]
  omega

theorem flockRounds_getElem (κ a : ℕ) (h : a < (flockRounds κ).length) :
    (flockRounds κ)[a] = if a = 0 then ⟨false, 0, 3 + κ⟩ else if a = 1 then ⟨false, 8, 0⟩
      else if a < 22 + κ then ⟨false, 2, 0⟩ else ⟨false, 64, 5⟩ := by
  have h' : a < 23 + κ := flockRounds_length κ ▸ h
  simp only [flockRounds, List.getElem_append, List.length_append, List.length_cons,
    List.length_replicate, List.length_nil, List.getElem_replicate, List.getElem_cons]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **The transcript's shape**: `23 + κ` rounds, each of its round's reads and draws. -/
structure Fits (κ : ℕ) (done : Done) : Prop where
  len : done.length = 23 + κ
  r0 : (rd done 0).2.length = 4 + κ
  r1v : (rd done 1).1.2.length = 8
  r1c : (rd done 1).2.length = 1
  mid : ∀ a, 2 ≤ a → a < 22 + κ → (rd done a).1.2.length = 2 ∧ (rd done a).2.length = 1
  r6v : (rd done (22 + κ)).1.2.length = 64
  r6c : (rd done (22 + κ)).2.length = 6

theorem fits_of_doneFits {done : Done} (h : DoneFits (flockRounds κ) done) : Fits κ done := by
  obtain ⟨hl, hr⟩ := doneFits_rd h
  have hL := flockRounds_length κ
  have at_ : ∀ a (ha : a < 23 + κ), (rd done a).1.2.length = ((flockRounds κ)[a]'(by omega)).nv ∧
      (rd done a).2.length = ((flockRounds κ)[a]'(by omega)).ns + 1 :=
    fun a ha ↦ hr a (by omega)
  refine ⟨by omega, ?_, ?_, ?_, fun a h2 h22 ↦ ?_, ?_, ?_⟩
  · have := (at_ 0 (by omega)).2
    rw [flockRounds_getElem] at this
    simp only [ite_true] at this
    omega
  · have := (at_ 1 (by omega)).1
    rw [flockRounds_getElem] at this
    simpa using this
  · have := (at_ 1 (by omega)).2
    rw [flockRounds_getElem] at this
    simpa using this
  · have := at_ a (by omega)
    rw [flockRounds_getElem, ite_eq_right (by omega : ¬a = 0), ite_eq_right (by omega : ¬a = 1),
      ite_eq_left h22] at this
    exact this
  · have := (at_ (22 + κ) (by omega)).1
    rw [flockRounds_getElem, ite_eq_right (by omega : ¬22 + κ = 0), ite_eq_right (by omega : ¬22 + κ = 1),
      ite_eq_right (by omega : ¬22 + κ < 22 + κ)] at this
    exact this
  · have := (at_ (22 + κ) (by omega)).2
    rw [flockRounds_getElem, ite_eq_right (by omega : ¬22 + κ = 0), ite_eq_right (by omega : ¬22 + κ = 1),
      ite_eq_right (by omega : ¬22 + κ < 22 + κ)] at this
    exact this

/-! ## The decoded rounds are consistent -/

/-- **A decoded sumcheck is consistent** (`decode_consistent`): from the claim `c₀ = c`, rounds of
two scalars decoded from the claim before them, with the `eq` factors `w`. Its claims are the
decoding's (`scClaim`). -/
theorem sc_consistent {n : ℕ} (c c₀ : E) (hc : c = c₀) (es : List (Option E)) (d : Done)
    (w : Fin n → Option E) (q : Fin n → E[X]) (χ : Fin n → E)
    (hq : ∀ t : Fin n, q t = msgPoly (decodeMsg (scClaim c es d t) (es.getD t none) (rd d t).1.2))
    (hχ : ∀ t : Fin n, χ t = (rd d t).2.headD 0) (hw : ∀ t : Fin n, es.getD t none = w t)
    (h2 : ∀ t : Fin n, (rd d t).1.2.length = 2) :
    (∀ t : Fin (n + 1), claimAt c₀ q χ t = scClaim c es d t) ∧ Consistent 2 w c₀ q χ := by
  have hclaim : ∀ t : Fin (n + 1), claimAt c₀ q χ t = scClaim c es d t := by
    intro t
    refine Fin.cases ?_ (fun s ↦ ?_) t
    · exact hc.symm
    · show (q s).eval (χ s) = scClaim c es d (s.val + 1)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 s)
      rw [scClaim_succ, hq, hχ, hab, (decode_consistent _ _ a b).2.2]
  refine ⟨hclaim, fun s ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 s)
  obtain ⟨hdeg, hL, -⟩ := decode_consistent (scClaim c es d s) (es.getD s none) a b
  rw [hq s, hab]
  refine ⟨hdeg, ?_⟩
  rw [← hw s, hL, hclaim]
  rfl

/-! ## Lists and their functions -/

theorem fin_append_cast {α : Type} {n m : ℕ} (h : n = 7 + m) (a : Fin 7 → α) (b : Fin m → α)
    (t : Fin n) :
    Fin.append a b (Fin.cast h t) = if ht : t.val < 7 then a ⟨t, ht⟩ else b ⟨t - 7, by omega⟩ := by
  split_ifs with ht
  · have e : Fin.cast h t = Fin.castAdd m ⟨t, ht⟩ := Fin.ext rfl
    rw [e, Fin.append_left]
  · have e : Fin.cast h t = Fin.natAdd 7 ⟨t - 7, by omega⟩ := Fin.ext (by simp; omega)
    rw [e, Fin.append_right]

theorem ofFn_three_parts {α : Type} {a b c : ℕ} (x : Fin (a + b + c) → α) :
    (List.ofFn x).take a = List.ofFn (lowPart (lowPart x)) ∧
      ((List.ofFn x).drop a).take b = List.ofFn (highPart (lowPart x)) ∧
      ((List.ofFn x).drop a).drop b = List.ofFn (highPart x) := by
  have e : List.ofFn x =
      List.ofFn (lowPart (lowPart x)) ++ (List.ofFn (highPart (lowPart x)) ++ List.ofFn (highPart x)) := by
    rw [← List.append_assoc, ← List.ofFn_fin_append, append_lowPart_highPart, ← List.ofFn_fin_append,
      append_lowPart_highPart]
  rw [e]
  refine ⟨List.take_left' (by simp), ?_, ?_⟩
  · rw [List.drop_left' (by simp)]
    exact List.take_left' (by simp)
  · rw [List.drop_left' (by simp)]
    exact List.drop_left' (by simp)

/-- The 64 slices as the code reads them: slice `i` at the cube point of `i`'s bits. -/
def sliceList (s : Cube (3 + 3) → E) : List E :=
  List.ofFn fun i : Fin 64 ↦ s ((cubeFin (3 + 3)).symm i)

theorem eq_sliceList {l : List E} (h : l.length = 64) :
    l = sliceList fun cy ↦ l.getD (cubeFin (3 + 3) cy) 0 := by
  conv_lhs => rw [eq_ofFn_getD h 0]
  rw [sliceList]
  congr 1
  funext i
  simp only [Equiv.apply_symm_apply]

/-! ## What the code's evaluators must be -/

/-- **The evaluator transcription Flock's soundness needs**: the evaluators `Flock.verifyDeferred`
calls (and the interface's `FlockEndHolds`, `PendingHolds` read) equal `FlockSound`'s cube forms, at
every input. -/
structure Tx (κ : ℕ) : Prop where
  /-- `fixed_challenges()` are leanVM's seven fixed coordinates. -/
  fixed : ∀ i : Fin 7, Flock.fixedChallenges.getD i 0 = fixedPt i
  /-- `E::pow` is the power. -/
  epow : ∀ (x : E) (n : ℕ), UniStatement.epow x n = x ^ n
  /-- The skip's start (`lagrange_interpolate(16, [0; 8] ++ coset, z)`) is the interpolant over the
  nodes `φ_8(0..15)` (`skipNodes 3`: the domain zeros, the coset values `cv`) at `z`. -/
  interp : ∀ (cv : Cube 3 → E) (z : E),
    Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ List.ofFn fun i : Fin 8 ↦ cv ((cubeFin 3).symm i)) z =
      (FlockSound.interp (skipNodes 3 (by decide)) cv).eval z
  /-- **The ring switch's target** (`ring_tower::target`): `Σ_i x^i Φ_tower(s_i)`, `Φ_tower` the
  staged map with shifts `1, 2, …, 32` (`towerShifts`) and challenges `f`. -/
  target : ∀ (s : Cube (3 + 3) → E) (f : Fin 6 → E),
    Flock.towerTarget (sliceList s) (List.ofFn f) =
      ∑ cy, packW (k := 3) (l := 3) rfl cy * stagedMap towerShifts f (s cy)
  /-- **The ring claim's weight** (`towerCoefficients` on the 64 Frobenius twists of the point) is
  `Φ_tower(eq(p, ·))` against the column's words. -/
  ring : ∀ (qf : Column (8 + κ)) (p : Fin (8 + κ) → E) (f : Fin 6 → E),
    ∑ k ∈ range 64, (Flock.towerCoefficients (List.ofFn f)).getD k 0 * mleE qf (twist (List.ofFn p) k) =
      ∑ u, stagedMap towerShifts f (eqP p u) * colWord qf u
  /-- **The pending claim** (`Pending::new` with the slices): `r_lc` plus the terminal's known terms,
  `α² eq(χ_in, χ') Σ_cy e(cy) s(cy) + α³ eq(χ', cpos.2) s(cpos.1)`. -/
  claim : ∀ (z α rLc : E) (rl : Fin 3 → E) (rh χ' : Fin 8 → E) (s : Cube (3 + 3) → E),
    (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc (some (sliceList s))).claim =
      rLc + (α ^ 2 * FlockSound.eqEval rh χ' * ∑ cy, lowW (skipNodes 3 (by decide)) z rl cy * s cy +
        α ^ 3 * eqP χ' ((posFin (k := 3) (l := 3) rfl).symm Lv42.Parameters.Flock.constPos).2 *
          s ((posFin (k := 3) (l := 3) rfl).symm Lv42.Parameters.Flock.constPos).1)
  /-- **The pending sum** (`Σ_u G(u) L(u)` on the setup stacks `A0`, `B0`) is the matrices' part of
  the lincheck's terminal against the slices. -/
  sum : ∀ (z α rLc : E) (rl : Fin 3 → E) (rh χ' : Fin 8 → E) (s : Cube (3 + 3) → E),
    ∑ u ∈ range (2 ^ (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
        (some (sliceList s))).rounds),
      Pending.G (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
          (some (sliceList s))) u *
        Pending.L (Flock.Pending.new (some z) (List.ofFn rl) (List.ofFn rh) (List.ofFn χ') α rLc
          (some (sliceList s))) u =
      ∑ cy, matPart (cubeMat (k := 3) (l := 3) rfl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A)
        (cubeMat (k := 3) (l := 3) rfl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B)
        (skipNodes 3 (by decide)) z rl rh χ' α cy * s cy

/-! ## The code's result is the run's -/

theorem outOf_eq (d : Done) :
    outOf κ d = flockOut (pSampled d) (pCoset d) (pZ d) ((d.drop 2).take (11 + κ)) (pVa κ d)
      (pVb κ d) (pAlpha κ d) ((d.drop (14 + κ)).take 8) (rd d (22 + κ)).1.2 (rd d (22 + κ)).2 := by
  simp only [outOf, rd_drop, Nat.add_zero]
  rfl

theorem flockOut_of (sampled coset : List E) (z : E) (zc : Done) (vA vB α : E) (lc : Done)
    (slices map zs ls : List E) (running rLc : E)
    (hzr : decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ coset) z)
      ((Flock.fixedChallenges ++ sampled).map some) zc = (zs, running))
    (hlr : decodeSC (vA + α * vB + epow α 2 * (running + vA * vB) + epow α 3) (List.replicate 8 none) lc =
      (ls, rLc)) :
    flockOut sampled coset z zc vA vB α lc slices map =
      (ls.reverse ++ (zs.drop 3).drop 8, some (.ring map (Flock.towerTarget slices map)),
        Flock.Pending.new (some z) (zs.take 3) ((zs.drop 3).take 8) ls.reverse α rLc (some slices)) := by
  simp only [flockOut, hzr, hlr]

theorem getD_replicate_none (t : Fin 8) : (List.replicate 8 (none : Option E)).getD t none = none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, t.isLt, ite_true, Option.getD_some]

section Run

variable (tx : Tx κ) {done : Done} (hF : Fits κ done)
include tx hF

/-- The parsed run's zerocheck point is the code's `eq` factors. -/
theorem pEs_getD (t : Fin (3 + 8 + κ)) :
    (pEs done).getD t none = some (Front.τ (mainSetup κ) (parse κ done) t) := by
  have hlen : (Flock.fixedChallenges ++ pSampled done).length = 3 + 8 + κ := by
    simp only [List.length_append, length_fixedChallenges, pSampled, hF.r0]
    omega
  have ht := t.isLt
  have e1 : (pEs done).getD t none = some ((Flock.fixedChallenges ++ pSampled done).getD t 0) := by
    simp only [pEs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show t.val < (Flock.fixedChallenges ++ pSampled done).length by omega),
      Option.map_some, Option.getD_some]
  rw [e1]
  congr 1
  show _ = Fin.append fixedPt (parse κ done).τs (Fin.cast _ t)
  rw [fin_append_cast]
  split_ifs with h7
  · rw [← tx.fixed]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left
      (show t.val < Flock.fixedChallenges.length by rw [length_fixedChallenges]; exact h7)]
  · show _ = (pSampled done).getD (t - 7) 0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right
      (show Flock.fixedChallenges.length ≤ t.val by rw [length_fixedChallenges]; omega),
      length_fixedChallenges]

/-- **The zerocheck is consistent**, and its claims are the code's. -/
theorem zc_consistent :
    (∀ t : Fin (3 + 8 + κ + 1), claimAt (Front.c₀ (mainSetup κ) (parse κ done)) (parse κ done).zq
      (parse κ done).zχ t = scClaim (pC0 done) (pEs done) (done.drop 2) t) ∧
    Consistent 2 (fun i ↦ some (Front.τ (mainSetup κ) (parse κ done) i))
      (Front.c₀ (mainSetup κ) (parse κ done)) (parse κ done).zq (parse κ done).zχ := by
  refine sc_consistent (pC0 done) _ ?_ (pEs done) (done.drop 2) _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
    (pEs_getD tx hF) fun t ↦ ?_
  · have hc : pCoset done = List.ofFn fun i : Fin 8 ↦ (parse κ done).cv ((cubeFin 3).symm i) := by
      show (rd done 1).1.2 = _
      conv_lhs => rw [eq_ofFn_getD hF.r1v 0]
      congr 1
      funext i
      show _ = (pCoset done).getD (cubeFin 3 ((cubeFin 3).symm i)) 0
      rw [Equiv.apply_symm_apply]
      rfl
    show Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ pCoset done) (pZ done) = _
    rw [hc, tx.interp]
    rfl
  · rw [rd_drop]
    exact (hF.mid _ (by omega) (by have := t.isLt; omega)).1

theorem running_eq : Front.running (mainSetup κ) (parse κ done) = pRunning κ done :=
  (zc_consistent tx hF).1 (Fin.last _)

/-- **The lincheck is consistent**, and its claims are the code's. -/
theorem lin_consistent :
    (∀ t : Fin (8 + 1), claimAt (Front.linC₀ (mainSetup κ) (parse κ done)) (parse κ done).lq
      (parse κ done).lχ t = scClaim (pLc0 κ done) (List.replicate 8 none) (done.drop (14 + κ)) t) ∧
    Consistent 2 (fun _ ↦ none) (Front.linC₀ (mainSetup κ) (parse κ done)) (parse κ done).lq
      (parse κ done).lχ := by
  refine sc_consistent (pLc0 κ done) _ ?_ (List.replicate 8 none) (done.drop (14 + κ)) _ _ _
    (fun t ↦ ?_) (fun _ ↦ rfl) (fun t ↦ getD_replicate_none t) fun t ↦ ?_
  · show _ = (parse κ done).va + (parse κ done).α * (parse κ done).vb +
      (parse κ done).α ^ 2 * (Front.running (mainSetup κ) (parse κ done) + (parse κ done).va *
        (parse κ done).vb) + (parse κ done).α ^ 3
    rw [running_eq tx hF, ← tx.epow, ← tx.epow]
    rfl
  · show msgPoly (decodeMsg _ none _) = msgPoly (decodeMsg _ _ _)
    rw [getD_replicate_none]
  · rw [rd_drop]
    exact (hF.mid _ (by omega) (by have := t.isLt; omega)).1

omit tx in
theorem decode_zc :
    decodeSC (Flock.lagrangeInterpolate 16 (List.replicate 8 0 ++ pCoset done) (pZ done))
        ((Flock.fixedChallenges ++ pSampled done).map some) ((done.drop 2).take (11 + κ)) =
      (List.ofFn (parse κ done).zχ, pRunning κ done) := by
  have hl : ((done.drop 2).take (11 + κ)).length = 11 + κ := by
    simp only [List.length_take, List.length_drop, hF.len]
    omega
  have hes : ((Flock.fixedChallenges ++ pSampled done).map some).length = 11 + κ := by
    simp only [List.length_map, List.length_append, length_fixedChallenges, pSampled, hF.r0]
    omega
  rw [decodeSC_eq _ _ _ (hl.trans hes.symm), hes, map_eq_ofFn hl noRound]
  congr 1
  · congr 1
    funext t
    show (rd ((done.drop 2).take (11 + κ)) t).2.headD 0 = (rd (done.drop 2) t).2.headD 0
    rw [rd_take t.isLt]
  · exact scClaim_congr _ _ _ fun v hv ↦ rd_take hv

theorem decode_lin :
    decodeSC (pVa κ done + pAlpha κ done * pVb κ done +
        epow (pAlpha κ done) 2 * (pRunning κ done + pVa κ done * pVb κ done) + epow (pAlpha κ done) 3)
        (List.replicate 8 none) ((done.drop (14 + κ)).take 8) =
      (List.ofFn (parse κ done).lχ, Front.rlc (mainSetup κ) (parse κ done)) := by
  have hl : ((done.drop (14 + κ)).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, hF.len]
    omega
  rw [decodeSC_eq _ _ _ (hl.trans (List.length_replicate ..).symm), List.length_replicate,
    map_eq_ofFn hl noRound]
  congr 1
  · congr 1
    funext t
    show (rd ((done.drop (14 + κ)).take 8) t).2.headD 0 = (rd (done.drop (14 + κ)) t).2.headD 0
    rw [rd_take t.isLt]
  · rw [scClaim_congr _ _ _ fun v hv ↦ rd_take hv]
    exact ((lin_consistent tx hF).1 (Fin.last 8)).symm

/-- **The code's result is the run's**: the point of the words, the ring map, the target of the
sent slices, and the pending reduction at the run's row and column points, `α`, `r_lc` and slices. -/
theorem outOf_parse :
    outOf κ done =
      (List.ofFn (Front.p (mainSetup κ) (parse κ done)),
        some (.ring (List.ofFn (parse κ done).f)
          (Flock.towerTarget (sliceList (parse κ done).s) (List.ofFn (parse κ done).f))),
        Flock.Pending.new (some (parse κ done).z) (List.ofFn (Front.rl (mainSetup κ) (parse κ done)))
          (List.ofFn (Front.rh (mainSetup κ) (parse κ done)))
          (List.ofFn (Front.χ' (mainSetup κ) (parse κ done))) (parse κ done).α
          (Front.rlc (mainSetup κ) (parse κ done)) (some (sliceList (parse κ done).s))) := by
  obtain ⟨h3, h8, h8'⟩ := ofFn_three_parts (a := 3) (b := 8) (c := κ) (parse κ done).zχ
  have hmap : (rd done (22 + κ)).2 = List.ofFn (parse κ done).f := eq_ofFn_getD hF.r6c 0
  have hsl : (rd done (22 + κ)).1.2 = sliceList (parse κ done).s := eq_sliceList hF.r6v
  rw [outOf_eq, flockOut_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ (decode_zc hF) (decode_lin tx hF), h3, h8,
    h8', reverse_ofFn, hmap, hsl]
  congr 1
  rw [← List.ofFn_fin_append]
  rfl

end Run

/-! ## Each bad event is a hit -/

section Hit

variable (qf : Column (8 + κ)) (R : Front E 3 3 8 κ (4 + κ) 6)

theorem badAt_τ (a : Fin (4 + κ)) :
    badAt qf R 0 a = pointBad (4 + κ) (sampledTables (mainSetup κ).hsize (mainSetup κ).fixed
      (Front.zRes (mainSetup κ) (zOf qf))) R.τs a := by
  unfold badAt
  rw [ite_eq_left rfl, dite_eq_left a.isLt]

theorem badAt_z :
    badAt qf R 1 0 = skipBad (mainSetup κ).node (Front.zA (mainSetup κ) (zOf qf))
      (Front.zB (mainSetup κ) (zOf qf)) (Front.zZ (zOf qf)) (Front.τ (mainSetup κ) R) R.cv := by
  unfold badAt
  rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl]

theorem badAt_zc (t : Fin (3 + 8 + κ)) :
    badAt qf R (2 + t) 0 = zcBad (mainSetup κ).node (Front.zA (mainSetup κ) (zOf qf))
      (Front.zB (mainSetup κ) (zOf qf)) (Front.zZ (zOf qf)) (pinTab (zOf qf) (mainSetup κ).cpos)
      (Front.τ (mainSetup κ) R) R.z (Front.c₀ (mainSetup κ) R) R.zq R.zχ t := by
  have := t.isLt
  unfold badAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega), ite_eq_left rfl]
  congr 1
  ext
  simp

theorem badAt_α :
    badAt qf R (13 + κ) 0 = alphaBad R.va R.vb (Front.vc (mainSetup κ) R)
      (skipVal (mainSetup κ).node (Front.zA (mainSetup κ) (zOf qf)) R.z R.zχ)
      (skipVal (mainSetup κ).node (Front.zB (mainSetup κ) (zOf qf)) R.z R.zχ)
      (skipVal (mainSetup κ).node (Front.zZ (zOf qf)) R.z R.zχ)
      (zhat (zOf qf) (Front.rt (mainSetup κ) R) (mainSetup κ).cpos) := by
  unfold badAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left rfl,
    ite_eq_left rfl]

theorem badAt_lin (t : Fin 8) :
    badAt qf R (14 + κ + t) 0 = sumBad 2 8 (fun _ ↦ none)
      (linRev (linFun (mainSetup κ).A (mainSetup κ).B (zOf qf) (mainSetup κ).cpos (mainSetup κ).node
        R.z (Front.rl (mainSetup κ) R) (Front.rh (mainSetup κ) R) (Front.rt (mainSetup κ) R) R.α))
      R.lq R.lχ t := by
  have := t.isLt
  unfold badAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
    ite_eq_right (by omega), dite_eq_left (by omega), ite_eq_left rfl]
  congr 1
  ext
  simp

theorem badAt_ring (a : Fin (mainSetup κ).sh.length) :
    badAt qf R (22 + κ) a = ringBad univ (mainSetup κ).w (mainSetup κ).sh
      (fun cy ↦ R.s cy - strue (zOf qf) (Front.rt (mainSetup κ) R) (Front.χ' (mainSetup κ) R) cy) R.f
      a := by
  unfold badAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
    ite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left rfl,
    dite_eq_left (show (a : ℕ) < 6 from a.isLt)]

/-- **Each of `Front.Bad`'s events on the transcript's parse is a hit of `flockBad`.** -/
theorem hit_of_bad {done : Done} (hF : Fits κ done)
    (hbad : Front.Bad (mainSetup κ) (parse κ done) (zOf qf)) : HitIn (flockBad κ) qf done := by
  have hl := hF.len
  unfold Front.Bad at hbad
  rcases hbad with ⟨a, ha⟩ | hz | ⟨t, ht⟩ | hα | ⟨t, ht⟩ | ⟨a, ha⟩
  · refine hitIn_of_mem qf (j := 0) (i := a) (by omega) (by rw [hF.r0]; exact a.isLt) ?_
    rw [badAt_τ]
    exact ha
  · refine hitIn_of_mem qf (j := 1) (i := 0) (by omega) (by rw [hF.r1c]; omega) ?_
    rw [badAt_z, ← headD_eq_getD']
    exact hz
  · have ht2 := t.isLt
    refine hitIn_of_mem qf (j := 2 + t) (i := 0) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAt_zc, ← headD_eq_getD', ← rd_drop]
    exact ht
  · refine hitIn_of_mem qf (j := 13 + κ) (i := 0) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAt_α, ← headD_eq_getD']
    exact hα
  · have ht8 := t.isLt
    refine hitIn_of_mem qf (j := 14 + κ + t) (i := 0) (by omega)
      (by rw [(hF.mid _ (by omega) (by omega)).2]; omega) ?_
    rw [badAt_lin, ← headD_eq_getD', ← rd_drop]
    exact ht
  · refine hitIn_of_mem qf (j := 22 + κ) (i := a) (by omega)
      (by rw [hF.r6c]; exact (show (a : ℕ) < 6 from a.isLt)) ?_
    rw [badAt_ring]
    exact ha

end Hit

/-! ## The catch, and the interface -/

/-- **The bad family catches, given the evaluator transcription**: on a completed transcript whose
ring claim holds of the column and whose pending claim is its sum, the column satisfies Flock's
relation or a challenge is in its bad set (`flock_front` at leanVM's constants on the parse). -/
theorem catches_of_tx (tx : Tx κ) : Catches (flockProg κ) (flockBad κ) := by
  intro qf done hfit hend hpend
  have hF := fits_of_doneFits hfit
  by_cases hold : FlockHolds κ qf
  · exact Or.inl hold
  right
  have hend' : FlockEndHolds qf (outOf κ done) := hend
  have hpend' : PendingHolds (outOf κ done).2.2 := hpend
  rw [outOf_parse tx hF] at hend' hpend'
  have hring : ∑ u, stagedMap (mainSetup κ).sh (parse κ done).f
      (eqP (Front.p (mainSetup κ) (parse κ done)) u) * colWord qf u =
      Front.target (mainSetup κ) (parse κ done) := by
    have h := hend'
    simp only [FlockEndHolds] at h
    rw [tx.ring, tx.target] at h
    exact h
  have hnot : ¬ R1CSHolds (mainSetup κ).A (mainSetup κ).B (zOf qf) (mainSetup κ).cpos :=
    fun h ↦ hold ((r1csHolds_iff rfl _ qf).mp h)
  rcases flock_front (mainSetup κ)
      (leanvmSetup_valid 3 3 κ (4 + κ) rfl (by decide) (by omega) towerShifts (Or.inr rfl) _ _ _)
      (zOf qf) (colBits_bool rfl qf) (colWord qf) (colPack rfl qf) (parse κ done)
      (zc_consistent tx hF).2 (lin_consistent tx hF).2 hring hnot with hbad | hfalse
  · exact hit_of_bad qf hF hbad
  · exfalso
    apply hfalse
    have h := hpend'
    unfold PendingHolds at h
    rw [tx.sum, tx.claim] at h
    exact h

/-- **Flock's interface from the evaluator transcription**: the chain program `flockProg κ`, its link
(`flock_link`), the bad family `flockBad κ` with its sizes `dBound κ`, which catches given `Tx κ`. -/
noncomputable def flockSound_of_tx (tx : Tx κ) : FlockSound κ :=
  ofFamily (flockProg κ) (flockProg_root κ) (flockProg_tail κ) (fun F ↦ flock_link κ F) (flockBad κ)
    (dBound κ) (card_flockBad κ) (catches_of_tx tx)

/-! ## The rounds' errors -/

/-- **Round `j`'s error, times `|E|`**: `4 + κ` for `τ` (one value per coordinate), `15` for `z`,
`2` for each zerocheck round, `3` for `α`, `2` for each lincheck round, `6` for the ring map. -/
def roundErr (κ j : ℕ) : ℕ :=
  if j = 0 then 4 + κ else if j = 1 then 15 else if j < 13 + κ then 2 else if j = 13 + κ then 3
  else if j < 22 + κ then 2 else 6

open scoped ENNReal in
theorem flockSound_err (tx : Tx κ) (j : ℕ) (hj : j < 23 + κ) :
    (flockSound_of_tx tx).err j = (roundErr κ j : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  show ((∑ i ∈ range ((((flockRounds κ)[j]?).map (·.ns)).getD 0 + 1), dBound κ j i : ℕ) : ℝ≥0∞) /
    (Fintype.card E : ℝ≥0∞) = _
  have hj' : j < (flockRounds κ).length := by rw [flockRounds_length]; exact hj
  rw [List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some, flockRounds_getElem]
  congr 2
  unfold roundErr dBound
  split_ifs <;> simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] <;> omega

theorem roundErr_zc {j : ℕ} (h1 : 2 ≤ j) (h2 : j < 13 + κ) : roundErr κ j = 2 := by
  unfold roundErr
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

theorem roundErr_lin {j : ℕ} (h1 : 14 + κ ≤ j) (h2 : j < 22 + κ) : roundErr κ j = 2 := by
  unfold roundErr
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left h2]

theorem sum_roundErr (κ : ℕ) : ∑ j ∈ range (23 + κ), roundErr κ j = 66 + 3 * κ := by
  rw [show 23 + κ = 2 + ((11 + κ) + (1 + (8 + 1))) by omega,
    Finset.sum_range_add (roundErr κ) 2, Finset.sum_range_add _ (11 + κ), Finset.sum_range_add _ 1,
    Finset.sum_range_add _ 8]
  have e2 : ∑ x ∈ range 2, roundErr κ x = 19 + κ := by
    have h0 : roundErr κ 0 = 4 + κ := by unfold roundErr; rw [ite_eq_left rfl]
    have h1 : roundErr κ 1 = 15 := by unfold roundErr; rw [ite_eq_right (by omega), ite_eq_left rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
    omega
  have hzc : ∀ x ∈ range (11 + κ), roundErr κ (2 + x) = 2 := fun x hx ↦
    roundErr_zc (by omega) (by have := Finset.mem_range.mp hx; omega)
  have hlin : ∀ x ∈ range 8, roundErr κ (2 + (11 + κ + (1 + x))) = 2 := fun x hx ↦
    roundErr_lin (by omega) (by have := Finset.mem_range.mp hx; omega)
  have eα : roundErr κ (2 + (11 + κ + 0)) = 3 := by
    unfold roundErr
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  have er : roundErr κ (2 + (11 + κ + (1 + (8 + 0)))) = 6 := by
    unfold roundErr
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [e2, Finset.sum_congr rfl hzc, Finset.sum_congr rfl hlin, Finset.sum_range_one,
    Finset.sum_range_one, eα, er]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

open scoped ENNReal in
/-- **Flock's error per candidate**: `(66 + 3κ)/|E|`, the sum of its rounds' errors. -/
theorem flockSound_error (tx : Tx κ) :
    (flockSound_of_tx tx).flockError = ((66 + 3 * κ : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have hl : (flockSound_of_tx tx).prog.rounds.length = 23 + κ := flockRounds_length κ
  rw [FlockSound.flockError, hl, Finset.sum_congr rfl fun j hj ↦
    flockSound_err tx j (Finset.mem_range.mp hj), ← sum_roundErr κ, Nat.cast_sum]
  simp only [ENNReal.div_eq_inv_mul, Finset.mul_sum]

end FlockSound.Uni
