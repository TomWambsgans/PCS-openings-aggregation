-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockPure
import RecGraph.Sim.FlockWalk

/-!
# The walked terminal, simulated: `Pi1.walkedTerminal` against `UniStatement.Flock.walkedTerminal`

The column weights `w = s ⊗ eq(chi_in')` (the program's loops over the zipped lists, `UniStatement`'s over the
ranges), the walk (`blake2sRowValues_ph`), the matrix sum weighed by `eq(chi_in)` and the low weights, the known
weights' terms.
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

theorem eqKernel_size_aux (A : Array E) (xs : List E) :
    (xs.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) A).size = A.size * 2 ^ xs.length := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih]; simp [Nat.pow_succ]; ring

theorem eqKernel_size (xs : List E) : (UniStatement.eqKernel xs).size = 2 ^ xs.length := by
  unfold UniStatement.eqKernel
  rw [eqKernel_size_aux]; simp

theorem getD_toArray_eq (l : List E) (i : ℕ) (h : i < l.length) : l.toArray.getD i 0 = l[i] := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_eq_toList (A : Array E) (i : ℕ) (h : i < A.size) : A.getD i 0 = A.toList[i]'(by simpa using h) := by
  simp [Array.getD_eq_getD_getElem?, h]

section Terminal

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream
local notation "PZ" => PH.zero (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)

theorem RpL.getD' {st : RecState} {l : List Sym} {xs : List E} (h : RpL' st l xs) {i : ℕ} (hi : i < xs.length) :
    Rp' st (l.getD i 0) (xs.getD i 0) := by
  have hl := h.length
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact h.get i (by omega) hi

/-- **`walked_terminal(z_skip, row_low, chi_in, chi_in', s, α)`**. -/
theorem walkedTerminal_ph {st : RecState} (hg : Good st) {zSkip : Option Sym} {zS : Option E}
    (hz : OptRp π iv publicInput stream st zSkip zS) {rowLow chiIn chiInPrime s : List Sym} {RL CI CIP S : List E}
    (hrl : RpL' st rowLow RL) (hci : RpL' st chiIn CI) (hcip : RpL' st chiInPrime CIP) (hs : RpL' st s S)
    {alpha : Sym} {a : E} (ha : Rp' st alpha a) (hCI : CI.length = 8) (hS : S.length = 64)
    (hLW : (Flock.rowLowWeights zS RL).2.length ≤ 64) :
    PH (Pi1.walkedTerminal zSkip rowLow chiIn chiInPrime s alpha) st
      (fun st' r ↦ Rp' st' r (Flock.walkedTerminal zS RL CI CIP S a)) := by
  have hN : (2 : ℕ) ^ blake2sR1csLogSize = 16384 := by simp [blake2sR1csLogSize]
  have hslen := hs.length
  generalize hW : Flock.walkedTerminal zS RL CI CIP S a = W
  unfold Pi1.walkedTerminal
  dsimp only
  subst hW
  unfold Flock.walkedTerminal
  dsimp (config := { iota := false, proj := false }) only [Id.run]
  split
  rename_i fst lw hrlw
  rw [hrlw] at hLW
  dsimp only at hLW
  phg (rowLowWeights_ph hg hz hrl) as st1 rl hs1 hrl'
  rw [hrlw] at hrl'
  dsimp only at hrl'
  obtain ⟨_, hlw⟩ := hrl'
  have hlwlen := hlw.length
  phg (eqKernel_ph hg hcip) as st2 high hs2 hhigh
  have hhl := hhigh.length
  rw [Array.length_toList, Array.length_toList] at hhl
  phg (PZ hg) as st3 z hs3 hz3
  generalize hU1 : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E) _ _ _) = U1
  rw [idBind]
  rw [forIn_range_list] at hU1
  -- The column weights.
  refine PH.bind' (PH.forIn_rel2 _ _ (by simp [hhl]) _ _ _ _ hU1 st3
    (fun st' (w : Array Sym) (u : Array E) ↦ RpA' st' w u ∧ w.size = 2 ^ blake2sR1csLogSize) hg
    ⟨RpA.replicate hz3 _, by simp⟩ ?_) ?_
  · intro j hj hj' st' w u hs' ⟨hw, hwsz⟩
    grow_all hg hs'
    simp only [List.length_zip, List.length_range, Array.length_toList, Nat.min_self] at hj
    simp only [List.getElem_zip, List.getElem_range, List.getElem_range', Nat.zero_add, Nat.one_mul]
    have hjE : j < (UniStatement.eqKernel CIP).size := hhl ▸ hj
    have hh := hhigh.get j (by simpa using hj) (by simpa using hjE)
    generalize hV : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E) _ _ _) = V
    rw [idBind]
    rw [forIn_range_list] at hV
    refine PH.bind' (PH.forIn_rel2 _ _ (by simp [hslen]) _ _ _ _ hV st'
      (fun st'' (w' : Array Sym) (v : Array E) ↦ RpA' st'' w' v ∧ w'.size = 2 ^ blake2sR1csLogSize) hg
      ⟨hw, hwsz⟩ ?_) ?_
    · intro l hl hl' st'' w' v hs'' ⟨hw', hwsz'⟩
      grow_all hg hs''
      simp only [List.length_zip, List.length_range, Nat.min_self] at hl
      simp only [List.getElem_zip, List.getElem_range, List.getElem_range', Nat.zero_add, Nat.one_mul]
      have hsl := hs.get l hl (by omega)
      phg (PH.mul hg hsl hh) as st4 m hs4 hm
      rw [getD_toArray_eq _ _ (by omega), getD_eq_toList _ _ hjE]
      exact PH.ret hg ⟨_, _, rfl, rfl, hw'.set hm _, by simp [hwsz']⟩
    · rintro st'' w' hs'' hR
      exact PH.ret hs''.good ⟨_, _, rfl, rfl, hR⟩
  rintro st4 w hs4 ⟨hw, hwsz⟩
  grow_all hg hs4
  -- The walk.
  phg (blake2sRowValues_ph hg hw (by rw [← hw.1, hwsz])) as st5 lr hs5 hlr
  split
  rename_i left right hb
  rw [hb] at hlr
  obtain ⟨hleft, hright, hlsz, hrsz⟩ := hlr
  phg (eqKernel_ph hg hci) as st6 rows hs6 hrows
  have hrl2 := hrows.length
  rw [Array.length_toList, Array.length_toList, eqKernel_size, hCI] at hrl2
  phg (PZ hg) as st7 m0 hs7 hm0
  generalize hU2 : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := E) _ _ _) = U2
  rw [idBind]
  rw [forIn_range_list] at hU2
  -- The matrix's sum.
  refine PH.bind' (PH.forIn_rel2 _ _ (by simp [hrl2, eqKernel_size, hCI]) _ _ _ _ hU2 st7
    (fun st' (m : Sym) (u : E) ↦ Rp' st' m u) hg hm0 ?_) ?_
  · intro j hj hj' st' m u hs' hmu
    grow_all hg hs'
    simp only [List.length_zip, List.length_range] at hj
    simp only [List.getElem_zip, List.getElem_range, List.getElem_range', Nat.zero_add, Nat.one_mul]
    have hrw := hrows.get j (by simpa using hj) (by simpa [eqKernel_size, hCI] using (show j < 256 by omega))
    phg (PZ hg) as st8 l0 hs8 hl0
    phg (PZ hg) as st9 r0 hs9 hr0
    generalize hV : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := E × E) _ _ _) = V
    rw [idBind]
    rw [forIn_range_list] at hV
    refine PH.bind' (PH.forIn_rel2 _ _ (by simp [hlwlen]) _ _ _ _ hV st9
      (fun st'' (p : Sym × Sym) (v : E × E) ↦ Rp' st'' p.1 v.1 ∧ Rp' st'' p.2 v.2) hg ⟨hl0, hr0⟩ ?_) ?_
    · intro k hk hk' st'' p v hs'' ⟨hp1, hp2⟩
      grow_all hg hs''
      simp only [List.length_zip, List.length_range, Nat.min_self] at hk
      simp only [List.getElem_zip, List.getElem_range, List.getElem_range', Nat.zero_add, Nat.one_mul]
      have hwk := hlw.get k hk (by omega)
      have hlv := hleft.get (i := j * Flock.kBits + k) (by rw [← hleft.1, hlsz, hN]; simp [Flock.kBits]; omega)
      have hrv := hright.get (i := j * Flock.kBits + k) (by rw [← hright.1, hrsz, hN]; simp [Flock.kBits]; omega)
      phg (PH.mul hg hwk hlv) as st10 pl hs10 hpl
      phg (PH.add hg hp1 hpl) as st11 ls hs11 hls
      phg (PH.mul hg hwk hrv) as st12 pr hs12 hpr
      phg (PH.add hg hp2 hpr) as st13 rs hs13 hrs
      rw [getD_toArray_eq _ _ (by omega)]
      exact PH.ret hg ⟨_, _, rfl, rfl, hls, hrs⟩
    · rintro st'' p hs'' ⟨hp1, hp2⟩
      grow_all hg hs''
      phg (PH.mul hg ha hp2) as st10 ar hs10 har
      phg (PH.add hg hp1 har) as st11 lr' hs11 hlr'
      phg (PH.mul hg hrw hlr') as st12 rw' hs12 hrw'
      phg (PH.add hg hmu hrw') as st13 m' hs13 hm'
      rw [getD_eq_toList _ _ (by rw [eqKernel_size, hCI]; omega)]
      exact PH.ret hg ⟨_, _, rfl, rfl, hm'⟩
  rintro st8 m hs8 hm
  grow_all hg hs8
  -- The known terms.
  phg (knownWeights_ph hg ha hci hcip) as st9 kw hs9 hkw
  split
  rename_i cW pW hk
  rw [hk] at hkw
  obtain ⟨hcW, hpW⟩ := hkw
  phg (PSim.ph (dot_psim st9 hg hlw hs)) as st10 d hs10 hd
  phg (PH.mul hg hcW hd) as st11 cd hs11 hcd
  phg (PH.add hg hm hcd) as st12 m1 hs12 hm1
  phg (PH.mul hg hpW (hs.getD' (i := Flock.constantColumn % Flock.kBits) (by
    rw [hS]; simp [Flock.constantColumn, Flock.kBits]))) as st13 ps hs13 hps
  exact PH.add hg hm1 hps

end Terminal

end RecGraph.Sim
