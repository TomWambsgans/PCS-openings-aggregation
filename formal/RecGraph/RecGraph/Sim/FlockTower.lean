-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockNet
import RecGraph.Sim.FlockPure

/-!
# The tower target, simulated: `Pi1.towerTarget` against `UniStatement.Flock.towerTarget`

The program adds the 64 leaves by the `XOR` network (`towerNetwork`), `UniStatement` sums each leaf's slices
directly; by the network's invariant (`xorNetwork_inv`) each leaf's variables sum to its mask's slices. Then six
levels, each pairing the nodes `(a, b) ↦ (a + θ_j b) + f_j (a^(|F_j|) + θ_j b^(|F_j|))`, the powers by `2^j`
squarings (`sqn`).
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

theorem foldl_add_eq (f : ℕ → E) (l : List ℕ) (c : E) :
    l.foldl (fun a v ↦ a + f v) c = c + (l.map f).sum := by
  induction l generalizing c with
  | nil => simp
  | cons v t ih => rw [List.foldl_cons, ih]; simp; ring

theorem list_getD_toArray (S : List E) (i : ℕ) : S.toArray.getD i 0 = S.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `UniStatement`'s leaf: the sum of the slices its mask names. -/
theorem uleaf_eq (S : List E) (mask : ℕ) :
    (List.range Flock.kBits).foldl (fun acc i ↦ if mask.testBit i = true then acc + S.getD i 0 else acc) 0 =
      rowSum S.toArray (leafRow mask) := by
  rw [← List.foldl_filter (p := fun i ↦ mask.testBit i) (f := fun acc i ↦ acc + S.getD i 0)]
  rw [foldl_add_eq, zero_add, rowSum, leafRow]
  congr 1
  exact List.map_congr_left fun i _ ↦ (list_getD_toArray S i).symm

theorem towerNetwork_inv :
    NetInv Flock.towerLeaves Pi1.towerNetwork.2.toArray Pi1.towerNetwork.1.toArray :=
  xorNetwork_inv Flock.towerLeaves

section Tower

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream
local notation "PZ" => PH.zero (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)
local notation "PC" => PH.const (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)

/-- `2^j` squarings. -/
theorem squarings_ph {st : RecState} (hg : Good st) {a : Sym} {x : E} (ha : Rp' st a x) (n : ℕ)
    (f : ℕ → Sym → Prog (ForInStep Sym))
    (hf : ∀ i s, f i s = (Pi1.square s >>= fun s' ↦ pure (ForInStep.yield s'))) :
    PH (forIn ({ start := 0, stop := n, step := 1, step_pos := Nat.one_pos } : Std.Legacy.Range) a f) st
      (fun st' r ↦ Rp' st' r (sqn x n)) := by
  have := PH.forIn_range 0 n a f st (fun j st' s ↦ Rp' st' s (sqn x j)) hg ha fun j _ st' s hs' hj ↦ by
    rw [hf]
    exact PH.bind' (PH.square hs'.good hj) fun st'' s' hs'' h' ↦
      PH.ret hs''.good ⟨_, rfl, by rw [sqn_succ']; exact h'⟩
  simpa using this

/-- **`ring_tower::target(slices, map)`**: the leaves by the `XOR` network, then six levels. -/
theorem towerTarget_ph {st : RecState} (hg : Good st) {slices map : List Sym} {S M : List E}
    (hs : RpL' st slices S) (hm : RpL' st map M) (hS : S.length = Flock.kBits) (hM : M.length = Flock.towerStages) :
    PH (Pi1.towerTarget slices map) st (fun st' r ↦ Rp' st' r (Flock.towerTarget S M)) := by
  have hslen := hs.length
  have hmlen := hm.length
  unfold Flock.towerTarget
  dsimp (config := { iota := false, proj := false }) only [Id.run]
  generalize hU : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E) _ _ _) = U
  rw [idBind]
  unfold Pi1.towerTarget
  have hinv := towerNetwork_inv
  split
  rename_i xors sums hnet
  rw [hnet] at hinv
  have hsumsz : sums.length = Flock.kBits := by
    have := hinv.size; simp only [List.size_toArray] at this; rw [this, towerLeaves_size]
  dsimp only
  -- The network's variables.
  refine PH.bind' (PH.forIn_list xors slices.toArray _ st
    (fun j st' (V : Array Sym) ↦ RpA' st' V (netVals S.toArray (xors.take j)) ∧ V.size = Flock.kBits + j) hg
    ⟨by simpa [netVals] using hs.toRpA, by simp [hslen, hS]⟩ ?_) ?_
  · intro j hj st' V hs' ⟨hV, hVs⟩
    grow_all hg hs'
    have hx := hinv.xlt j (by simpa using hj)
    simp only [List.getElem_toArray] at hx
    have hsz : (netVals S.toArray (xors.take j)).size = Flock.kBits + j := by
      rw [netVals_size]; simp [hS]; omega
    have h1 := hV.get (i := xors[j].1) (by omega)
    have h2 := hV.get (i := xors[j].2) (by omega)
    phg (PH.add hg h1 h2) as st1 d hs1 hd
    refine PH.ret hg ⟨_, rfl, ?_, by simp [hVs]; omega⟩
    rw [take_succ_getElem _ _ hj, netVals_snoc]
    exact hV.push hd
  rintro st1 V hs1 ⟨hV, hVs⟩
  grow_all hg hs1
  rw [List.take_length] at hV
  set VV := netVals S.toArray xors with hVV
  have hVVs : VV.size = Flock.kBits + xors.length := by rw [hVV, netVals_size]; simp [hS]
  -- The leaves.
  refine PH.bind' (PH.forIn_list sums #[] _ st1
    (fun j st' (N : Array Sym) ↦ N.size = j ∧ ∀ w < j, Rp' st' (N.getD w 0)
      ((List.range Flock.kBits).foldl (fun acc i ↦
        if (Flock.towerLeaves.getD w 0).testBit i = true then acc + S.getD i 0 else acc) 0)) hg
    ⟨rfl, fun w hw ↦ absurd hw (Nat.not_lt_zero w)⟩ ?_) ?_
  · intro j hj st' N hs' ⟨hN, hNv⟩
    grow_all hg hs'
    have hrow : sums[j] ∈ sums.toArray.toList := by simp
    phg (PZ hg) as st2 z hs2 hz
    refine PH.bind' (PH.forIn_list sums[j] z _ st2
      (fun i st'' acc ↦ Rp' st'' acc ((sums[j].take i).foldl (fun a v ↦ a + VV.getD v 0) 0)) hg
      (by simpa using hz) ?_) ?_
    · intro i hi st'' acc hs'' hacc
      grow_all hg hs''
      have hv := hinv.lt _ hrow _ (List.getElem_mem hi)
      simp only [List.size_toArray] at hv
      phg (PH.add hg hacc (hV.get (i := sums[j][i]) (by omega))) as st3 a hs3 ha
      refine PH.ret hg ⟨_, rfl, ?_⟩
      rw [take_succ_getElem _ _ hi, List.foldl_append]
      exact ha
    · rintro st'' acc hs'' hacc
      rw [List.take_length, foldl_add_eq, zero_add] at hacc
      refine PH.ret hs''.good ⟨_, rfl, push_rp hN (fun w hw ↦ (hNv w hw).pgrow hg hs'') ?_⟩
      rw [uleaf_eq]
      have := hinv.sum S.toArray (by simp [hS]) j (by simpa using hj)
      simp only [List.getElem_toArray] at this
      rw [← this]
      exact hacc
  rintro st2 N hs2 ⟨hN, hNv⟩
  grow_all hg hs2
  rw [hsumsz] at hN hNv
  have hN0 := RpA.ofFn (g := fun (w : Fin Flock.kBits) ↦ (List.range Flock.kBits).foldl (fun acc i ↦
    if (Flock.towerLeaves.getD w.val 0).testBit i = true then acc + S.getD i 0 else acc) 0) hN fun w hw ↦ hNv w hw
  -- The six levels.
  rw [forIn_range_list] at hU
  refine PH.bind' (PH.forIn_rel2i _ _ (by simp [hmlen, hM]) _ _ _ _ hU st2
    (fun j st' (N : Array Sym) (u : Array E) ↦ RpA' st' N u ∧ u.size = 2 ^ (Flock.towerStages - j)) hg
    ⟨hN0, by simp [Flock.towerStages, Flock.kBits]⟩ ?_) ?_
  · intro j hj hj' st' N u hs' ⟨hNu, husz⟩
    grow_all hg hs'
    simp only [List.length_zip, List.length_range, Nat.min_self] at hj
    simp only [List.getElem_zip, List.getElem_range, List.getElem_range', Nat.zero_add, Nat.one_mul]
    have hj6 : j < Flock.towerStages := by rw [← hM, ← hmlen]; exact hj
    have hf := hm.get j hj (by omega)
    phg (PC hg (Flock.towerTheta.getD j 0)) as st3 θ hs3 hθ
    refine PH.bind' (PH.forIn_range 0 (N.size / 2) #[] _ st3
      (fun q st'' (nx : Array Sym) ↦ nx.size = q ∧ ∀ k < q, Rp' st'' (nx.getD k 0)
        (u.getD (2 * k) 0 + Flock.towerTheta.getD j 0 * u.getD (2 * k + 1) 0 +
          M.getD j 0 * (sqn (u.getD (2 * k) 0) (2 ^ j) + Flock.towerTheta.getD j 0 * sqn (u.getD (2 * k + 1) 0) (2 ^ j))))
      hg ⟨rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero k)⟩ ?_) ?_
    · intro q hq st'' nx hs'' ⟨hnx, hnxv⟩
      grow_all hg hs''
      simp only [Nat.zero_add, Nat.sub_zero] at hq ⊢
      have ha := hNu.get (i := 2 * q) (by rw [← hNu.1]; omega)
      have hb := hNu.get (i := 2 * q + 1) (by rw [← hNu.1]; omega)
      phg (PH.mul hg hθ hb) as st4 tb hs4 htb
      phg (PH.add hg ha htb) as st5 first hs5 hfirst
      phg (squarings_ph hg ha (2 ^ j) _ fun _ _ ↦ rfl) as st6 fa hs6 hfa
      phg (squarings_ph hg hb (2 ^ j) _ fun _ _ ↦ rfl) as st7 fb hs7 hfb
      phg (PH.mul hg hθ hfb) as st8 tfb hs8 htfb
      phg (PH.add hg hfa htfb) as st9 inner hs9 hinner
      phg (PH.mul hg hf hinner) as st10 second hs10 hsecond
      phg (PH.add hg hfirst hsecond) as st11 o hs11 ho
      refine PH.ret hg ⟨_, rfl, push_rp hnx hnxv ?_⟩
      rw [List.getD_eq_getElem M 0 (by omega)]
      exact ho
    · rintro st'' nx hs'' ⟨hnx, hnxv⟩
      rw [Nat.sub_zero] at hnx hnxv
      refine PH.ret hs''.good ⟨_, _, rfl, rfl, RpA.ofFn (by rw [hnx, hNu.1]) fun k hk ↦ hnxv k (by
        rw [hNu.1]; exact hk), ?_⟩
      simp only [Array.size_ofFn, husz]
      rw [show Flock.towerStages - j = (Flock.towerStages - (j + 1)) + 1 by omega, Nat.pow_succ]
      simp
  rintro st3 N hs3 ⟨hNu, husz⟩
  simp only [List.length_zip, List.length_range, Nat.min_self, hmlen, hM, Nat.sub_self, Nat.pow_zero] at husz
  exact PH.ret hs3.good (hNu.get (by omega))

end Tower

end RecGraph.Sim
