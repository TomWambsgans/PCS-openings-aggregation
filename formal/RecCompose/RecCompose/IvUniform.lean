-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.RealDeployment

/-!
# `IvChecked` from the compiler's IV factorization (`STATEMENT_REVIEW_2.md`, finding 2)

`IvChecked` asks, at every 32-byte IV, three things of the compiler's output: the compile succeeds (with its
checker), the circuit passes `viewCheck`, and it decodes π1's stream as the reference IV's circuit does
(`streamAgree`). This file proves the last two at every IV from the two evaluated IVs that set every IV constant both
ways (the all-ones IV and the zero IV), given the compiler's **IV factorization**:

* **`patchCircuit C Z`**: `C` with the `κ` entries at the positions `Z` removed.
* **`seedPositions B`**: the final positions of the seed's 256 IV constants in a compiled circuit `B` (the producers of
  block 0's input bits `128..383` of the sponge whose message is `B`'s seed message at the all-ones IV), bit `j` of
  the IV at index `j` (byte `j / 8`, bit `j % 8`, as `constantBits`).
* **`zeroPos P iv`**: the positions of `iv`'s zero bits.
* **`PatchChecked`**: at every 32-byte IV, the compile succeeds and its circuit is the all-ones IV's with the `κ`
  entries at the IV's zero bits' seed positions removed (`patchCircuit`), its view, free bits and free reads the
  all-ones IV's (`patchCheck iv`, a `Bool`). This is the reviewer's factorization `compile iv = patchκ P iv (compile
  base)`, stated on what the checks read.

**Proved** (`ivChecked_of_patchChecked`): `PatchChecked`, `ivCheck` at the all-ones IV and `ivCheck` at the zero IV
give `IvChecked`. The view check transfers because `viewOf`, `callsOf` and every part of `validB` but `kappaExprB` do
not read `κ`, and `kappaExprB` holds of a sublist (`viewCheck_patch`). `streamAgree` transfers because a patched
circuit's `κ` is, at every position, the all-ones IV's or the zero IV's (`kappaAt_patch`, `zeroPos_sub`), and
`valAgree` reads `κ` at one position only (`valAgree_mix_kd`, `streamAgree_mix`).

**Not proved**: `PatchChecked` itself (the simulation of `compileM` that the factorization needs; see
`RealDeployment.lean`). It is a statement about the compiler alone (no checker, no view check), universally
quantified over the IVs like `IvChecked`.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters
open RecCircuit (NONE)

/-! ## The patch -/

/-- The all-ones IV and the zero IV: every IV constant of the seed `1`, resp. `0`. -/
def onesIv : List UInt8 := List.replicate 32 0xff
def zeroIv : List UInt8 := List.replicate 32 0

/-- The compiled circuit at the all-ones IV: the base of the patch (every seed IV constant has `κ = 1` there). -/
def onesCompiled : RecCircuit.Compiled := compiledAt onesIv

/-- **The seed's 256 IV constants' final positions** in `B`: the producers of block 0's input bits `128 + j` of the
sponge whose message is `B`'s seed message at the all-ones IV (`[]` if there is none). -/
def seedPositions (B : RecCircuit.Compiled) : List ℕ :=
  match B.st.sponges.find? (fun s ↦ decide (s.message = B.seedMessage onesIv)) with
  | some s =>
    let a0 := (B.st.keccaks.getD (s.perms.getD 0 0) default).a.getD 0 #[]
    (List.range 256).map fun j ↦ B.ctx.prod (a0.getD (128 + j) NONE)
  | none => []

/-- Bit `j` of an IV, as `constantBits` reads it. -/
def ivBit (iv : List UInt8) (j : ℕ) : Bool := (iv.getD (j / 8) 0).toNat.testBit (j % 8)

/-- The positions (of `P`, indexed by the IV's bits) of `iv`'s zero bits. -/
def zeroPos (P : List ℕ) (iv : List UInt8) : List ℕ :=
  ((List.range 256).filter fun j ↦ !ivBit iv j).map fun j ↦ P.getD j NONE

/-- **`C` with its `κ` entries at the positions `Z` removed.** -/
def patchCircuit (C : RecCircuit.Circuit) (Z : List ℕ) : RecCircuit.Circuit :=
  { C with kappa := C.kappa.filter fun e ↦ !Z.contains e.1 }

/-- Two circuits are equal, field by field. -/
def circuitEqB (C D : RecCircuit.Circuit) : Bool :=
  decide (C.logN = D.logN) && decide (C.logWidth = D.logWidth) && decide (C.regions = D.regions) &&
    decide (C.blocks = D.blocks) && decide (C.sigma = D.sigma) && decide (C.kappa = D.kappa) &&
    decide (C.ports = D.ports) && decide (C.calls = D.calls)

/-- Two views are equal, field by field. -/
def viewEqB (V W : RecCircuit.View) : Bool :=
  decide (V.rowMap = W.rowMap) && decide (V.producerF = W.producerF) && decide (V.cellF = W.cellF) &&
    decide (V.chains = W.chains) && decide (V.idxF = W.idxF)

theorem circuit_eq_of_circuitEqB {C D : RecCircuit.Circuit} (h : circuitEqB C D = true) : C = D := by
  cases C; cases D
  simp only [circuitEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

theorem view_eq_of_viewEqB {V W : RecCircuit.View} (h : viewEqB V W = true) : V = W := by
  cases V; cases W
  simp only [viewEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  subst h1 h2 h3 h4 h5
  rfl

/-- A compiled circuit is `B`'s patched at `Z` (what the checks of `ivCheck` read: the circuit, the view, the free
bits and the free reads). -/
def IvPatched (B : RecCircuit.Compiled) (Z : List ℕ) (c : RecCircuit.Compiled) : Prop :=
  c.circuit = patchCircuit B.circuit Z ∧ c.view = B.view ∧ c.bitSelf = B.bitSelf ∧ c.freeReads = B.freeReads

/-- A compiler's result is a circuit `B`'s patched at `Z`. -/
def patchOk (B : RecCircuit.Compiled) (Z : List ℕ) (e : Except String RecCircuit.Compiled) : Bool :=
  match e with
  | .ok c => circuitEqB c.circuit (patchCircuit B.circuit Z) && viewEqB c.view B.view &&
      decide (c.bitSelf = B.bitSelf) && decide (c.freeReads = B.freeReads)
  | .error _ => false

/-- **The per-IV factorization check**: the compiler accepts π1-rec3's emitted graph at `iv`, and its circuit is the
all-ones IV's with the `κ` entries at `iv`'s zero bits' seed positions removed (view, free bits, free reads equal). -/
def patchCheck (iv : List UInt8) : Bool :=
  patchOk onesCompiled (zeroPos (seedPositions onesCompiled) iv)
    (RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv))

/-- **The compiler's IV factorization at every 32-byte IV** (not proved; see the module docstring). -/
def PatchChecked : Prop := ∀ iv : List UInt8, iv.length = 32 → patchCheck iv = true

theorem patchOk_spec {B : RecCircuit.Compiled} {Z : List ℕ} {e : Except String RecCircuit.Compiled}
    (h : patchOk B Z e = true) : e = .ok (okOr e) ∧ IvPatched B Z (okOr e) := by
  cases e with
  | error m => exact absurd h Bool.false_ne_true
  | ok c =>
    change (circuitEqB c.circuit (patchCircuit B.circuit Z) && viewEqB c.view B.view &&
      decide (c.bitSelf = B.bitSelf) && decide (c.freeReads = B.freeReads)) = true at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨rfl, circuit_eq_of_circuitEqB h1, view_eq_of_viewEqB h2, h3, h4⟩

theorem patchCheck_spec {iv : List UInt8} (h : patchCheck iv = true) :
    RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) = .ok (compiledAt iv) ∧
      IvPatched onesCompiled (zeroPos (seedPositions onesCompiled) iv) (compiledAt iv) :=
  patchOk_spec h

/-! ## `κ` of a patched circuit -/

theorem foldl_filter_kappa (L : List (ℕ × K)) (keep : ℕ → Bool) (i : ℕ) (acc : K) :
    (L.filter fun e ↦ keep e.1).foldl (fun acc e ↦ if e.1 = i then e.2 else acc) acc =
      if keep i then L.foldl (fun acc e ↦ if e.1 = i then e.2 else acc) acc else acc := by
  induction L generalizing acc with
  | nil => split <;> rfl
  | cons e L ih =>
    by_cases he : keep e.1 = true
    · rw [List.filter_cons_of_pos (p := fun e : ℕ × K ↦ keep e.1) he, List.foldl_cons, List.foldl_cons, ih]
      by_cases hk : keep i = true
      · simp only [hk, ↓reduceIte]
      · have hne : e.1 ≠ i := fun h ↦ hk (h ▸ he)
        simp only [hk, hne, ↓reduceIte, Bool.false_eq_true]
    · rw [List.filter_cons_of_neg (p := fun e : ℕ × K ↦ keep e.1) he, ih, List.foldl_cons]
      by_cases hk : keep i = true
      · have hne : e.1 ≠ i := fun h ↦ he (h ▸ hk)
        simp only [hk, hne, ↓reduceIte]
      · simp only [hk, ↓reduceIte, Bool.false_eq_true]

/-- **`κ` of a patched circuit**: `0` at the patch's positions, the circuit's elsewhere. -/
theorem kappaAt_patch (C : RecCircuit.Circuit) (Z : List ℕ) (i : ℕ) :
    (patchCircuit C Z).kappaAt i = if Z.contains i then 0 else C.kappaAt i := by
  unfold patchCircuit RecCircuit.Circuit.kappaAt
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_filter,
    foldl_filter_kappa _ (fun q ↦ !Z.contains q)]
  by_cases hz : Z.contains i = true
  · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.eq_false_iff.mpr hz, Bool.not_false, Bool.false_eq_true, ↓reduceIte]

/-- Every bit of the zero IV is `0`. -/
theorem ivBit_zero (j : ℕ) : ivBit zeroIv j = false := by
  unfold ivBit zeroIv
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

/-- The zero IV's positions are all of them: they contain every IV's. -/
theorem zeroPos_sub (P : List ℕ) (iv : List UInt8) (q : ℕ) (h : (zeroPos P iv).contains q = true) :
    (zeroPos P zeroIv).contains q = true := by
  unfold zeroPos at h ⊢
  simp only [List.contains_iff_mem, List.mem_map, List.mem_filter, List.mem_range] at h ⊢
  obtain ⟨j, ⟨hj, -⟩, rfl⟩ := h
  exact ⟨j, ⟨hj, by simp [ivBit_zero]⟩, rfl⟩

/-! ## The view check transfers -/

theorem kappaExprB_patch (C : RecCircuit.Circuit) (Z : List ℕ) (h : kappaExprB C = true) :
    kappaExprB (patchCircuit C Z) = true := by
  unfold kappaExprB at h ⊢
  rw [Array.all_eq_true_iff_forall_mem] at h ⊢
  intro e he
  exact h e (Array.mem_filter.mp he).1

theorem validB_patch (C : RecCircuit.Circuit) (Z : List ℕ) (h : validB C = true) :
    validB (patchCircuit C Z) = true := by
  unfold validB at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, kappaExprB_patch C Z h7⟩, h8⟩

theorem viewOf_patch (C : RecCircuit.Circuit) (Z : List ℕ) : viewOf (patchCircuit C Z) = viewOf C := rfl

theorem callsOf_patch (C : RecCircuit.Circuit) (Z : List ℕ) : callsOf (patchCircuit C Z) = callsOf C := rfl

/-- **The view check transfers to a patched circuit.** -/
theorem viewCheck_patch {c B : RecCircuit.Compiled} {Z : List ℕ} (hc : c.circuit = patchCircuit B.circuit Z)
    (h : viewCheck B = true) : viewCheck c = true := by
  unfold viewCheck at h ⊢
  rw [hc, viewOf_patch, callsOf_patch]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, validB_patch _ Z h.2⟩

/-! ## `streamAgree` transfers -/

/-- `valAgree` reads `κ` at one position: the value's producer. -/
theorem valAgree_kd (C : RecCircuit.Circuit) (V : RecCircuit.View) (k k' : Array K) (Y : RecCircuit.Ctx) (v : ℕ)
    (hk : V.producerF.getD v NONE < C.n → k.getD (V.producerF.getD v NONE) 0 = k'.getD (V.producerF.getD v NONE) 0) :
    valAgree ⟨C, V, k⟩ Y v = valAgree ⟨C, V, k'⟩ Y v := by
  unfold valAgree
  simp only [RecCircuit.Ctx.prod, RecCircuit.Ctx.kap, RecCircuit.Ctx.n, RecCircuit.Ctx.chain]
  by_cases hq : V.producerF.getD v NONE < C.n
  · have e := hk hq
    by_cases hn : V.producerF.getD v NONE = NONE
    · simp only [hn, ↓reduceIte]
      congr
    · simp only [hn, ↓reduceIte, e]
      congr
  · by_cases hn : V.producerF.getD v NONE = NONE
    · simp only [hn, ↓reduceIte]
      congr
    · simp only [hn, ↓reduceIte, hq, decide_false, Bool.false_and, Bool.and_false]

/-- **`valAgree` of a mix**: if `κ` is, at every position, `k1`'s or `k0`'s, `valAgree` at both gives it. -/
theorem valAgree_mix_kd (C : RecCircuit.Circuit) (V : RecCircuit.View) (k k1 k0 : Array K) (Y : RecCircuit.Ctx)
    (v : ℕ) (hk : ∀ q < C.n, k.getD q 0 = k1.getD q 0 ∨ k.getD q 0 = k0.getD q 0)
    (h1 : valAgree ⟨C, V, k1⟩ Y v = true) (h0 : valAgree ⟨C, V, k0⟩ Y v = true) :
    valAgree ⟨C, V, k⟩ Y v = true := by
  by_cases hq : V.producerF.getD v NONE < C.n
  · rcases hk _ hq with e | e
    · rw [valAgree_kd C V k k1 Y v fun _ ↦ e]; exact h1
    · rw [valAgree_kd C V k k0 Y v fun _ ↦ e]; exact h0
  · rw [valAgree_kd C V k k1 Y v fun h ↦ absurd h hq]; exact h1

/-- A patched circuit's dense `κ` is, at every position, the base's or the base's patched at a larger set. -/
theorem dense_mix (C : RecCircuit.Circuit) (Z Z0 : List ℕ) (hZ : ∀ q, Z.contains q = true → Z0.contains q = true) :
    ∀ q < C.n, (RecCircuit.denseKappa (patchCircuit C Z)).getD q 0 = (RecCircuit.denseKappa C).getD q 0 ∨
      (RecCircuit.denseKappa (patchCircuit C Z)).getD q 0 = (RecCircuit.denseKappa (patchCircuit C Z0)).getD q 0 := by
  intro q hq
  rw [RecCircuit.denseKappa_getD (patchCircuit C Z) q hq, RecCircuit.denseKappa_getD C q hq,
    RecCircuit.denseKappa_getD (patchCircuit C Z0) q hq, kappaAt_patch, kappaAt_patch]
  by_cases hz : Z.contains q = true
  · right; simp only [hz, hZ q hz, ↓reduceIte]
  · left; simp only [hz, ↓reduceIte, Bool.false_eq_true]

theorem valAgree_patch (C : RecCircuit.Circuit) (V : RecCircuit.View) (Z Z0 : List ℕ)
    (hZ : ∀ q, Z.contains q = true → Z0.contains q = true) (Y : RecCircuit.Ctx) (v : ℕ)
    (h1 : valAgree ⟨C, V, RecCircuit.denseKappa C⟩ Y v = true)
    (h0 : valAgree ⟨patchCircuit C Z0, V, RecCircuit.denseKappa (patchCircuit C Z0)⟩ Y v = true) :
    valAgree ⟨patchCircuit C Z, V, RecCircuit.denseKappa (patchCircuit C Z)⟩ Y v = true := by
  have e : ∀ (Z' : List ℕ) (k : Array K), valAgree ⟨patchCircuit C Z', V, k⟩ Y v = valAgree ⟨C, V, k⟩ Y v :=
    fun _ _ ↦ rfl
  rw [e] at h0 ⊢
  exact valAgree_mix_kd C V _ _ _ Y v (dense_mix C Z Z0 hZ) h1 h0

/-- **`streamAgree` of a mix**: the same free bits and free reads, and each value read off alike if it is in both. -/
theorem streamAgree_mix (c c1 c0 R : RecCircuit.Compiled) (hb1 : c.bitSelf = c1.bitSelf)
    (hb0 : c.bitSelf = c0.bitSelf) (hf1 : c.freeReads = c1.freeReads) (hf0 : c.freeReads = c0.freeReads)
    (hval : ∀ v, valAgree c1.ctx R.ctx v = true → valAgree c0.ctx R.ctx v = true → valAgree c.ctx R.ctx v = true)
    (h1 : streamAgree c1 R = true) (h0 : streamAgree c0 R = true) : streamAgree c R = true := by
  unfold streamAgree at h1 h0 ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem] at h1 h0 ⊢
  obtain ⟨⟨⟨⟨a1, b1⟩, n1⟩, s1⟩, f1⟩ := h1
  obtain ⟨⟨⟨⟨_, _⟩, n0⟩, s0⟩, f0⟩ := h0
  refine ⟨⟨⟨⟨hb1.trans a1, hf1.trans b1⟩, hval _ n1 n0⟩, ?_⟩, ?_⟩
  · intro o ho
    have m1 := s1 o (hb1 ▸ ho)
    have m0 := s0 o (hb0 ▸ ho)
    cases o with
    | none => rfl
    | some v => exact hval v m1 m0
  · intro e he x hx
    exact hval x (f1 e (hf1 ▸ he) x hx) (f0 e (hf0 ▸ he) x hx)

/-- **`streamAgree` transfers to a patched circuit**, from the base's and the base's patched at a larger set. -/
theorem streamAgree_patch {c c0 B R : RecCircuit.Compiled} {Z Z0 : List ℕ}
    (hZ : ∀ q, Z.contains q = true → Z0.contains q = true) (hc : IvPatched B Z c) (hc0 : IvPatched B Z0 c0)
    (h1 : streamAgree B R = true) (h0 : streamAgree c0 R = true) : streamAgree c R = true := by
  obtain ⟨hcC, hcV, hcb, hcf⟩ := hc
  obtain ⟨h0C, h0V, h0b, h0f⟩ := hc0
  refine streamAgree_mix c B c0 R hcb (hcb.trans h0b.symm) hcf (hcf.trans h0f.symm) ?_ h1 h0
  intro v m1 m0
  change valAgree ⟨c.circuit, c.view, RecCircuit.denseKappa c.circuit⟩ R.ctx v = true
  change valAgree ⟨c0.circuit, c0.view, RecCircuit.denseKappa c0.circuit⟩ R.ctx v = true at m0
  change valAgree ⟨B.circuit, B.view, RecCircuit.denseKappa B.circuit⟩ R.ctx v = true at m1
  rw [h0C, h0V] at m0
  rw [hcC, hcV]
  exact valAgree_patch B.circuit B.view Z Z0 hZ R.ctx v m1 m0

/-! ## `IvChecked` -/

theorem zeroIv_length : zeroIv.length = 32 := List.length_replicate

/-- **`IvChecked` from the compiler's IV factorization and two evaluated IVs**: `PatchChecked` (the compile at every
32-byte IV is the all-ones IV's with `κ` removed at its zero bits' seed positions), `ivCheck` at the all-ones IV and
at the zero IV (both evaluated: `rec-real-check`). -/
theorem ivChecked_of_patchChecked (hp : PatchChecked) (h1 : ivCheck onesIv = true) (h0 : ivCheck zeroIv = true) :
    IvChecked := by
  intro iv hiv
  obtain ⟨hc, hP⟩ := patchCheck_spec (hp iv hiv)
  obtain ⟨-, hP0⟩ := patchCheck_spec (hp zeroIv zeroIv_length)
  obtain ⟨-, hv1, hs1⟩ := ivCheck_spec h1
  obtain ⟨-, -, hs0⟩ := ivCheck_spec h0
  change checkOk refCompiled (RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv))
    = true
  rw [hc]
  change (viewCheck (compiledAt iv) && streamAgree (compiledAt iv) refCompiled) = true
  rw [Bool.and_eq_true]
  exact ⟨viewCheck_patch hP.1 hv1,
    streamAgree_patch (zeroPos_sub _ iv) hP hP0 hs1 hs0⟩

end RecCompose

/-- info: 'RecCompose.ivChecked_of_patchChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.ivChecked_of_patchChecked
