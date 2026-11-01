/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-/
import Circuit.Semantics
import Circuit.Keccak256Spec

/-!
# The Keccak gadgets compute Keccak

A state of wires *computes* a state of bits when its wire for lane `i`, bit `z` computes bit `z` of
lane `i` (`StateComputes`). θ (`spec_theta`), ρ and π (`rhoPi_computes`), χ (`spec_chiStep`) and ι
(`spec_iota`) compute their bit specifications in `KeccakBits`, loop by loop (`Spec.mapM_range`, one
gadget an index `64 i + z`); so does a round (`spec_round`) and, by induction on the round constants,
Keccak-f[1600] (`spec_keccakF`) and Keccak-256 of a 64-byte block (`spec_keccak256Block`).

The row counts: θ at most `3200` rows, χ at most `1600` (one a bit) once the state is rows, which θ
makes it when the input's lanes `0`–`3` are rows (`LowRows`), ι at most `64`; else χ at most `3200`
(`low = false`).
-/

set_option maxRecDepth 10000

namespace PcsCircuit

open LeanVM.Parameters Builder

/-! ## States and loops -/

/-- The state's wires compute the bits `S v`. -/
def StateComputes (b : Builder) (st : State) (S : (Nat → Bool) → Bits) : Prop :=
  ∀ i < 25, ∀ z < 64, Computes b (st.get i z) fun v => S v i z

/-- Every wire of the state is a row. -/
def AllRows (st : State) : Prop := ∀ i < 25, ∀ z < 64, IsRow (st.get i z)

/-- The wires of lanes `0`–`3` are rows. -/
def LowRows (st : State) : Prop := ∀ i < 4, ∀ z < 64, IsRow (st.get i z)

theorem StateComputes.of_ext {b b' : Builder} {st : State} {S : (Nat → Bool) → Bits} (h : Ext b b')
    (hs : StateComputes b st S) : StateComputes b' st S :=
  fun i hi z hz => (hs i hi z hz).of_ext h

theorem AllRows.low {st : State} (h : AllRows st) : LowRows st := fun i hi z hz => h i (by omega) z hz

/-- `mapM` over `List.range n`, the element `k` specified by `P k`. -/
theorem Spec.mapM_range {α : Type} (f : Nat → BuildM α) (n : Nat) (b : Builder) (k : Nat)
    (P : Nat → α → Builder → Prop) (hP : ∀ x, Mono (P x))
    (hf : ∀ x < n, ∀ b', Ext b b' → WF b' → Spec (f x) b' k (P x)) (hb : WF b) :
    Spec ((List.range n).mapM f) b (k * n) fun as b' =>
      as.length = n ∧ ∀ i (hi : i < as.length), P i as[i] b' := by
  have := Spec.mapM f (List.range n) b k P hP (fun x hx b' he hw => hf x (List.mem_range.mp hx) b' he hw) hb
  refine this.mono (by simp) fun as b' _ ⟨hlen, has⟩ => ⟨by simpa using hlen, fun i hi => ?_⟩
  have hi' : i < (List.range n).length := by rw [hlen] at hi; exact hi
  have := has i hi' hi
  simpa using this

theorem get_toArray {l : List Src} {i z : Nat} (h : 64 * i + z < l.length) :
    State.get l.toArray i z = l[64 * i + z] := toArray_getD_of_lt _ _ _ h

theorem div64 {i z : Nat} (hz : z < 64) : (64 * i + z) / 64 = i := by omega
theorem mod64 {i z : Nat} (hz : z < 64) : (64 * i + z) % 64 = z := by omega

/-- The results of a loop over `64 n` indices, element `k` satisfying `P (k / 64) (k % 64)`, as a
state of lanes: bit `z` of lane `i` satisfies `P i z`. -/
theorem lanes_of_mapM {l : List Src} {n : Nat} {b : Builder} {P : Nat → Nat → Src → Builder → Prop}
    (hlen : l.length = 64 * n) (h : ∀ k (hk : k < l.length), P (k / 64) (k % 64) l[k] b) :
    ∀ i < n, ∀ z < 64, P i z (State.get l.toArray i z) b := by
  intro i hi z hz
  have hk : 64 * i + z < l.length := by rw [hlen]; omega
  rw [get_toArray hk]
  have := h _ hk
  rwa [div64 hz, mod64 hz] at this

/-! ## θ -/

/-- A chain of XORs (`foldlM` of `xorG`): `init ⊕ f y₁ ⊕ f y₂ ⊕ …`, a row if `init` is. -/
theorem spec_xorChain (l : List Nat) (f : Nat → Src) (F : Nat → (Nat → Bool) → Bool) :
    ∀ (init : Src) (I : (Nat → Bool) → Bool) (b : Builder), WF b → Computes b init I →
      (∀ y ∈ l, Computes b (f y) (F y)) →
      Spec (l.foldlM (fun acc y => xorG acc (f y)) init) b l.length
        (Out (IsRow init) fun v => l.foldl (fun acc y => acc ^^ F y v) (I v)) := by
  induction l with
  | nil => intro init I b hb hi _; exact Spec.pure hb ⟨id, hi⟩
  | cons y l ih =>
    intro init I b hb hi hf
    rw [List.foldlM_cons]
    have hy := hf y (by simp)
    refine (Spec.bind (k := 1) (k' := l.length) (spec_xorG hb hi.1 hy.1) fun a b' hg ⟨hr, ha⟩ => ?_).mono
      (by simp; omega)
      fun _ _ _ h => h
    have ha' : Computes b' a fun v => I v ^^ F y v :=
      ha.congr fun v hv => by rw [hi.2 v (hv.of_ext hg.ext), hy.2 v (hv.of_ext hg.ext)]
    exact (ih a _ b' hg.wf ha' fun y' hy' => (hf y' (by simp [hy'])).of_ext hg.ext).mono (Nat.le_refl _)
      fun r b'' _ ⟨hr', hc⟩ => ⟨fun h => hr' (hr (Or.inl h)), hc⟩

/-- **θ** computes `KeccakBits.theta`, in at most `3200` rows; its result is rows when the input's
lanes `0`–`3` are. -/
theorem spec_theta {st : State} {S : (Nat → Bool) → Bits} {b : Builder} (hb : WF b)
    (hs : StateComputes b st S) :
    Spec (theta st) b 3200 fun st' b' =>
      StateComputes b' st' (fun v => KeccakBits.theta (S v)) ∧ (LowRows st → AllRows st') := by
  unfold theta
  -- the column parities
  have hc := Spec.mapM_range (fun k => [1, 2, 3, 4].foldlM
      (fun acc y => xorG acc (st.get (k / 64 + 5 * y) (k % 64))) (st.get (k / 64) (k % 64))) 320 b 4
    (fun k a b' => Out (IsRow (st.get (k / 64) (k % 64)))
      (fun v => KeccakBits.thetaC (S v) (k / 64) (k % 64)) a b') (fun _ => Out.mono _ _)
    (fun k hk b' he hw => spec_xorChain [1, 2, 3, 4] _ (fun y v => S v (k / 64 + 5 * y) (k % 64)) _ _ b' hw
      ((hs _ (by omega) _ (by omega)).of_ext he)
      (fun y hy => (hs _ (by simp at hy; omega) _ (by omega)).of_ext he)) hb
  refine (Spec.bind (k := 4 * 320) (k' := 320 + 1600) hc fun cs b1 hg1 ⟨hlen1, hcs⟩ => ?_).mono
    (by omega) fun _ _ _ h => h
  have hcs' := lanes_of_mapM (n := 5) (b := b1)
    (P := fun x z a b' => Out (IsRow (st.get x z)) (fun v => KeccakBits.thetaC (S v) x z) a b') (by omega) hcs
  -- the mixes
  have hd := Spec.mapM_range (fun k => xorG (State.get cs.toArray ((k / 64 + 4) % 5) (k % 64))
      (State.get cs.toArray ((k / 64 + 1) % 5) ((k % 64 + 63) % 64))) 320 b1 1
    (fun k a b' => Out (LowRows st) (fun v => KeccakBits.thetaD (S v) (k / 64) (k % 64)) a b')
    (fun _ => Out.mono _ _)
    (fun k hk b' he hw => by
      have h1 := hcs' ((k / 64 + 4) % 5) (by omega) (k % 64) (by omega)
      have h2 := hcs' ((k / 64 + 1) % 5) (by omega) ((k % 64 + 63) % 64) (by omega)
      refine (spec_xorG hw (h1.2.1.of_ext he) (h2.2.1.of_ext he)).mono (Nat.le_refl _)
        fun a b'' hg ⟨hr, ha⟩ => ⟨fun hl => hr ?_, ha.congr fun v hv => ?_⟩
      · by_cases hx : (k / 64 + 4) % 5 < 4
        · exact Or.inl (h1.1 (hl _ hx _ (by omega)))
        · exact Or.inr (h2.1 (hl _ (by omega) _ (by omega)))
      · have hv1 := hv.of_ext (he.trans hg.ext)
        rw [h1.2.2 v hv1, h2.2.2 v hv1]; rfl) hg1.wf
  refine Spec.bind (k := 1 * 320) (k' := 1600) hd fun ds b2 hg2 ⟨hlen2, hds⟩ => ?_
  have hds' := lanes_of_mapM (n := 5) (b := b2)
    (P := fun x z a b' => Out (LowRows st) (fun v => KeccakBits.thetaD (S v) x z) a b') (by omega) hds
  -- the lanes
  have ha := Spec.mapM_range (fun k => xorG (st.get (k / 64) (k % 64))
      (State.get ds.toArray (k / 64 % 5) (k % 64))) 1600 b2 1
    (fun k a b' => Out (LowRows st) (fun v => KeccakBits.theta (S v) (k / 64) (k % 64)) a b')
    (fun _ => Out.mono _ _)
    (fun k hk b' he hw => by
      have h0 := (hs (k / 64) (by omega) (k % 64) (by omega)).of_ext ((hg1.ext.trans hg2.ext).trans he)
      have h1 := hds' (k / 64 % 5) (by omega) (k % 64) (by omega)
      refine (spec_xorG hw h0.1 (h1.2.of_ext he).1).mono (Nat.le_refl _)
        fun a b'' hg ⟨hr, ha⟩ => ⟨fun hl => hr (Or.inr (h1.1 hl)), ha.congr fun v hv => ?_⟩
      have hv1 := hv.of_ext hg.ext
      rw [h0.2 v hv1, (h1.2.of_ext he).2 v hv1]; rfl) hg2.wf
  refine (Spec.bind (k := 1 * 1600) (k' := 0) ha fun as b3 hg3 ⟨hlen3, has⟩ => Spec.pure hg3.wf ?_).mono
    (by omega) fun _ _ _ h => h
  have has' := lanes_of_mapM (n := 25) (b := b3)
    (P := fun x z a b' => Out (LowRows st) (fun v => KeccakBits.theta (S v) x z) a b') (by omega) has
  exact ⟨fun i hi z hz => (has' i hi z hz).2, fun hl i hi z hz => (has' i hi z hz).1 hl⟩

/-! ## ρ and π -/

/-- **ρ and π** (wiring only) compute `KeccakBits.rhoPi`. -/
theorem rhoPi_computes {st : State} {S : (Nat → Bool) → Bits} {b : Builder} (hs : StateComputes b st S) :
    StateComputes b (rhoPi st) fun v => KeccakBits.rhoPi (S v) := by
  intro j hj z hz
  have hk : 64 * j + z < 1600 := by omega
  simp only [rhoPi, State.get]
  rw [map_range_getD _ _ _ _ hk, div64 hz, mod64 hz]
  exact hs _ (piInv_lt j hj) _ (mod64_lt _)

theorem rhoPi_allRows {st : State} (h : AllRows st) : AllRows (rhoPi st) := by
  intro j hj z hz
  have hk : 64 * j + z < 1600 := by omega
  simp only [rhoPi, State.get]
  rw [map_range_getD _ _ _ _ hk, div64 hz, mod64 hz]
  exact h _ (piInv_lt j hj) _ (mod64_lt _)

/-! ## χ -/

/-- **χ** computes `KeccakBits.chi`, at most `kc` rows a bit when every wire's `chiCost` is at most
`kc`; its result is rows when the input is. -/
theorem spec_chiStep {st : State} {S : (Nat → Bool) → Bits} {b : Builder} (kc : Nat) (hb : WF b)
    (hs : StateComputes b st S) (hk : ∀ i < 25, ∀ z < 64, chiCost (st.get i z) ≤ kc) :
    Spec (chiStep st) b (1600 * kc) fun st' b' =>
      StateComputes b' st' (fun v => KeccakBits.chi (S v)) ∧ (AllRows st → AllRows st') := by
  unfold chiStep
  have ha := Spec.mapM_range (fun k => chiG (st.get (k / 64) (k % 64))
      (st.get ((k / 64 % 5 + 1) % 5 + 5 * (k / 64 / 5)) (k % 64))
      (st.get ((k / 64 % 5 + 2) % 5 + 5 * (k / 64 / 5)) (k % 64))) 1600 b kc
    (fun k a b' => Out (AllRows st) (fun v => KeccakBits.chi (S v) (k / 64) (k % 64)) a b')
    (fun _ => Out.mono _ _)
    (fun k hk' b' he hw => by
      have h0 := (hs (k / 64) (by omega) (k % 64) (by omega)).of_ext he
      have h1 := (hs ((k / 64 % 5 + 1) % 5 + 5 * (k / 64 / 5)) (by omega) (k % 64) (by omega)).of_ext he
      have h2 := (hs ((k / 64 % 5 + 2) % 5 + 5 * (k / 64 / 5)) (by omega) (k % 64) (by omega)).of_ext he
      refine (spec_chiG hw h0.1 h1.1 h2.1).mono (hk _ (by omega) _ (by omega))
        fun a b'' hg ⟨hr, ha⟩ => ⟨fun hl => hr ⟨hl _ (by omega) _ (by omega), hl _ (by omega) _ (by omega),
          hl _ (by omega) _ (by omega)⟩, ha.congr fun v hv => ?_⟩
      have hv1 := hv.of_ext hg.ext
      rw [h0.2 v hv1, h1.2 v hv1, h2.2 v hv1]; rfl) hb
  refine (Spec.bind (k := kc * 1600) (k' := 0) ha fun as b1 hg1 ⟨hlen1, has⟩ => Spec.pure hg1.wf ?_).mono
    (by rw [Nat.mul_comm]; omega) fun _ _ _ h => h
  have has' := lanes_of_mapM (n := 25) (b := b1)
    (P := fun x z a b' => Out (AllRows st) (fun v => KeccakBits.chi (S v) x z) a b') (by omega) has
  exact ⟨fun i hi z hz => (has' i hi z hz).2, fun hl i hi z hz => (has' i hi z hz).1 hl⟩

/-! ## ι -/

theorem testBit_toNat64 (w : UInt64) (z : Nat) : w.toNat.testBit z = w.toBitVec.getLsbD z := by
  rw [← UInt64.toNat_toBitVec, BitVec.testBit_toNat]

/-- **ι** computes `KeccakBits.iota`, in at most `64` rows. -/
theorem spec_iota {st : State} {S : (Nat → Bool) → Bits} {b : Builder} (rc : UInt64) (hb : WF b)
    (hs : StateComputes b st S) :
    Spec (iota st rc) b 64 fun st' b' =>
      StateComputes b' st' (fun v => KeccakBits.iota rc (S v)) ∧ (AllRows st → AllRows st') := by
  unfold iota
  have ha := Spec.mapM_range (fun z => if rc.toNat.testBit z then notG (st.get 0 z) else pure (st.get 0 z))
    64 b 1 (fun z a b' => Out (IsRow (st.get 0 z)) (fun v => KeccakBits.iota rc (S v) 0 z) a b')
    (fun _ => Out.mono _ _)
    (fun z hz b' he hw => by
      have h0 := (hs 0 (by omega) z hz).of_ext he
      by_cases hr : rc.toNat.testBit z
      · simp only [hr, if_true]
        refine (spec_notG hw h0.1).mono (Nat.le_refl _) fun a b'' hg ⟨hr', ha⟩ => ⟨hr', ha.congr fun v hv => ?_⟩
        rw [h0.2 v (hv.of_ext hg.ext)]
        simp [KeccakBits.iota, ← testBit_toNat64, hr]
      · simp only [hr]
        refine Spec.pure hw ⟨id, h0.congr fun v hv => ?_⟩
        simp [KeccakBits.iota, ← testBit_toNat64, hr]) hb
  refine (Spec.bind (k := 1 * 64) (k' := 0) ha fun ls b1 hg1 ⟨hlen1, hls⟩ => Spec.pure hg1.wf ?_).mono
    (by omega) fun _ _ _ h => h
  have get_eq : ∀ i < 25, ∀ z < 64, State.get ((List.range 1600).map fun k =>
      if k < 64 then ls.toArray.getD k .zero else st.getD k .zero).toArray i z =
      if i = 0 then ls.getD z .zero else st.get i z := by
    intro i hi z hz
    simp only [State.get]
    rw [map_range_getD _ _ _ _ (by omega)]
    by_cases h0 : i = 0
    · subst h0; simp only [Nat.mul_zero, Nat.zero_add, hz, if_true]; exact toArray_getD _ _ _
    · have : ¬ 64 * i + z < 64 := by omega
      simp only [this, if_false, h0]
  refine ⟨fun i hi z hz => ?_, fun hl i hi z hz => ?_⟩
  · rw [get_eq i hi z hz]
    by_cases h0 : i = 0
    · subst h0; simp only [if_true]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact (hls z (by omega)).2
    · simp only [h0, if_false]
      exact ((hs i hi z hz).of_ext hg1.ext).congr fun v _ => by simp [KeccakBits.iota, h0]
  · rw [get_eq i hi z hz]
    by_cases h0 : i = 0
    · subst h0; simp only [if_true]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact (hls z (by omega)).1 (hl 0 (by omega) z hz)
    · simp only [h0, if_false]; exact hl i hi z hz

/-! ## A round and the permutation -/

/-- The rows χ may make a bit: one when the state is rows (`low`), else two. -/
def chiRows (low : Bool) : Nat := if low then 1 else 2

/-- The rows of a round: θ, χ, ι. -/
def roundRows (low : Bool) : Nat := 3200 + 1600 * chiRows low + 64

/-- **A round** computes `KeccakBits.round`; when `low`, the input's lanes `0`–`3` being rows, in at
most `4864` rows, and its result is rows. -/
theorem spec_round {st : State} {S : (Nat → Bool) → Bits} {b : Builder} (rc : UInt64) (low : Bool)
    (hb : WF b) (hs : StateComputes b st S) (hlow : low = true → LowRows st) :
    Spec (round st rc) b (roundRows low) fun st' b' =>
      StateComputes b' st' (fun v => KeccakBits.round (S v) rc) ∧ (low = true → AllRows st') := by
  unfold round
  refine (Spec.bind (k := 3200) (k' := 1600 * chiRows low + 64) (spec_theta hb hs)
    fun a b1 hg1 ⟨ha, har⟩ => ?_).mono (by unfold roundRows; omega) fun _ _ _ h => h
  have hrp := rhoPi_computes ha
  have hrr : low = true → AllRows (rhoPi a) := fun hl => rhoPi_allRows (har (hlow hl))
  show Spec (chiStep (rhoPi a) >>= fun a => iota a rc) b1 _ _
  generalize rhoPi a = c0 at hrp hrr ⊢
  have hk : ∀ i < 25, ∀ z < 64, chiCost (c0.get i z) ≤ chiRows low := by
    intro i hi z hz
    cases low with
    | true => rw [chiCost_row (hrr rfl i hi z hz)]; simp [chiRows]
    | false => exact chiCost_le _
  refine Spec.bind (spec_chiStep (chiRows low) hg1.wf hrp hk) fun c b2 hg2 ⟨hc, hcr⟩ => ?_
  exact (spec_iota rc hg2.wf hc).mono (Nat.le_refl _) fun d b3 _ ⟨hd, hdr⟩ =>
    ⟨hd, fun hl => hdr (hcr (hrr hl))⟩

/-- The rows of Keccak-f[1600]. -/
def keccakRows (low : Bool) : Nat := 24 * roundRows low

/-- **Keccak-f[1600]** computes `KeccakBits.keccakF`, round by round; when `low`, in at most
`24 · 4864` rows, and its result is rows. -/
theorem spec_keccakF {st : State} {S : (Nat → Bool) → Bits} {b : Builder} (low : Bool) (hb : WF b)
    (hs : StateComputes b st S) (hlow : low = true → LowRows st) :
    Spec (keccakF st) b (keccakRows low) fun st' b' =>
      StateComputes b' st' (fun v => KeccakBits.keccakF (S v)) ∧ (low = true → AllRows st') := by
  suffices ∀ (rcs : List UInt64) (st : State) (S : (Nat → Bool) → Bits) (b : Builder), WF b →
      StateComputes b st S → (low = true → LowRows st) →
      Spec (rcs.foldlM round st) b (rcs.length * roundRows low) fun st' b' =>
        StateComputes b' st' (fun v => rcs.foldl KeccakBits.round (S v)) ∧
        (low = true → (AllRows st → AllRows st') ∧ (rcs ≠ [] → AllRows st')) by
    have := this keccakRC st S b hb hs hlow
    unfold keccakF keccakRows KeccakBits.keccakF
    exact this.mono (by simp [keccakRC]) fun st' b' _ ⟨h1, h2⟩ =>
      ⟨h1, fun hl => (h2 hl).2 (by simp [keccakRC])⟩
  intro rcs
  induction rcs with
  | nil => intro st S b hb hs _; exact Spec.pure hb ⟨hs, fun _ => ⟨id, fun h => absurd rfl h⟩⟩
  | cons rc rcs ih =>
    intro st S b hb hs hlow
    rw [List.foldlM_cons]
    refine (Spec.bind (k := roundRows low) (k' := rcs.length * roundRows low) (spec_round rc low hb hs hlow)
      fun a b1 hg1 ⟨ha, har⟩ => ?_).mono (by simp [Nat.succ_mul]; omega) fun _ _ _ h => h
    exact (ih a (fun v => KeccakBits.round (S v) rc) b1 hg1.wf ha fun hl => (har hl).low).mono
      (Nat.le_refl _) fun st' b' _ ⟨h1, h2⟩ =>
        ⟨h1, fun hl => ⟨fun _ => (h2 hl).1 (har hl), fun _ => (h2 hl).1 (har hl)⟩⟩

/-! ## Keccak-256 of a block -/

/-- **Keccak-256 of a 64-byte block** (`Builder::keccak256_64`): bit `k` of its result computes bit
`k` of `KeccakBits.hash` of the message's bits; when `low`, the message's first `256` bits being
rows, in at most `24 · 4864` rows, and its result is rows. -/
theorem spec_keccak256Block {msg : Array Src} {b : Builder} (low : Bool) (hb : WF b)
    (hmsg : ∀ p < 512, Valid b (msg.getD p .zero))
    (hlow : low = true → ∀ p < 256, IsRow (msg.getD p .zero)) :
    Spec (keccak256Block msg) b (keccakRows low) fun out b' =>
      ∀ k < 256, Out (low = true) (fun v => KeccakBits.hash (fun p => read v (msg.getD p .zero)) k)
        (out.getD k .zero) b' := by
  unfold keccak256Block
  have get0 : ∀ i < 25, ∀ z < 64, State.get (((List.range 1600).map fun k =>
      if k < 512 then msg.getD k .zero else if k = 64 * 8 then Src.one
      else if k = 64 * 16 + 63 then Src.one else Src.zero).toArray) i z =
      if 64 * i + z < 512 then msg.getD (64 * i + z) .zero else if 64 * i + z = 64 * 8 then Src.one
      else if 64 * i + z = 64 * 16 + 63 then Src.one else Src.zero := by
    intro i hi z hz
    simp only [State.get]
    rw [map_range_getD _ _ _ _ (by omega)]
  have hs : StateComputes b (((List.range 1600).map fun k =>
      if k < 512 then msg.getD k .zero else if k = 64 * 8 then Src.one
      else if k = 64 * 16 + 63 then Src.one else Src.zero).toArray)
      (fun v => KeccakBits.init fun p => read v (msg.getD p .zero)) := by
    intro i hi z hz
    rw [get0 i hi z hz]
    simp only [KeccakBits.init]
    split
    · exact Computes.self (hmsg _ (by omega))
    · split
      · exact computes_one b
      · split
        · exact computes_one b
        · exact computes_zero b
  have hl : low = true → LowRows (((List.range 1600).map fun k =>
      if k < 512 then msg.getD k .zero else if k = 64 * 8 then Src.one
      else if k = 64 * 16 + 63 then Src.one else Src.zero).toArray) := by
    intro h i hi z hz
    rw [get0 i (by omega) z hz, if_pos (by omega)]
    exact hlow h _ (by omega)
  refine (Spec.bind (k := keccakRows low) (k' := 0) (spec_keccakF low hb hs hl)
    fun out b1 hg1 ⟨ho, hor⟩ => Spec.pure hg1.wf fun k hk => ?_).mono (by omega) fun _ _ _ h => h
  rw [map_range_getD _ _ _ _ hk]
  have e : out.getD k .zero = out.get (k / 64) (k % 64) := by
    simp only [State.get]; congr 1; omega
  rw [e]
  exact ⟨fun h => hor h _ (by omega) _ (mod64_lt k), ho _ (by omega) _ (mod64_lt k)⟩

end PcsCircuit
