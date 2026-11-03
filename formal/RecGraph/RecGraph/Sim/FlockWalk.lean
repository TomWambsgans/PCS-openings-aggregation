-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.FlockBase

/-!
# The BLAKE2s circuit's walk, simulated: `Pi1.blake2sRowValues` against `UniStatement.Flock.blake2sRowValues`

Both transcribe the Rust's `RowValues` line for line, so the proof goes loop for loop: `walkXor`, `walkRotr`, `slots`,
`literal`, `add`, `add3`, the linear rows, the ten rounds of eight gates, the output words. The invariant: every
entry of the arrays is a node held, worth `UniStatement`'s entry (`RpA`; the walk's state `RW`, the sixteen words
`RpS`).
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

section Defs

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **The walk's state against `UniStatement`'s**: the column weights, `left`, `right`, entry for entry. -/
def RW (st : RecState) (s : Walk) (cw L R : Array E) : Prop :=
  RpA π iv publicInput stream st s.cw cw ∧ RpA π iv publicInput stream st s.left L ∧
    RpA π iv publicInput stream st s.right R

/-- **The sixteen words against `UniStatement`'s**: each a word of 32 bits, bit for bit. -/
def RpS (st : RecState) (state : Array (Array Sym)) (U : Array Flock.WalkWord) : Prop :=
  state.size = U.size ∧ ∀ w, w < U.size → RpA π iv publicInput stream st (state.getD w #[]) (U.getD w #[]) ∧
    (U.getD w #[]).size = 32

end Defs

section Walk

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream
local notation "RW'" => RW π iv publicInput stream
local notation "RpS'" => RpS π iv publicInput stream
local notation "PZ" => PH.zero (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)
local notation "PC" => PH.const (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)

theorem RW.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {s : Walk} {cw L R : Array E}
    (h : RW' st s cw L R) : RW' st' s cw L R :=
  ⟨h.1.pgrow hg hs, h.2.1.pgrow hg hs, h.2.2.pgrow hg hs⟩

theorem RpS.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {state : Array (Array Sym)}
    {U : Array Flock.WalkWord} (h : RpS' st state U) : RpS' st' state U :=
  ⟨h.1, fun w hw ↦ ⟨(h.2 w hw).1.pgrow hg hs, (h.2 w hw).2⟩⟩

theorem getD_ofFnB {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) :
    (Array.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : i < n <;> simp [h]

theorem walkXor_ph {st : RecState} (hg : Good st) {x y : Array Sym} {X Y : Array E}
    (hx : RpA' st x X) (hy : RpA' st y Y) (hX : X.size = 32) (hY : Y.size = 32) :
    PH (Pi1.walkXor x y) st (fun st' r ↦ RpA' st' r (Flock.walkXor X Y)) := by
  unfold Pi1.walkXor
  dsimp only
  refine PH.bind' (PH.forIn_range 0 32 #[] _ st
    (fun j st' out ↦ out.size = j ∧ ∀ b < j, Rp' st' (out.getD b 0) (X.getD b 0 + Y.getD b 0)) hg
    ⟨rfl, by simp⟩ ?_) ?_
  · intro j hj st' out hs' ⟨hsz, hout⟩
    have hx' := hx.pgrow hg hs'
    have hy' := hy.pgrow hg hs'
    refine PH.bind' (PH.add hs'.good (hx'.get (by omega)) (hy'.get (by omega))) ?_
    intro st'' i hs'' hi
    refine PH.ret hs''.good ⟨_, rfl, by simp [hsz], fun b hb ↦ ?_⟩
    rw [getD_pushB]
    by_cases hb' : b < out.size
    · rw [iteT hb']; exact (hout b (by omega)).pgrow hs'.good hs''
    · rw [iteF hb', iteT (by omega)]
      have : b = j := by omega
      subst this
      simpa using hi
  · rintro st' out hs' ⟨hsz, hout⟩
    exact PH.ret hs'.good (RpA.ofFn (by simpa using hsz) fun i hi ↦ hout i (by simpa using hi))

theorem walkXor_size (X Y : Flock.WalkWord) : (Flock.walkXor X Y).size = 32 := by simp [Flock.walkXor]

theorem walkRotr_rp {st : RecState} {w : Array Sym} {W : Array E} (h : RpA' st w W) (hW : W.size = 32)
    (amount : ℕ) : RpA' st (Pi1.walkRotr w amount) (Flock.walkRotr W amount) := by
  unfold Pi1.walkRotr Flock.walkRotr
  refine RpA.ofFn (by simp) fun i hi ↦ ?_
  rw [getD_ofFnB, ditT hi]
  exact h.get (by rw [hW]; exact Nat.mod_lt _ (by norm_num))

theorem walkRotr_size (W : Flock.WalkWord) (amount : ℕ) : (Flock.walkRotr W amount).size = 32 := by
  simp [Flock.walkRotr]

theorem slots_rp {st : RecState} {s : Walk} {CW : Array E} (h : RpA' st s.cw CW) {base : ℕ}
    (hb : base + 32 ≤ CW.size) : RpA' st (s.slots base) (Flock.walkSlots CW base) := by
  unfold Pi1.Walk.slots Flock.walkSlots
  refine RpA.ofFn (by simp) fun i hi ↦ ?_
  rw [getD_ofFnB, ditT hi]
  exact h.get (by omega)

theorem walkSlots_size (CW : Array E) (base : ℕ) : (Flock.walkSlots CW base).size = 32 := by
  simp [Flock.walkSlots]

theorem literal_ph {st : RecState} (hg : Good st) {s : Walk} {CW : Array E} (h : RpA' st s.cw CW)
    (hc : Flock.constantColumn < CW.size) (value : ℕ) :
    PH (s.literal value) st (fun st' r ↦ RpA' st' r (Flock.walkLiteral CW value)) := by
  unfold Pi1.Walk.literal
  dsimp only
  refine PH.bind' (PH.forIn_range 0 32 #[] _ st
    (fun j st' out ↦ out.size = j ∧ ∀ b < j, Rp' st' (out.getD b 0)
      (if value.testBit b then CW.getD Flock.constantColumn 0 else 0)) hg ⟨rfl, by simp⟩ ?_) ?_
  · intro j hj st' out hs' ⟨hsz, hout⟩
    have hcw := (h.pgrow hg hs').get hc
    have hstep : ∀ (p : Prog Sym) (v : E), PH p st' (fun st'' i ↦ Rp' st'' i v) →
        (if value.testBit (0 + j) then CW.getD Flock.constantColumn 0 else 0) = v →
        PH (p >>= fun l ↦ pure (ForInStep.yield (out.push l))) st'
          (fun st'' r ↦ ∃ b', r = .yield b' ∧ b'.size = j + 1 ∧ ∀ b < j + 1, Rp' st'' (b'.getD b 0)
            (if value.testBit b then CW.getD Flock.constantColumn 0 else 0)) := by
      intro p v hp hv
      refine PH.bind' hp fun st'' i hs'' hi ↦ PH.ret hs''.good ⟨_, rfl, by simp [hsz], fun b hb ↦ ?_⟩
      rw [getD_pushB]
      by_cases hb' : b < out.size
      · rw [iteT hb']; exact (hout b (by omega)).pgrow hs'.good hs''
      · rw [iteF hb', iteT (by omega)]
        have : b = j := by omega
        subst this
        rw [Nat.zero_add] at hv
        rw [hv]; exact hi
    by_cases hbit : value.testBit (0 + j) = true
    · rw [iteT hbit]
      exact hstep _ _ (PH.ret hs'.good hcw) (by rw [iteT hbit])
    · rw [iteF hbit]
      exact hstep _ _ (PZ hs'.good) (by rw [iteF hbit])
  · rintro st' out hs' ⟨hsz, hout⟩
    exact PH.ret hs'.good (RpA.ofFn (by simpa using hsz) fun i hi ↦ hout i (by simpa using hi))

theorem walkLiteral_size (CW : Array E) (value : ℕ) : (Flock.walkLiteral CW value).size = 32 := by
  simp [Flock.walkLiteral]


/-- **`RowValues::add`**: the walk's state, the sum's bits. -/
theorem walkAdd_ph {st : RecState} (hg : Good st) {s : Walk} {CW L R : Array E} {x y : Array Sym}
    {X Y : Array E} (hs : RW' st s CW L R) (hx : RpA' st x X) (hy : RpA' st y Y) (hX : X.size = 32)
    (hY : Y.size = 32) {base : ℕ} (hb : base + 31 ≤ CW.size) :
    PH (s.add x y base) st (fun st' r ↦ RW' st' r.1 CW (Flock.walkAdd CW L R X Y base).1
      (Flock.walkAdd CW L R X Y base).2.1 ∧ r.1.cw = s.cw ∧ r.1.left.size = s.left.size ∧
      r.1.right.size = s.right.size ∧ RpA' st' r.2 (Flock.walkAdd CW L R X Y base).2.2 ∧
      (Flock.walkAdd CW L R X Y base).2.2.size = 32) := by
  unfold Pi1.Walk.add Flock.walkAdd
  dsimp only [Id.run]
  generalize hU : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E × Array E × E × Array E) [:32] _ _) = U
  phg (PZ hg) as st1 c hs1 hc
  phg (PZ hg) as st2 z hs2 hz
  refine PH.bind' (PH.forIn_rel_range 0 32 _ _ _ _ hU st2
    (fun st' b u ↦ RW' st' b.1 CW u.1 u.2.1 ∧ b.1.cw = s.cw ∧ b.1.left.size = s.left.size ∧
      b.1.right.size = s.right.size ∧ Rp' st' b.2.1 u.2.2.1 ∧ RpA' st' b.2.2 u.2.2.2 ∧ u.2.2.2.size = 32)
    hg ⟨hs, rfl, rfl, rfl, hc, RpA.replicate hz 32, by simp⟩ ?_) ?_
  · intro j hj st' b u hs' ⟨hw, hcw, hls, hrs, hcar, hout, hosz⟩
    grow_all hg hs'
    have hxj := hx.get (i := j) (by omega)
    have hyj := hy.get (i := j) (by omega)
    simp only [Nat.zero_add]
    by_cases hj31 : j < 31
    · simp only [hj31, ↓reduceIte]
      have hcwj := hw.1.get (i := base + j) (by omega)
      phg (PH.add hg hxj hcar) as st3 l hs3 hl
      phg (PH.add hg hyj hcar) as st4 r hs4 hr
      phg (PH.add hg hxj hyj) as st5 xy hs5 hxy
      phg (PH.add hg hxy hcar) as st6 o hs6 ho
      phg (PH.add hg hcar hcwj) as st7 c' hs7 hc'
      exact PH.ret hg ⟨_, _, rfl, rfl, ⟨hw.1, hw.2.1.set hl _, hw.2.2.set hr _⟩, hcw,
        by simp [hls], by simp [hrs], hc', hout.set ho _, by simp [hosz]⟩
    · simp only [hj31, ↓reduceIte]
      phg (PH.add hg hxj hyj) as st5 xy hs5 hxy
      phg (PH.add hg hxy hcar) as st6 o hs6 ho
      exact PH.ret hg ⟨_, _, rfl, rfl, hw, hcw, hls, hrs, hcar, hout.set ho _, by simp [hosz]⟩
  · rintro st' b hs' ⟨hw, hcw, hls, hrs, hcar, hout, hosz⟩
    exact PH.ret hs'.good ⟨hw, hcw, hls, hrs, hout, hosz⟩

/-- **`RowValues::add3`**: the walk's state, the sum's bits. -/
theorem walkAdd3_ph {st : RecState} (hg : Good st) {s : Walk} {CW L R : Array E} {x y z : Array Sym}
    {X Y Z : Array E} (hs : RW' st s CW L R) (hx : RpA' st x X) (hy : RpA' st y Y) (hz : RpA' st z Z)
    (hX : X.size = 32) (hY : Y.size = 32) (hZ : Z.size = 32) {base : ℕ} (hb : base + 61 ≤ CW.size) :
    PH (s.add3 x y z base) st (fun st' r ↦ RW' st' r.1 CW (Flock.walkAdd3 CW L R X Y Z base).1
      (Flock.walkAdd3 CW L R X Y Z base).2.1 ∧ r.1.cw = s.cw ∧ r.1.left.size = s.left.size ∧
      r.1.right.size = s.right.size ∧ RpA' st' r.2 (Flock.walkAdd3 CW L R X Y Z base).2.2 ∧
      (Flock.walkAdd3 CW L R X Y Z base).2.2.size = 32) := by
  unfold Pi1.Walk.add3 Flock.walkAdd3
  dsimp only [Id.run]
  generalize hU1 : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E × Array E × Array E) [:31] _ _) = U1
  rw [idBind]
  generalize hU2 : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E × Array E × E × Array E) [:32] _ _) = U2
  phg (PZ hg) as st1 z0 hs1 hz0
  refine PH.bind' (PH.forIn_rel_range 0 31 _ _ _ _ hU1 st1
    (fun st' b u ↦ RW' st' b.1 CW u.1 u.2.1 ∧ b.1.cw = s.cw ∧ b.1.left.size = s.left.size ∧
      b.1.right.size = s.right.size ∧ RpA' st' b.2 u.2.2 ∧ u.2.2.size = 31)
    hg ⟨hs, rfl, rfl, rfl, RpA.replicate hz0 31, by simp⟩ ?_) ?_
  · intro j hj st' b u hs' ⟨hw, hcw, hls, hrs, hmaj, hmsz⟩
    grow_all hg hs'
    have hxj := hx.get (i := j) (by omega)
    have hyj := hy.get (i := j) (by omega)
    have hzj := hz.get (i := j) (by omega)
    have hcwj := hw.1.get (i := base + j) (by omega)
    simp only [Nat.zero_add]
    phg (PH.add hg hxj hzj) as st3 l hs3 hl
    phg (PH.add hg hyj hzj) as st4 r hs4 hr
    phg (PH.add hg hcwj hzj) as st5 m hs5 hm
    exact PH.ret hg ⟨_, _, rfl, rfl, ⟨hw.1, hw.2.1.set hl _, hw.2.2.set hr _⟩, hcw,
      by simp [hls], by simp [hrs], hmaj.set hm _, by simp [hmsz]⟩
  rintro st2 b hs2 ⟨hw, hcw, hls, hrs, hmaj, hmsz⟩
  grow_all hg hs2
  phg (PZ hg) as st3 c hs3 hc
  phg (PZ hg) as st4 z1 hs4 hz1
  refine PH.bind' (PH.forIn_rel_range 0 32 _ _ _ _ hU2 st4
    (fun st' b' u ↦ RW' st' b'.1 CW u.1 u.2.1 ∧ b'.1.cw = s.cw ∧ b'.1.left.size = s.left.size ∧
      b'.1.right.size = s.right.size ∧ Rp' st' b'.2.1 u.2.2.1 ∧ RpA' st' b'.2.2 u.2.2.2 ∧ u.2.2.2.size = 32)
    hg ⟨hw, hcw, hls, hrs, hc, RpA.replicate hz1 32, by simp⟩ ?_) ?_
  · intro j hj st' b' u hs' ⟨hw', hcw', hls', hrs', hcar, hout, hosz⟩
    grow_all hg hs'
    have hxj := hx.get (i := j) (by omega)
    have hyj := hy.get (i := j) (by omega)
    have hzj := hz.get (i := j) (by omega)
    simp only [Nat.zero_add]
    have hq : ∀ (p : Prog Sym) (v : E), PH p st' (fun st'' i ↦ Rp' st'' i v) →
        (if j = 0 then 0 else U1.2.2.getD (j - 1) 0) = v →
        PH (p >>= fun q ↦ do
            let xy ← Pi1.add (x.getD j 0) (y.getD j 0)
            let xyz ← Pi1.add xy (z.getD j 0)
            let l ← Pi1.add xyz b'.2.1
            let o ← Pi1.add l q
            if 1 ≤ j ∧ j ≤ 30 then do
                let r ← Pi1.add q b'.2.1
                let carry ← Pi1.add b'.2.1 (b'.1.cw.getD (base + 31 + j - 1) 0)
                pure (ForInStep.yield
                  ({ cw := b'.1.cw, left := b'.1.left.set! (base + 31 + j - 1) l,
                      right := b'.1.right.set! (base + 31 + j - 1) r }, carry, b'.2.2.set! j o))
              else pure (ForInStep.yield (b'.1, b'.2.1, b'.2.2.set! j o))) st'
          (fun st'' r ↦ ∃ b'' u', r = .yield b'' ∧
            (if 1 ≤ j ∧ j ≤ 30 then
              pure (ForInStep.yield
                (u.1.set! (base + 31 + j - 1) (X.getD j 0 + Y.getD j 0 + Z.getD j 0 + u.2.2.1),
                  u.2.1.set! (base + 31 + j - 1) ((if j = 0 then 0 else U1.2.2.getD (j - 1) 0) + u.2.2.1),
                  u.2.2.1 + CW.getD (base + 31 + j - 1) 0,
                  u.2.2.2.set! j (X.getD j 0 + Y.getD j 0 + Z.getD j 0 + u.2.2.1 +
                    if j = 0 then 0 else U1.2.2.getD (j - 1) 0)))
            else pure (ForInStep.yield (u.1, u.2.1, u.2.2.1,
                  u.2.2.2.set! j (X.getD j 0 + Y.getD j 0 + Z.getD j 0 + u.2.2.1 +
                    if j = 0 then 0 else U1.2.2.getD (j - 1) 0))) : Id (ForInStep _)) = .yield u' ∧
            (RW' st'' b''.1 CW u'.1 u'.2.1 ∧ b''.1.cw = s.cw ∧ b''.1.left.size = s.left.size ∧
              b''.1.right.size = s.right.size ∧ Rp' st'' b''.2.1 u'.2.2.1 ∧ RpA' st'' b''.2.2 u'.2.2.2 ∧
              u'.2.2.2.size = 32)) := by
      intro p v hp hv
      rw [hv]
      phg hp as st5 q hs5 hqv
      phg (PH.add hg hxj hyj) as st6 xy hs6 hxy
      phg (PH.add hg hxy hzj) as st7 xyz hs7 hxyz
      phg (PH.add hg hxyz hcar) as st8 l hs8 hl
      phg (PH.add hg hl hqv) as st9 o hs9 ho
      by_cases hc30 : 1 ≤ j ∧ j ≤ 30
      · simp only [hc30, and_self, ↓reduceIte]
        have hcwj := hw'.1.get (i := base + 31 + j - 1) (by omega)
        phg (PH.add hg hqv hcar) as st10 r hs10 hr
        phg (PH.add hg hcar hcwj) as st11 c' hs11 hc'
        exact PH.ret hg ⟨_, _, rfl, rfl, ⟨hw'.1, hw'.2.1.set hl _, hw'.2.2.set hr _⟩, hcw',
          by simp [hls'], by simp [hrs'], hc', hout.set ho _, by simp [hosz]⟩
      · simp only [hc30, ↓reduceIte]
        exact PH.ret hg ⟨_, _, rfl, rfl, hw', hcw', hls', hrs', hcar, hout.set ho _, by simp [hosz]⟩
    refine PH.ite (fun hj0 ↦ ?_) (fun hj0 ↦ ?_)
    · exact hq _ _ (PZ hg) (iteT hj0)
    · have hm := hmaj.get (i := j - 1) (by omega)
      exact hq _ _ (PH.ret hg hm) (iteF hj0)
  · rintro st' b' hs' ⟨hw', hcw', hls', hrs', hcar, hout, hosz⟩
    exact PH.ret hs'.good ⟨hw', hcw', hls', hrs', hout, hosz⟩

/-! ### The sixteen words -/

theorem RpS.get {st : RecState} {state : Array (Array Sym)} {U : Array Flock.WalkWord} (h : RpS' st state U)
    {w : ℕ} (hw : w < U.size) : RpA' st (state.getD w #[]) (U.getD w #[]) := (h.2 w hw).1

theorem RpS.getsz {st : RecState} {state : Array (Array Sym)} {U : Array Flock.WalkWord} (h : RpS' st state U)
    {w : ℕ} (hw : w < U.size) : (U.getD w #[]).size = 32 := (h.2 w hw).2

theorem RpS.set {st : RecState} {state : Array (Array Sym)} {U : Array Flock.WalkWord} (h : RpS' st state U)
    {a : Array Sym} {A : Flock.WalkWord} (ha : RpA' st a A) (hA : A.size = 32) (i : ℕ) :
    RpS' st (state.set! i a) (U.set! i A) := by
  refine ⟨by simp [h.1], fun w hw ↦ ?_⟩
  rw [size_setB] at hw
  rw [getD_setB, getD_setB, ← h.1]
  by_cases hj : i = w ∧ w < state.size
  · rw [iteT hj, iteT hj]; exact ⟨ha, hA⟩
  · rw [iteF hj, iteF hj]; exact h.2 w hw

theorem RpS.replicate {st : RecState} {z : Sym} (hz : Rp' st z 0) :
    RpS' st (Array.replicate 16 (Array.replicate 32 z)) (Array.replicate 16 (Array.replicate 32 0)) := by
  refine ⟨by simp, fun w hw ↦ ?_⟩
  simp only [Array.size_replicate] at hw
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hw, ↓reduceIte, Option.getD_some]
  exact ⟨RpA.replicate hz 32, by simp⟩

/-! ### The circuit's constants -/

theorem lin_bound : ∀ p ∈ ([(0, 256), (640, 512), (1152, 128)] : List (ℕ × ℕ)), p.1 + p.2 ≤ 1280 := by decide

theorem ctr_bound : ∀ p ∈ ([1152, 1184, 1216, 1248].zip (List.range 4)), p.1 + 32 ≤ 1280 ∧ p.2 < 4 := by decide

theorem sigma_bound : ∀ p ∈ Flock.blake2sSigma.zip (List.range Flock.blake2sSigma.length),
    (∀ i < 16, p.1.getD i 0 < 16) ∧ p.2 < 10 := by decide

theorem lanes_bound : ∀ p ∈ Flock.blake2sGLanes.zip (List.range Flock.blake2sGLanes.length),
    (∀ i < 4, p.1.getD i 0 < 16) ∧ p.2 < 8 := by decide

/-- **`blake2s_row_values(column_weights)`**: `A0 w` and `B0 w` by one forward walk of the circuit, entry for entry
`UniStatement`'s. -/
theorem blake2sRowValues_ph {st : RecState} (hg : Good st) {cw : Array Sym} {CW : Array E}
    (hcw : RpA' st cw CW) (hsz : CW.size = 2 ^ blake2sR1csLogSize) :
    PH (Pi1.blake2sRowValues cw) st (fun st' r ↦ RpA' st' r.1 (Flock.blake2sRowValues CW).1 ∧
      RpA' st' r.2 (Flock.blake2sRowValues CW).2 ∧ r.1.size = 2 ^ blake2sR1csLogSize ∧
      r.2.size = 2 ^ blake2sR1csLogSize) := by
  have hN : (2 : ℕ) ^ blake2sR1csLogSize = 16384 := by simp [blake2sR1csLogSize]
  have hsz' : CW.size = 16384 := by rw [hsz, hN]
  have hconst : Flock.constantColumn < CW.size := by rw [hsz']; simp [Flock.constantColumn]
  generalize hW : Flock.blake2sRowValues CW = W
  unfold Pi1.blake2sRowValues
  dsimp only
  subst hW
  unfold Flock.blake2sRowValues
  dsimp (config := { iota := false, proj := false }) only [Id.run]
  generalize hU1 : (forIn (m := Id) (ρ := List (ℕ × ℕ)) (β := Array E × Array E) _ _ _) = U1
  generalize hU2 : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array Flock.WalkWord) _ _ _) = U2
  rw [idBind, idBind]
  generalize hU3 : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array Flock.WalkWord) _ _ _) = U3
  rw [idBind]
  generalize hU4 : (forIn (m := Id) (ρ := List (ℕ × ℕ)) (β := Array Flock.WalkWord) _ _ _) = U4
  rw [idBind]
  generalize hU5 : (forIn (m := Id) (ρ := List (List ℕ × ℕ)) (β := Array E × Array E × Array Flock.WalkWord) _ _ _) = U5
  rw [idBind]
  generalize hU6 : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E × Array E) _ _ _) = U6
  rw [idBind]
  -- The linear rows.
  phg (PZ hg) as st1 z1 hs1 hz1
  phg (PZ hg) as st2 z2 hs2 hz2
  refine PH.bind' (PH.forIn_rel _ _ _ _ _ hU1 st2
    (fun st' (b : Walk) (u : Array E × Array E) ↦ RW' st' b CW u.1 u.2 ∧ b.cw = cw ∧
      b.left.size = 2 ^ blake2sR1csLogSize ∧ b.right.size = 2 ^ blake2sR1csLogSize) hg
    ⟨⟨hcw, RpA.replicate hz1 _, RpA.replicate hz2 _⟩, rfl, by simp, by simp⟩ ?_) ?_
  · intro j hj st' b u hs' ⟨hw, hbc, hbl, hbr⟩
    grow_all hg hs'
    have hmem := List.getElem_mem hj
    generalize hx : ([(0, 256), (640, 512), (1152, 128)] : List (ℕ × ℕ))[j] = x at hmem ⊢
    obtain ⟨base, length⟩ := x
    have hbd := lin_bound _ hmem
    dsimp only at hbd ⊢
    generalize hV : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E × Array E) _ _ _) = V
    rw [idBind]
    refine PH.bind' (PH.forIn_rel_range base (base + length) _ _ _ _ hV st'
      (fun st'' (b' : Walk) (v : Array E × Array E) ↦ RW' st'' b' CW v.1 v.2 ∧ b'.cw = cw ∧
        b'.left.size = 2 ^ blake2sR1csLogSize ∧ b'.right.size = 2 ^ blake2sR1csLogSize) hg
      ⟨hw, hbc, hbl, hbr⟩ ?_) ?_
    · intro i hi st'' b' v hs'' ⟨hw', hbc', hbl', hbr'⟩
      grow_all hg hs''
      have h1 := hcw.get (i := base + i) (by omega)
      have h2 := hcw.get hconst
      exact PH.ret hg ⟨_, _, rfl, rfl, ⟨hw'.1, hw'.2.1.set h1 _, hw'.2.2.set h2 _⟩, hbc',
        by simp [hbl'], by simp [hbr']⟩
    · rintro st'' b' hs'' hR
      exact PH.ret hs''.good ⟨_, _, rfl, rfl, hR⟩
  rintro st3 w1 hs3 ⟨hw1, hw1c, hw1l, hw1r⟩
  grow_all hg hs3
  -- The chaining value's words.
  phg (PZ hg) as st4 z3 hs4 hz3
  refine PH.bind' (PH.forIn_rel_range 0 8 _ _ _ _ hU2 st4
    (fun st' (b : Array (Array Sym)) (u : Array Flock.WalkWord) ↦ RpS' st' b u ∧ u.size = 16) hg
    ⟨RpS.replicate hz3, by simp⟩ ?_) ?_
  · intro j hj st' b u hs' ⟨hS, hS16⟩
    grow_all hg hs'
    exact PH.ret hg ⟨_, _, rfl, rfl, hS.set (slots_rp hw1.1 (by omega)) (walkSlots_size _ _) _, by simp [hS16]⟩
  rintro st5 s1 hs5 ⟨hS1, hS1z⟩
  grow_all hg hs5
  -- The IV's words.
  refine PH.bind' (PH.forIn_rel_range 0 4 _ _ _ _ hU3 st5
    (fun st' (b : Array (Array Sym)) (u : Array Flock.WalkWord) ↦ RpS' st' b u ∧ u.size = 16) hg
    ⟨hS1, hS1z⟩ ?_) ?_
  · intro j hj st' b u hs' ⟨hS, hS16⟩
    grow_all hg hs'
    phg (literal_ph hg hw1.1 hconst _) as st6 l hs6 hl
    exact PH.ret hg ⟨_, _, rfl, rfl, hS.set hl (walkLiteral_size _ _) _, by simp [hS16]⟩
  rintro st7 s2 hs7 ⟨hS2, hS2z⟩
  grow_all hg hs7
  -- The counters' and flags' words.
  refine PH.bind' (PH.forIn_rel _ _ _ _ _ hU4 st7
    (fun st' (b : Array (Array Sym)) (u : Array Flock.WalkWord) ↦ RpS' st' b u ∧ u.size = 16) hg
    ⟨hS2, hS2z⟩ ?_) ?_
  · intro j hj st' b u hs' ⟨hS, hS16⟩
    grow_all hg hs'
    have hmem := List.getElem_mem hj
    generalize hx : ([1152, 1184, 1216, 1248].zip (List.range 4))[j] = x at hmem ⊢
    obtain ⟨base, word⟩ := x
    have hbd := ctr_bound _ hmem
    dsimp only at hbd ⊢
    phg (literal_ph hg hw1.1 hconst _) as st6 l hs6 hl
    phg (walkXor_ph hg hl (slots_rp hw1.1 (base := base) (by omega)) (walkLiteral_size _ _)
      (walkSlots_size _ _)) as st8 xr hs8 hxr
    exact PH.ret hg ⟨_, _, rfl, rfl, hS.set hxr (walkXor_size _ _) _, by simp [hS16]⟩
  rintro st9 s3 hs9 ⟨hS3, hS3z⟩
  grow_all hg hs9
  -- The ten rounds.
  refine PH.bind' (PH.forIn_rel _ _ _ _ _ hU5 st9
    (fun st' (b : Walk × Array (Array Sym)) (u : Array E × Array E × Array Flock.WalkWord) ↦
      RW' st' b.1 CW u.1 u.2.1 ∧ b.1.cw = cw ∧ b.1.left.size = 2 ^ blake2sR1csLogSize ∧
        b.1.right.size = 2 ^ blake2sR1csLogSize ∧ RpS' st' b.2 u.2.2 ∧ u.2.2.size = 16) hg
    ⟨hw1, hw1c, hw1l, hw1r, hS3, hS3z⟩ ?_) ?_
  · intro j hj st' b u hs' hR
    grow_all hg hs'
    have hmem := List.getElem_mem hj
    split
    rename_i sigma roundIndex heq
    rw [heq] at hmem
    rw [heq]
    obtain ⟨hsig, hri⟩ := sigma_bound _ hmem
    dsimp (config := { iota := false }) only at hsig hri ⊢
    generalize hV : (forIn (m := Id) (ρ := List (List ℕ × ℕ)) (β := Array E × Array E × Array Flock.WalkWord) _ _ _) = V
    rw [idBind]
    refine PH.bind' (PH.forIn_rel _ _ _ _ _ hV st'
      (fun st'' (b' : Walk × Array (Array Sym)) (v : Array E × Array E × Array Flock.WalkWord) ↦
        RW' st'' b'.1 CW v.1 v.2.1 ∧ b'.1.cw = cw ∧ b'.1.left.size = 2 ^ blake2sR1csLogSize ∧
          b'.1.right.size = 2 ^ blake2sR1csLogSize ∧ RpS' st'' b'.2 v.2.2 ∧ v.2.2.size = 16) hg hR ?_) ?_
    · -- One gate.
      intro i hi st'' b' v hs'' ⟨hw, hbc, hbl, hbr, hS, hS16⟩
      grow_all hg hs''
      have hmem' := List.getElem_mem hi
      split
      rename_i lanes gateIndex heq'
      rw [heq'] at hmem'
      rw [heq']
      obtain ⟨hlan, hgi⟩ := lanes_bound _ hmem'
      dsimp (config := { iota := false }) only at hlan hgi ⊢
      have hla := hlan 0 (by norm_num)
      have hlb := hlan 1 (by norm_num)
      have hlc := hlan 2 (by norm_num)
      have hld := hlan 3 (by norm_num)
      have hs0 := hsig (2 * gateIndex) (by omega)
      have hs1' := hsig (2 * gateIndex + 1) (by omega)
      have hgate : roundIndex * 8 + gateIndex < 80 := by omega
      split
      rename_i l1 r1 a1 hA1
      split
      rename_i l2 r2 c1 hA2
      split
      rename_i l3 r3 a2 hA3
      split
      rename_i l4 r4 c2 hA4
      have hwa := hS.get (w := lanes.getD 0 0) (by omega)
      have hwb := hS.get (w := lanes.getD 1 0) (by omega)
      have hwc := hS.get (w := lanes.getD 2 0) (by omega)
      have hwd := hS.get (w := lanes.getD 3 0) (by omega)
      have hza := hS.getsz (w := lanes.getD 0 0) (by omega)
      have hzb := hS.getsz (w := lanes.getD 1 0) (by omega)
      have hzc := hS.getsz (w := lanes.getD 2 0) (by omega)
      have hzd := hS.getsz (w := lanes.getD 3 0) (by omega)
      have hmx := slots_rp hw.1 (base := 640 + 32 * sigma.getD (2 * gateIndex) 0) (by omega)
      have hmy := slots_rp hw.1 (base := 640 + 32 * sigma.getD (2 * gateIndex + 1) 0) (by omega)
      phg (walkAdd3_ph hg hw hwa hwb hmx hza hzb (walkSlots_size _ _)
        (base := 1280 + 184 * (roundIndex * 8 + gateIndex)) (by omega)) as st3 x1 hs3 hx1
      rw [hA1] at hx1
      obtain ⟨hw1', hc1, hl1, hr1, ha1, ha1s⟩ := hx1
      phg (walkXor_ph hg hwd ha1 hzd ha1s) as st4 d1x hs4 hd1x
      have hd1 := walkRotr_rp hd1x (walkXor_size _ _) 16
      phg (walkAdd_ph hg hw1' hwc hd1 hzc (walkRotr_size _ _)
        (base := 1280 + 184 * (roundIndex * 8 + gateIndex) + 61) (by omega)) as st5 x2 hs5 hx2
      rw [hA2] at hx2
      obtain ⟨hw2, hc2, hl2, hr2, hc1v, hc1s⟩ := hx2
      phg (walkXor_ph hg hwb hc1v hzb hc1s) as st6 b1x hs6 hb1x
      have hb1 := walkRotr_rp hb1x (walkXor_size _ _) 12
      phg (walkAdd3_ph hg hw2 ha1 hb1 hmy ha1s (walkRotr_size _ _) (walkSlots_size _ _)
        (base := 1280 + 184 * (roundIndex * 8 + gateIndex) + 92) (by omega)) as st7 x3 hs7 hx3
      rw [hA3] at hx3
      obtain ⟨hw3, hc3, hl3, hr3, ha2, ha2s⟩ := hx3
      phg (walkXor_ph hg hd1 ha2 (walkRotr_size _ _) ha2s) as st8 d2x hs8 hd2x
      have hd2 := walkRotr_rp hd2x (walkXor_size _ _) 8
      phg (walkAdd_ph hg hw3 hc1v hd2 hc1s (walkRotr_size _ _)
        (base := 1280 + 184 * (roundIndex * 8 + gateIndex) + 153) (by omega)) as st9 x4 hs9 hx4
      rw [hA4] at hx4
      obtain ⟨hw4, hc4, hl4, hr4, hc2v, hc2s⟩ := hx4
      phg (walkXor_ph hg hb1 hc2v (walkRotr_size _ _) hc2s) as st10 b2x hs10 hb2x
      have hb2 := walkRotr_rp hb2x (walkXor_size _ _) 7
      exact PH.ret hg ⟨_, _, rfl, rfl, hw4, by rw [hc4, hc3, hc2, hc1, hbc],
        by rw [hl4, hl3, hl2, hl1, hbl], by rw [hr4, hr3, hr2, hr1, hbr],
        ((((hS.set ha2 ha2s _).set hb2 (walkRotr_size _ _) _).set hc2v hc2s _).set hd2 (walkRotr_size _ _) _),
        by simp [hS16]⟩
    · rintro st'' b' hs'' hR'
      exact PH.ret hs''.good ⟨_, _, rfl, rfl, hR'⟩
  rintro st10 b5 hs10 ⟨hw5, hw5c, hw5l, hw5r, hS5, hS5z⟩
  grow_all hg hs10
  -- The output's words.
  refine PH.bind' (PH.forIn_rel_range 0 8 _ _ _ _ hU6 st10
    (fun st' (b : Walk) (u : Array E × Array E) ↦ RW' st' b CW u.1 u.2 ∧ b.cw = cw ∧
      b.left.size = 2 ^ blake2sR1csLogSize ∧ b.right.size = 2 ^ blake2sR1csLogSize) hg
    ⟨hw5, hw5c, hw5l, hw5r⟩ ?_) ?_
  · intro j hj st' b u hs' ⟨hw, hbc, hbl, hbr⟩
    grow_all hg hs'
    have hwa := hS5.get (w := j) (by omega)
    have hwb := hS5.get (w := j + 8) (by omega)
    have hza := hS5.getsz (w := j) (by omega)
    have hzb := hS5.getsz (w := j + 8) (by omega)
    simp only [Nat.zero_add]
    phg (walkXor_ph hg hwa hwb hza hzb) as st11 x1 hs11 hx1
    phg (walkXor_ph hg hx1 (slots_rp hw.1 (base := 32 * j) (by omega)) (walkXor_size _ _)
      (walkSlots_size _ _)) as st12 out hs12 hout
    generalize hV : (forIn (m := Id) (ρ := Std.Legacy.Range) (β := Array E × Array E) _ _ _) = V
    rw [idBind]
    refine PH.bind' (PH.forIn_rel_range 0 32 _ _ _ _ hV st12
      (fun st'' (b' : Walk) (v : Array E × Array E) ↦ RW' st'' b' CW v.1 v.2 ∧ b'.cw = cw ∧
        b'.left.size = 2 ^ blake2sR1csLogSize ∧ b'.right.size = 2 ^ blake2sR1csLogSize) hg
      ⟨hw, hbc, hbl, hbr⟩ ?_) ?_
    · intro i hi st'' b' v hs'' ⟨hw', hbc', hbl', hbr'⟩
      grow_all hg hs''
      have h1 := hout.get (i := i) (by rw [walkXor_size]; omega)
      have h2 := hcw.get hconst
      simp only [Nat.zero_add]
      exact PH.ret hg ⟨_, _, rfl, rfl, ⟨hw'.1, hw'.2.1.set h1 _, hw'.2.2.set h2 _⟩, hbc',
        by simp [hbl'], by simp [hbr']⟩
    · rintro st'' b' hs'' hR
      exact PH.ret hs''.good ⟨_, _, rfl, rfl, hR⟩
  rintro st13 w6 hs13 ⟨hw6, hw6c, hw6l, hw6r⟩
  grow_all hg hs13
  have h2 := hcw.get hconst
  exact PH.ret hg ⟨hw6.2.1.set h2 _, hw6.2.2.set h2 _, by simp [hw6l], by simp [hw6r]⟩

end Walk

end RecGraph.Sim
