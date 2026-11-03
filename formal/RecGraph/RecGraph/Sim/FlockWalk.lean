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

end Walk

end RecGraph.Sim
