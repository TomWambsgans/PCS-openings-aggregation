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


end Walk

end RecGraph.Sim
