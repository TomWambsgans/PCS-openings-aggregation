-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The honest witness is `layout.rs`'s (`Builder::finish`:
-- the words in value order, a given word for a free value or a self-referential slot, the witness the words at their
-- pulls, `crates/leanvm_rec/src/circuit/layout.rs`), its given words `compile.rs`'s (the stream's and the public
-- input's bits, `units.rs`'s `bit_and_copy`; the never-hashed reads' limbs).
import RecCircuit.End

/-!
# The compiled circuit's completeness: the honest witness

For every public input `input` (32 bytes) and stream `s` of the graph's length, **`witness c input s`** satisfies the
compiled circuit (`Circuit.Satisfied`, and `RecPiop`'s copy constraints, `witness_copy`) and encodes them
(`pubW_witness`: the public input, `streamW_witness`: the stream), for every circuit the compiler accepts
(`compile r = .ok c`): generic in the graph, from the checker's completeness checks (`Check.lean`'s `completeSlots`,
`completeValues`, `completeGiven`, `completeCover`).

* `word c input s v`: value `v`'s word, by recursion on `v` (`layout.rs`'s value order): a given value's from its
  source (`givenWord`: a public-input or stream bit, a never-hashed read's limb, big-endian), a produced value's its
  producer's formula on the words its row pulls (all earlier or given, `slotOk`) plus its `κ`;
* `witness c input s q`: the word of the value position `q` pulls (`pullArr`), `0` where none.

Then every push reaches a position pulling its value (`push_witness`): a forward passes its pull on, a gate's push is
its value's word (`word`'s own equation; a free bit's slot is `b = b²`, a bit), a dead slot reads nothing pulled and is a
self-loop of `0`.
-/

namespace RecCircuit

open Primitives

namespace Compiled

variable (c : Compiled)

/-- The big-endian 64-bit word of 8 bytes of `s` from `a`. -/
def be8 (s : List UInt8) (a : ℕ) : ℕ :=
  (s.getD a 0).toNat * 2 ^ 56 + (s.getD (a + 1) 0).toNat * 2 ^ 48 + (s.getD (a + 2) 0).toNat * 2 ^ 40 +
    (s.getD (a + 3) 0).toNat * 2 ^ 32 + (s.getD (a + 4) 0).toNat * 2 ^ 24 + (s.getD (a + 5) 0).toNat * 2 ^ 16 +
    (s.getD (a + 6) 0).toNat * 2 ^ 8 + (s.getD (a + 7) 0).toNat

/-- **A given value's word**: a public-input bit, a stream bit, a never-hashed read's limb `l` (bytes
`8 (2 − l) .. 8 (3 − l)` of the read, big-endian). -/
def givenWord (input s : List UInt8) : Given → K
  | .pub k => ofBool ((input.getD (k / 8) 0).toNat.testBit (k % 8))
  | .stream k => ofBool ((s.getD (k / 8) 0).toNat.testBit (k % 8))
  | .free e l => F64.ofU64 (UInt64.ofNat (be8 s ((c.freeReads.getD e default).1 + 8 * (2 - l))))

/-- A given value's word, `0` for any other. -/
def wordOf (input s : List UInt8) (u : ℕ) : K :=
  match c.givenArr.getD u none with
  | some g => c.givenWord input s g
  | none => 0

/-- **The honest words, in value order**: a given value's from its source, a produced value's its producer's formula
on its row's pulls (earlier values' words, or given ones) plus its `κ`. -/
def word (input s : List UInt8) (v : ℕ) : K :=
  match c.givenArr.getD v none with
  | some g => c.givenWord input s g
  | none =>
    match c.circuit.formulaAt (c.ctx.prod v) with
    | .expr p => p.eval (fun cl =>
        let u := c.pullArr.getD (c.ctx.rowStart (c.ctx.prod v) + cl) NONE
        if h : u < v then word input s u else c.wordOf input s u) + c.ctx.kap (c.ctx.prod v)
    | _ => 0
termination_by v
decreasing_by exact h

/-- **The honest witness**: at each position the word of the value it pulls. -/
def witness (input s : List UInt8) (q : ℕ) : K :=
  if c.pullArr.getD q NONE = NONE then 0 else c.word input s (c.pullArr.getD q NONE)

variable {c} {input s : List UInt8}

theorem word_given {v : ℕ} {g : Given} (h : c.givenArr.getD v none = some g) :
    c.word input s v = c.givenWord input s g := by
  rw [word]; simp only [h]

theorem word_gate {v : ℕ} {p : Poly} (h : c.givenArr.getD v none = none)
    (hf : c.circuit.formulaAt (c.ctx.prod v) = .expr p) :
    c.word input s v = p.eval (fun cl =>
        let u := c.pullArr.getD (c.ctx.rowStart (c.ctx.prod v) + cl) NONE
        if u < v then c.word input s u else c.wordOf input s u) + c.ctx.kap (c.ctx.prod v) := by
  rw [word]
  simp only [h, hf]
  congr 1

theorem witness_of {q v : ℕ} (h : c.pullArr.getD q NONE = v) (hv : v ≠ NONE) :
    c.witness input s q = c.word input s v := by
  unfold witness; rw [h, if_neg hv]

theorem witness_none {q : ℕ} (h : c.pullArr.getD q NONE = NONE) : c.witness input s q = 0 := by
  unfold witness; rw [if_pos h]

theorem Poly.eval_zero' (p : Poly) : p.eval (fun _ => 0) = 0 := by
  unfold Poly.eval
  have h1 : ∀ (L : List (ℕ × K)) (a : K), L.foldl (fun acc t => acc + t.2 * (fun _ => (0 : K)) t.1) a = a := by
    intro L; induction L with
    | nil => intro a; rfl
    | cons t L ih => intro a; rw [List.foldl_cons, ih]; simp
  have h2 : ∀ (L : List (ℕ × ℕ × K)) (a : K),
      L.foldl (fun acc t => acc + t.2.2 * (fun _ => (0 : K)) t.1 * (fun _ => (0 : K)) t.2.1) a = a := by
    intro L; induction L with
    | nil => intro a; rfl
    | cons t L ih => intro a; rw [List.foldl_cons, ih]; simp
  rw [h1, h2]

theorem ofBool_sq (b : Bool) : Ctx.one * ofBool b * ofBool b = ofBool b := by
  rw [Ctx.one_eq, one_mul]; cases b <;> simp [ofBool]

/-- **Every push reaches a position pulling its value**: at a non-port position, `σ` stays inside and the pull there
is the push. -/
theorem push_witness {r : Recorded} (hc : c.Checked r) {i : ℕ} (hi : i < c.circuit.n)
    (hp : (c.circuit.formulaAt i).isPort = false) :
    c.circuit.sigmaAt i < c.circuit.n ∧ c.witness input s (c.circuit.sigmaAt i) = c.circuit.push (c.witness input s) i := by
  have hs := allBelow_spec hc.cSlots i hi
  have hk : c.ctx.kap i = c.circuit.kappaAt i := c.ctx.kap_eq rfl hi
  unfold Ctx.slotOk at hs
  have hC : c.ctx.C = c.circuit := rfl
  rw [hC] at hs
  unfold Circuit.push
  cases hf : c.circuit.formulaAt i with
  | port ls => rw [hf] at hp; cases hp
  | forward =>
    rw [hf] at hs
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨hk0, hlt⟩, hpl⟩ := hs
    refine ⟨hlt, ?_⟩
    rw [Formula.eval, ← hk, hk0, add_zero]
    unfold witness; rw [hpl]
  | expr p =>
    rw [hf] at hs
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    obtain ⟨_, hs⟩ := hs
    rw [Formula.eval, ← hk]
    by_cases hv : c.prodArr.getD i NONE = NONE
    · rw [if_pos (by simpa using hv)] at hs
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
      obtain ⟨⟨⟨hsig, hpl⟩, hk0⟩, hreads⟩ := hs
      rw [hsig, hk0, add_zero, witness_none hpl]
      refine ⟨hi, ?_⟩
      rw [Poly.eval_congr p (f := c.circuit.cells (c.witness input s) i) (g := fun _ => 0)
        (fun cl hcl => witness_none (hreads cl hcl)), Poly.eval_zero']
    · rw [if_neg (by simpa using hv)] at hs
      set v := c.prodArr.getD i NONE with hvdef
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨hprod, hlt⟩, hpl⟩, hg⟩ := hs
      refine ⟨hlt, ?_⟩
      rw [witness_of hpl hv]
      cases hG : c.givenArr.getD v none with
      | some g =>
        rw [hG] at hg
        cases g with
        | free e l => cases hg
        | pub k =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hg
          obtain ⟨⟨rfl, hk0⟩, hpi⟩ := hg
          rw [hk0, add_zero, word_given hG]
          have hcell : c.circuit.cells (c.witness input s) i (i % c.ctx.W) = c.witness input s i := by
            unfold Circuit.cells
            rw [show c.circuit.width = c.ctx.W from rfl, Nat.div_add_mod]
          simp only [Poly.eval, Ctx.sqPoly, List.foldl_nil, List.foldl_cons, zero_add, hcell, witness_of hpi hv,
            word_given hG, givenWord]
          exact (ofBool_sq _).symm
        | stream k =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hg
          obtain ⟨⟨rfl, hk0⟩, hpi⟩ := hg
          rw [hk0, add_zero, word_given hG]
          have hcell : c.circuit.cells (c.witness input s) i (i % c.ctx.W) = c.witness input s i := by
            unfold Circuit.cells
            rw [show c.circuit.width = c.ctx.W from rfl, Nat.div_add_mod]
          simp only [Poly.eval, Ctx.sqPoly, List.foldl_nil, List.foldl_cons, zero_add, hcell, witness_of hpi hv,
            word_given hG, givenWord]
          exact (ofBool_sq _).symm
      | none =>
        rw [hG] at hg
        simp only [List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hg
        have hpv : c.ctx.prod v = i := hprod
        rw [word_gate hG (by rw [hpv]; exact hf), hpv]
        refine congrArg (· + c.ctx.kap i) ?_
        apply Poly.eval_congr
        intro cl hcl
        obtain ⟨hne, hor⟩ := hg cl hcl
        unfold Circuit.cells
        rw [show c.circuit.width * (i / c.circuit.width) = c.ctx.rowStart i from rfl, witness_of rfl hne]
        dsimp only
        split
        · rfl
        · rename_i hlt'
          rcases hor with h' | h'
          · exact absurd h' hlt'
          · obtain ⟨g', hg'⟩ := Option.isSome_iff_exists.mp h'
            rw [word_given hg']
            unfold wordOf
            rw [hg']

/-- **The honest witness satisfies the circuit.** -/
theorem witness_satisfied {r : Recorded} (hc : c.Checked r) : c.circuit.Satisfied (c.witness input s) :=
  fun _ hi hp _ => (push_witness hc hi hp).2

/-- **The honest witness satisfies `RecPiop`'s copy constraints** (its words in `E`, `emb`). -/
theorem witness_copy {r : Recorded} (hc : c.Checked r) :
    ∀ i < c.circuit.toPiop.N, ¬ c.circuit.toPiop.IsHole i →
      emb (c.witness input s) (c.circuit.toPiop.sigma i) = c.circuit.toPiop.push (emb (c.witness input s)) 0 i := by
  intro i hi hh
  have hp : (c.circuit.formulaAt i).isPort = false := by
    unfold RecPiop.Circuit.IsHole at hh
    rw [toPiop_role, toRole_isPort] at hh
    simpa using hh
  rw [toPiop_push _ _ _ hp]
  exact congrArg F192.ofF64 (push_witness hc hi hp).2

/-! ## What the honest witness encodes -/

theorem completeValues_parts {r : Recorded} (hc : c.Checked r) :
    c.givenArr.size = c.view.producerF.size ∧ c.view.producerF.size < NONE ∧
      ∀ v < c.view.producerF.size, c.ctx.valueOk c.pullArr c.prodArr c.givenArr v = true := by
  have h := hc.cValues
  unfold completeValues at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, allBelow_spec h.2⟩

theorem lt_of_given {r : Recorded} (hc : c.Checked r) {u : ℕ} {g : Given} (h : c.givenArr.getD u none = some g) :
    u < c.view.producerF.size := by
  rw [← (completeValues_parts hc).1]
  by_contra hn
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h
  simp at h

/-- **Every value's word, read off the witness, is its honest word.** -/
theorem val_witness {r : Recorded} (hc : c.Checked r) {v : ℕ} (hv : v < c.view.producerF.size) :
    c.ctx.val (c.witness input s) v = c.word input s v := by
  obtain ⟨_, hN, hall⟩ := completeValues_parts hc
  have hvN : v ≠ NONE := by omega
  have h := hall v hv
  unfold Ctx.valueOk at h
  unfold Ctx.val
  by_cases hp : c.ctx.prod v = NONE
  · rw [if_pos (by simpa using hp)] at h
    rw [if_pos hp]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact witness_of h.2 hvN
  · rw [if_neg (by simpa using hp)] at h
    rw [if_neg hp]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hlt, hQ⟩, hf⟩ := h
    obtain ⟨p, hfp⟩ : ∃ p, c.circuit.formulaAt (c.ctx.prod v) = .expr p := by
      revert hf
      rw [show c.ctx.C = c.circuit from rfl]
      cases c.circuit.formulaAt (c.ctx.prod v) with
      | expr p => exact fun _ => ⟨p, rfl⟩
      | forward => simp
      | port _ => simp
    have hport : (c.circuit.formulaAt (c.ctx.prod v)).isPort = false := by rw [hfp]; rfl
    show c.circuit.push _ _ = _
    rw [← (push_witness hc hlt hport).2]
    have hs := allBelow_spec hc.cSlots _ hlt
    unfold Ctx.slotOk at hs
    rw [show c.ctx.C = c.circuit from rfl, hfp] at hs
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    obtain ⟨_, hs⟩ := hs
    rw [hQ, if_neg (by simpa using hvN)] at hs
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    exact witness_of hs.1.2 hvN

theorem bitOfWord_ofBool (b : Bool) : bitOfWord (ofBool b) = if b then 1 else 0 := by
  have : (0 : K) ≠ 1 := zero_ne_one
  cases b <;> simp [bitOfWord, ofBool, this]

/-- A byte from its eight bit words. -/
theorem byte_of_bits (v : ℕ → K) (b : UInt8) (h : ∀ t < 8, v t = ofBool (b.toNat.testBit t)) :
    ((List.range 8).foldl (fun acc j => acc + 2 ^ j * bitOfWord (v j)) 0).toUInt8 = b := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · rw [decoded_byte_testBit _ t ht, h t ht, bitOfWord_ofBool]
    cases b.toNat.testBit t <;> simp
  · rw [testBit_byte _ t (by omega), testBit_byte _ t (by omega)]

/-- **The honest witness encodes the public input.** -/
theorem pubW_witness {r : Recorded} (hc : c.Checked r) (hin : input.length = 32) :
    c.pubW (c.witness input s) = input := by
  have hps := (bitsOk_parts hc.bits).2.2
  have hg := hc.cGiven
  unfold completeGiven at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨hg1, -⟩, -⟩ := hg
  show c.decodePublic (c.ctx.val (c.witness input s)) = input
  apply List.ext_getElem?
  intro i
  unfold decodePublic
  rw [List.getElem?_map]
  by_cases hi1 : i < 32
  swap
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rfl
  have hi2 : i < input.length := by omega
  rw [List.getElem?_range hi1, Option.map_some, List.getElem?_eq_getElem hi2]
  congr 1
  refine byte_of_bits _ _ fun t ht => ?_
  have hk : 8 * i + t < c.publicSelf.size := by rw [hps]; omega
  have hG : c.givenArr.getD (c.publicSelf.getD (8 * i + t) NONE) none = some (.pub (8 * i + t)) := by
    have := allBelow_spec hg1 _ hk
    simpa using this
  rw [val_witness hc (lt_of_given hc hG), word_given hG, givenWord,
    show (8 * i + t) / 8 = i by omega, show (8 * i + t) % 8 = t by omega, List.getD_eq_getElem _ _ hi2]

theorem be8_lt (s : List UInt8) (a : ℕ) : be8 s a < 2 ^ 64 := by
  have h0 := (s.getD a 0).toNat_lt
  have h1 := (s.getD (a + 1) 0).toNat_lt
  have h2 := (s.getD (a + 2) 0).toNat_lt
  have h3 := (s.getD (a + 3) 0).toNat_lt
  have h4 := (s.getD (a + 4) 0).toNat_lt
  have h5 := (s.getD (a + 5) 0).toNat_lt
  have h6 := (s.getD (a + 6) 0).toNat_lt
  have h7 := (s.getD (a + 7) 0).toNat_lt
  unfold be8
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  omega

/-- A big-endian word's byte `m`. -/
theorem be8_byte (s : List UInt8) (a m : ℕ) (hm : m < 8) :
    be8 s a / 2 ^ (8 * (7 - m)) % 256 = (s.getD (a + m) 0).toNat := by
  have h0 := (s.getD a 0).toNat_lt
  have h1 := (s.getD (a + 1) 0).toNat_lt
  have h2 := (s.getD (a + 2) 0).toNat_lt
  have h3 := (s.getD (a + 3) 0).toNat_lt
  have h4 := (s.getD (a + 4) 0).toNat_lt
  have h5 := (s.getD (a + 5) 0).toNat_lt
  have h6 := (s.getD (a + 6) 0).toNat_lt
  have h7 := (s.getD (a + 7) 0).toNat_lt
  unfold be8
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  interval_cases m <;> norm_num <;> omega

/-- **The honest witness encodes the stream.** -/
theorem streamW_witness {r : Recorded} (hc : c.Checked r) (hs : s.length = r.graph.streamLen) :
    c.streamW r (c.witness input s) = s := by
  have hg := hc.cGiven
  unfold completeGiven at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨-, hg2⟩, hg3⟩ := hg
  have hfree := hc.free
  unfold freeReadsOk at hfree
  simp only [Bool.and_eq_true, Array.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hfree
  obtain ⟨hfr, -⟩ := hfree
  show c.decodeStream r.graph.streamLen (c.ctx.val (c.witness input s)) = s
  apply List.ext_getElem?
  intro i
  unfold decodeStream
  rw [List.getElem?_map]
  by_cases hi1 : i < r.graph.streamLen
  swap
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rfl
  have hi2 : i < s.length := by omega
  rw [List.getElem?_range hi1, Option.map_some, List.getElem?_eq_getElem hi2]
  congr 1
  have hcov := allBelow_spec hc.cCover i hi1
  simp only [Bool.or_eq_true, Array.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcov
  split
  · rename_i h0
    have hall : ∀ j < 8, (c.bitSelf.getD (8 * i + j) none).isSome := by
      rcases hcov with h | ⟨e, he, hle, hlt⟩
      · exact fun j hj => allBelow_spec h j hj
      · exfalso
        have hn := allBelow_spec (hfr e he).2 (8 * (i - (c.freeReads[e]'he).1)) (by omega)
        rw [show 8 * (c.freeReads[e]'he).1 + 8 * (i - (c.freeReads[e]'he).1) = 8 * i by omega] at hn
        simp only [Option.isNone_iff_eq_none] at hn
        rw [hn] at h0
        cases h0
    refine byte_of_bits _ _ fun t ht => ?_
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hall t ht)
    have hk : 8 * i + t < c.bitSelf.size := by rw [hc.sizes.2.2.2.1]; omega
    have hG : c.givenArr.getD v none = some (.stream (8 * i + t)) := by
      have := allBelow_spec hg2 _ hk
      rw [hv] at this
      simpa using this
    rw [show c.streamBit (8 * i + t) = v by simp [streamBit, hv], val_witness hc (lt_of_given hc hG), word_given hG,
      givenWord, show (8 * i + t) / 8 = i by omega, show (8 * i + t) % 8 = t by omega, List.getD_eq_getElem _ _ hi2]
  · rename_i h0
    have hex : ∃ e, ∃ he : e < c.freeReads.size,
        (c.freeReads[e]'he).1 ≤ i ∧ i < (c.freeReads[e]'he).1 + 24 := by
      rcases hcov with h | ⟨e, he, hle, hlt⟩
      · exact absurd (allBelow_spec h 0 (by norm_num)) (by simpa using h0)
      · exact ⟨e, he, hle, hlt⟩
    obtain ⟨x, hx⟩ : ∃ x, c.freeReads.find? (fun e => e.1 ≤ i && i < e.1 + 24) = some x := by
      apply Option.isSome_iff_exists.mp
      rw [Array.find?_isSome]
      obtain ⟨e, he, hle, hlt⟩ := hex
      exact ⟨_, Array.getElem_mem he, by simp [hle, hlt]⟩
    have hpx := Array.find?_some hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpx
    obtain ⟨e, he, hxe⟩ := Array.mem_iff_getElem.mp (Array.mem_of_find?_eq_some hx)
    rw [hx]
    obtain ⟨off, ls⟩ := x
    simp only at hpx ⊢
    set k := i - off with hkdef
    have hl : 2 - k / 8 < 3 := by omega
    have hxe' : c.freeReads.getD e default = (off, ls) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he, Option.getD_some, hxe]
    have hG : c.givenArr.getD (ls.getD (2 - k / 8) NONE) none = some (.free e (2 - k / 8)) := by
      have := allBelow_spec (allBelow_spec hg3 e he) _ hl
      rw [hxe'] at this
      simpa using this
    rw [val_witness hc (lt_of_given hc hG), word_given hG, givenWord, F64.toU64_ofU64, hxe']
    simp only
    rw [show 2 - (2 - k / 8) = k / 8 by omega, UInt64.toNat_ofNat_of_lt' (be8_lt _ _),
      be8_byte _ _ _ (Nat.mod_lt _ (by norm_num)), show off + 8 * (k / 8) + k % 8 = i by omega,
      List.getD_eq_getElem _ _ hi2]
    simp

/-! ## The zero ports, on a satisfying witness -/

/-- **A zero port carries `RecGraph`'s value of one of π1's zero checks**, on any witness satisfying the circuit
(`compile_sound_zero_rg`'s, from `Satisfied`). -/
theorem zero_port_sat {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8}
    (hc : compile (ofRG g rootsAt iv) = .ok c) {w : ℕ → K} (hw : c.circuit.Satisfied w) {J : ℕ}
    (hJ : J < c.circuit.ports.size) (hsrc : (c.circuit.ports.getD J default).source = .zero) :
    zeroOrig c (ofRG g rootsAt iv) (c.zeroIndex J) ∈ g.zero ∧
      c.circuit.portLimbs w J = limbsL (RecGraph.valE
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) (zeroOrig c (ofRG g rootsAt iv) (c.zeroIndex J))) := by
  have hchk := checked_of_compile hc
  set r := ofRG g rootsAt iv
  have hzero : c.zero = r.graph.zero.map (fun id => c.map.getD id 0) := (graphOk_parts hchk.graph).2.1
  have hso := allBelow_spec hchk.sources J hJ
  simp only [hsrc, decide_eq_true_eq] at hso
  set P := fun id => notConst (c.nodes.getD id default)
  have hP : (P ∘ fun id => c.map.getD id 0) = (fun id => notConst (c.nodes.getD (c.map.getD id 0) default)) := rfl
  have hzn : c.zeroNodes = (r.graph.zero.filter (P ∘ fun id => c.map.getD id 0)).map (fun id => c.map.getD id 0) := by
    unfold zeroNodes; rw [hzero, List.filter_map]
  rw [hP] at hzn
  have hlen : c.zeroIndex J < (r.graph.zero.filter
      (fun id => notConst (c.nodes.getD (c.map.getD id 0) default))).length := by
    rw [hzn, List.length_map] at hso; exact hso
  have hget : c.zeroNodes.getD (c.zeroIndex J) 0 = c.map.getD (zeroOrig c r (c.zeroIndex J)) 0 := by
    rw [hzn]
    simp only [zeroOrig, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen,
      Option.map_some, Option.getD_some]
  have hmemz : zeroOrig c r (c.zeroIndex J) ∈ g.zero := by
    have : zeroOrig c r (c.zeroIndex J) ∈ r.graph.zero.filter
        (fun id => notConst (c.nodes.getD (c.map.getD id 0) default)) := by
      simp only [zeroOrig, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
      exact List.getElem_mem hlen
    exact (List.mem_filter.mp this).1
  refine ⟨hmemz, ?_⟩
  rw [ports_carry hchk hw J hJ, portMeaning, hsrc]
  simp only
  have hmem := (graphOk_parts hchk.graph).2.2.1 (c.zeroNodes.getD (c.zeroIndex J) 0) (by
    apply List.mem_append_left
    simp [List.getD_eq_getElem?_getD, hso])
  rw [elem_rg hchk (expandSound hc) w hmem.1 hmem.2 (zero_lt hc _ hmemz) hget.symm]

end Compiled

end RecCircuit
