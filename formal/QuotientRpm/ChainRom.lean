-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientRpm.Uniform
import QuotientSecurity.Joint

/-!
# Knowledge soundness with the Keccak-256 chain, in the random-oracle model

The hash `H : bytes → 32 bytes` is a random oracle; the adversary and the verifier ask it, the
verifier through the chain (`chainExperiment`). **As a function of the transcript, the chain's
challenges are a random oracle on transcripts unless a collision or a prefix event happens**, and
this file proves the soundness bound that statement gives, query by query.

A fresh query `x`, asked after the inputs `H`, is *bad* (`chainBad`) when

* `Coll`: its answer repeats an earlier answer, or is the 32-byte head of an input asked before
  (or of `x`), or its root words sit where an input after a root holds them: the events that
  would let an input be read as a chain step it is not, or a state be used before it exists;
* `FirstBad`: `x` is the input after the first root of a statement and a first message whose
  label and root were asked before, and the triple it leads to (its answer, the hash of that, the
  hash of that, none asked before) makes the first round's state go from lost to won;
* `SecondBad`, `ThirdBad`: likewise for the input after the second root, and after the values,
  the chain before them asked before.

The parse of `x` is unique given the history when the history has no collision (`Set.InjOn`), so
each is bad with probability at most the round's error (`RoundByRound.lean`, the low 192 bits of
a uniform state being uniform): `prob_chainBad`, at most `roundError + (3 |H| + 2) / 2^256`. An
accepted proof whose cells fail the relation makes a fresh query bad (`trace_chainBad`): the
chain's inputs come in their order unless `Coll` (`before`), and `bad_of_accepts` of the existing
proof names the round. `prEvent_randomOracle_le_of_freshBad` adds it up:

**`knowledgeSoundness_chain`**: an adversary of at most `Q` queries wins with probability at
most `(Q + 8) (roundError + 3 (Q + 8) / 2^256)`, the verifier's eight hashes counted.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace QuotientRpm

open QuotientSecurity QuotientSecurity.Params

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B)

/-- A table of the hash. -/
abbrev Table := List UInt8 → Bytes32

/-- The inputs asked before. -/
abbrev Hist := Finset (List UInt8)

/-- `d` was asked before, and the table answers `v` there. -/
def Has (H : Hist) (T : Table) (d : List UInt8) (v : Bytes32) : Prop := d ∈ H ∧ T d = v

/-! ## The bad events -/

/-- **A collision**: the fresh answer at `x` repeats an earlier answer, or is the 32-byte head of
an input asked before or of `x`, or its root words are bytes `32..96` of one. -/
def Coll (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  (∃ y ∈ H, T y = T x) ∨
    ∃ y ∈ insert x H, (T x).toList = y.take 32 ∨ rootWords (T x) = (y.drop 32).take 64

/-- `x` is the input after the first root, for the statement `sb` and the first message `gm`:
their label and root were asked before, without collision. -/
def ParseFirst (H : Hist) (x : List UInt8) (T : Table) (sb : Vector UInt8 64) (gm : B.Msg₁) :
    Prop :=
  ∃ st₀ r₁, Has H T (W.label sb) st₀ ∧ Has H T (W.enc₁ gm) r₁ ∧ x = Wire.afterRoot st₀ r₁ ∧
    Set.InjOn T ↑H

open Classical in
/-- The triple the input after the first root leads to, its three states not asked before, makes
the first round's state go from lost to won. -/
def FreshFirst (H : Hist) (x : List UInt8) (T : Table) (sb : Vector UInt8 64) (gm : B.Msg₁) :
    Prop :=
  (T x).toList ∉ H ∧ (T (T x).toList).toList ∉ H ∧ (T (T x).toList).toList ≠ (T x).toList ∧
    ¬ State₁ (W.decode sb) gm ∧
    State₂ (W.decode sb) gm (W.chal (T x), W.chal (T (T x).toList), W.chal (T (T (T x).toList).toList))

/-- `x` is the input after the second root: the chain before it was asked, without collision,
and gave the first challenges `c`. -/
def ParseSecond (H : Hist) (x : List UInt8) (T : Table) (sb : Vector UInt8 64) (gm : B.Msg₁)
    (R : B.Msg₂) (c : F × F × F) : Prop :=
  ∃ st₀ r₁ st₁ st₂ st₃ r₂, Has H T (W.label sb) st₀ ∧ Has H T (W.enc₁ gm) r₁ ∧
    Has H T (Wire.afterRoot st₀ r₁) st₁ ∧ Has H T st₁.toList st₂ ∧ Has H T st₂.toList st₃ ∧
    Has H T (W.enc₂ R) r₂ ∧ x = Wire.afterRoot st₃ r₂ ∧
    c = (W.chal st₁, W.chal st₂, W.chal st₃) ∧ Set.InjOn T ↑H

/-- `x` is the input after the five values: the chain before it was asked, without collision,
and gave the challenges `c` and `t`. -/
def ParseThird (H : Hist) (x : List UInt8) (T : Table) (sb : Vector UInt8 64) (gm : B.Msg₁)
    (R : B.Msg₂) (c : F × F × F) (t : F) (v : (Fin 4 → F) × F) : Prop :=
  ∃ st₀ r₁ st₁ st₂ st₃ r₂ st₄, Has H T (W.label sb) st₀ ∧ Has H T (W.enc₁ gm) r₁ ∧
    Has H T (Wire.afterRoot st₀ r₁) st₁ ∧ Has H T st₁.toList st₂ ∧ Has H T st₂.toList st₃ ∧
    Has H T (W.enc₂ R) r₂ ∧ Has H T (Wire.afterRoot st₃ r₂) st₄ ∧ x = W.afterValues st₄ v ∧
    c = (W.chal st₁, W.chal st₂, W.chal st₃) ∧ t = W.chal st₄ ∧ Set.InjOn T ↑H

/-- The first round. -/
def FirstBad (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ sb gm, ParseFirst W H x T sb gm ∧ FreshFirst W H x T sb gm

open Classical in
/-- The second round: the answer's challenge makes the state go from lost to won. -/
def SecondBad (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ sb gm R c, ParseSecond W H x T sb gm R c ∧
    ¬ State₃ (W.decode sb) gm c R ∧ State₄ (W.decode sb) gm c R (W.chal (T x))

open Classical in
/-- The third round. -/
def ThirdBad (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ sb gm R c t v, ParseThird W H x T sb gm R c t v ∧
    ¬ State₄ (W.decode sb) gm c R t ∧ State₆ (W.decode sb) gm c R t v (W.chal (T x))

/-- **A bad fresh query.** -/
def chainBad (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  Coll H x T ∨ FirstBad W H x T ∨ SecondBad W H x T ∨ ThirdBad W H x T

/-! ## The parse is unique, and reads only the history -/

section Parse

variable {W}

theorem has_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (d : List UInt8)
    (v : Bytes32) : Has H T d v ↔ Has H T' d v :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, (h d h1) ▸ h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (h d h1).symm ▸ h2⟩⟩

theorem injOn_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) :
    Set.InjOn T ↑H ↔ Set.InjOn T' ↑H :=
  ⟨fun hi => hi.congr fun d hd => h d hd, fun hi => hi.congr fun d hd => (h d hd).symm⟩

theorem parseFirst_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x sb gm) :
    ParseFirst W H x T sb gm ↔ ParseFirst W H x T' sb gm := by
  simp only [ParseFirst, has_congr h, injOn_congr h]

theorem parseSecond_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x sb gm R c) :
    ParseSecond W H x T sb gm R c ↔ ParseSecond W H x T' sb gm R c := by
  simp only [ParseSecond, has_congr h, injOn_congr h]

theorem parseThird_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x sb gm R c t v) :
    ParseThird W H x T sb gm R c t v ↔ ParseThird W H x T' sb gm R c t v := by
  simp only [ParseThird, has_congr h, injOn_congr h]

theorem has_inj {H : Hist} {T : Table} (hi : Set.InjOn T ↑H) {d d' : List UInt8} {v : Bytes32}
    (h : Has H T d v) (h' : Has H T d' v) : d = d' :=
  hi h.1 h'.1 (h.2.trans h'.2.symm)

theorem parseFirst_unique {H : Hist} {x : List UInt8} {T : Table} {sb sb' gm gm'}
    (h : ParseFirst W H x T sb gm) (h' : ParseFirst W H x T sb' gm') : sb = sb' ∧ gm = gm' := by
  obtain ⟨st₀, r₁, h0, h1, hx, hi⟩ := h
  obtain ⟨st₀', r₁', h0', h1', hx', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (hx.symm.trans hx')
  exact ⟨W.label_injective (has_inj hi h0 h0'), W.enc₁_injective (has_inj hi h1 h1')⟩

theorem parseSecond_unique {H : Hist} {x : List UInt8} {T : Table} {sb sb' gm gm' R R' c c'}
    (h : ParseSecond W H x T sb gm R c) (h' : ParseSecond W H x T sb' gm' R' c') :
    sb = sb' ∧ gm = gm' ∧ R = R' ∧ c = c' := by
  obtain ⟨st₀, r₁, st₁, st₂, st₃, r₂, h0, h1, h2, h3, h4, h5, hx, hc, hi⟩ := h
  obtain ⟨st₀', r₁', st₁', st₂', st₃', r₂', h0', h1', h2', h3', h4', h5', hx', hc', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (hx.symm.trans hx')
  have e2 : st₂ = st₂' := Vector.toList_inj.mp (has_inj hi h4 h4')
  subst e2
  have e1 : st₁ = st₁' := Vector.toList_inj.mp (has_inj hi h3 h3')
  subst e1
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (has_inj hi h2 h2')
  exact ⟨W.label_injective (has_inj hi h0 h0'), W.enc₁_injective (has_inj hi h1 h1'),
    W.enc₂_injective (has_inj hi h5 h5'), hc.trans hc'.symm⟩

theorem parseThird_unique {H : Hist} {x : List UInt8} {T : Table} {sb sb' gm gm' R R' c c' t t' v v'}
    (h : ParseThird W H x T sb gm R c t v) (h' : ParseThird W H x T sb' gm' R' c' t' v') :
    sb = sb' ∧ gm = gm' ∧ R = R' ∧ c = c' ∧ t = t' ∧ v = v' := by
  obtain ⟨st₀, r₁, st₁, st₂, st₃, r₂, st₄, h0, h1, h2, h3, h4, h5, h6, hx, hc, ht, hi⟩ := h
  obtain ⟨st₀', r₁', st₁', st₂', st₃', r₂', st₄', h0', h1', h2', h3', h4', h5', h6', hx', hc', ht',
    -⟩ := h'
  obtain ⟨rfl, rfl⟩ := W.afterValues_injective (hx.symm.trans hx')
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (has_inj hi h6 h6')
  have e2 : st₂ = st₂' := Vector.toList_inj.mp (has_inj hi h4 h4')
  subst e2
  have e1 : st₁ = st₁' := Vector.toList_inj.mp (has_inj hi h3 h3')
  subst e1
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (has_inj hi h2 h2')
  exact ⟨W.label_injective (has_inj hi h0 h0'), W.enc₁_injective (has_inj hi h1 h1'),
    W.enc₂_injective (has_inj hi h5 h5'), hc.trans hc'.symm, ht.trans ht'.symm, rfl⟩

theorem length_tag : tag.length = 16 := rfl

theorem length_label (sb : Vector UInt8 64) : (W.label sb).length = 112 := by
  simp [Wire.label, length_tag]

/-- An input after a root is not both the first and the second. -/
theorem parseFirst_parseSecond {H : Hist} {x : List UInt8} {T : Table} {sb sb' gm gm' R c}
    (h : ParseFirst W H x T sb gm) (h' : ParseSecond W H x T sb' gm' R c) : False := by
  obtain ⟨st₀, r₁, h0, -, hx, hi⟩ := h
  obtain ⟨-, -, -, st₂, st₃, r₂, -, -, -, -, h4, -, hx', -, -⟩ := h'
  obtain ⟨rfl, -⟩ := Wire.afterRoot_injective (hx.symm.trans hx')
  have := congrArg List.length (has_inj hi h0 h4)
  simp [length_label] at this

theorem parseFirst_parseThird {H : Hist} {x : List UInt8} {T : Table} {sb sb' gm gm' R c t v}
    (h : ParseFirst W H x T sb gm) (h' : ParseThird W H x T sb' gm' R c t v) : False := by
  obtain ⟨_, _, _, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

theorem parseSecond_parseThird {H : Hist} {x : List UInt8} {T : Table} {sb sb' gm gm' R R' c c' t v}
    (h : ParseSecond W H x T sb gm R c) (h' : ParseThird W H x T sb' gm' R' c' t v) : False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

end Parse

/-! ## Each fresh query is bad with small probability -/

section Probability

variable {S : Finset (List UInt8)}

/-- A cache on a finite set `S` of inputs. -/
abbrev SCache (S : Finset (List UInt8)) :=
  (OracleSpec.ofFn fun d : ↥S => (fun _ : List UInt8 => Bytes32) d.1).QueryCache

/-- The inputs a cache on `S` holds. -/
def histOf (c : SCache S) : Hist := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))

/-- The table that completes a cache on `S` with `g`, fixed off `S`. -/
noncomputable def tableOf (c : SCache S) (g : ↥S → Bytes32) : Table :=
  extendTable (R := fun _ : List UInt8 => Bytes32) S (completeTable c g)

theorem mem_histOf {c : SCache S} {d : List UInt8} :
    d ∈ histOf c ↔ ∃ h : d ∈ S, c ⟨d, h⟩ ≠ none := by
  simp [histOf, mem_cacheDom]

theorem tableOf_subtype (c : SCache S) (g : ↥S → Bytes32) (d : ↥S) :
    tableOf c g d.1 = completeTable c g d :=
  extendTable_subtype (R := fun _ : List UInt8 => Bytes32) S _ d

theorem tableOf_eq_of_mem (c : SCache S) {d : List UInt8} (hd : d ∈ histOf c)
    (g g' : ↥S → Bytes32) : tableOf c g d = tableOf c g' d := by
  obtain ⟨hS, hne⟩ := mem_histOf.mp hd
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hne
  have e := tableOf_subtype c g ⟨d, hS⟩
  have e' := tableOf_subtype c g' ⟨d, hS⟩
  simp only at e e'
  rw [e, e']
  simp [completeTable, hv]

theorem tableOf_fresh (c : SCache S) {t : ↥S} (ht : c t = none) (g : ↥S → Bytes32) :
    tableOf c g t.1 = g t := by
  rw [tableOf_subtype]
  simp [completeTable, ht]

theorem tableOf_of_not_mem (c : SCache S) {d : List UInt8} (hS : d ∈ S) (hd : d ∉ histOf c)
    (g : ↥S → Bytes32) : tableOf c g d = g ⟨d, hS⟩ := by
  have h : c ⟨d, hS⟩ = none := by
    by_contra h
    exact hd (mem_histOf.mpr ⟨hS, h⟩)
  exact tableOf_fresh c h g

theorem card_bytes32 : Fintype.card Bytes32 = 2 ^ 256 := by
  rw [Common.card_vector_uInt8]
  norm_num

-- The linter runs out of recursion depth on this proof.
set_option linter.constructorNameAsVariable false in
/-- The answers a collision can take: at most `3 |H| + 2`. -/
theorem card_collSet_le (H : Hist) (x : List UInt8) (T₀ : Table) :
    (H.image T₀ ∪ (insert x H).biUnion fun y => Finset.univ.filter fun u : Bytes32 =>
      u.toList = y.take 32 ∨ rootWords u = (y.drop 32).take 64).card ≤ 3 * H.card + 2 := by
  have h1 : ∀ y : List UInt8, (Finset.univ.filter fun u : Bytes32 =>
      u.toList = y.take 32 ∨ rootWords u = (y.drop 32).take 64).card ≤ 2 := by
    intro y
    rw [Finset.filter_or]
    refine (Finset.card_union_le _ _).trans ?_
    have ha : (Finset.univ.filter fun u : Bytes32 => u.toList = y.take 32).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => by
        simp only [Finset.mem_filter] at ha hb
        exact Vector.toList_inj.mp (ha.2.trans hb.2.symm)
    have hb : (Finset.univ.filter fun u : Bytes32 =>
        rootWords u = (y.drop 32).take 64).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => by
        simp only [Finset.mem_filter] at ha hb
        exact rootWords_injective (ha.2.trans hb.2.symm)
    omega
  refine (Finset.card_union_le _ _).trans ?_
  have h2 := Finset.card_biUnion_le (s := insert x H) (t := fun y =>
    Finset.univ.filter fun u : Bytes32 => u.toList = y.take 32 ∨ rootWords u = (y.drop 32).take 64)
  have h3 : ∑ y ∈ insert x H, (Finset.univ.filter fun u : Bytes32 =>
      u.toList = y.take 32 ∨ rootWords u = (y.drop 32).take 64).card ≤ (insert x H).card * 2 := by
    simpa using Finset.sum_le_card_nsmul _ _ 2 fun y _ => h1 y
  have h4 := Finset.card_insert_le x H
  have h5 := Finset.card_image_le (s := H) (f := T₀)
  nlinarith

/-- **A collision has probability at most `(3 |H| + 2) / 2^256`.** -/
theorem prob_coll (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[Coll (histOf c) t.1 (tableOf c g)] ≤
      ((3 * (histOf c).card + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  let Bad : Finset Bytes32 := (histOf c).image (tableOf c g₀) ∪ (insert t.1 (histOf c)).biUnion
    fun y => Finset.univ.filter fun u : Bytes32 =>
      u.toList = y.take 32 ∨ rootWords u = (y.drop 32).take 64
  refine (prEvent_mono _ _ (fun g => g t ∈ Bad) fun g h => ?_).trans ?_
  · rw [← tableOf_fresh c ht g]
    rcases h with ⟨y, hy, hyx⟩ | ⟨y, hy, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨y, hy, by rw [tableOf_eq_of_mem c hy g₀ g, hyx]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, hy, by simpa using h⟩)
  · refine (prEvent_cell t (fun u => u ∈ Bad)).trans ?_
    rw [SampleableType.prEvent_uniformSample, card_bytes32]
    have hc := card_collSet_le (histOf c) t.1 (tableOf c g₀)
    have : ((Finset.univ.filter fun u : Bytes32 => u ∈ Bad).card : ℝ≥0∞) ≤
        ((3 * (histOf c).card + 2 : ℕ) : ℝ≥0∞) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact_mod_cast hc
    rw [Nat.cast_pow, Nat.cast_ofNat]
    gcongr

/-- The first round's fresh part has probability at most the round error. -/
theorem prob_freshFirst (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S) (ht : c t = none)
    (hlen : t.1.length = 96) (sb : Vector UInt8 64) (gm : B.Msg₁) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[FreshFirst W (histOf c) t.1 (tableOf c g) sb gm] ≤
      (roundError P B : ℝ≥0∞) := by
  let f : Bytes32 → ↥S := fun u => ⟨u.toList, hS₀ u⟩
  let Q : Bytes32 → Bytes32 → Bytes32 → Prop := fun a b d =>
    ¬ State₁ (W.decode sb) gm ∧ State₂ (W.decode sb) gm (W.chal a, W.chal b, W.chal d)
  refine (prEvent_mono _ _ (fun g => f (g t) ≠ t ∧ f (g (f (g t))) ≠ t ∧
    f (g (f (g t))) ≠ f (g t) ∧ Q (g t) (g (f (g t))) (g (f (g (f (g t))))))
    fun g h => ?_).trans ?_
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [tableOf_fresh c ht g] at h1 h2 h3 h5
    rw [tableOf_of_not_mem c (hS₀ _) h1 g] at h2 h3 h5
    rw [tableOf_of_not_mem c (hS₀ _) h2 g] at h5
    refine ⟨fun e => ?_, fun e => ?_, fun e => h3 (congrArg Subtype.val e), h4, h5⟩
    · have := congrArg (fun s : ↥S => s.1.length) e
      simp [f, hlen] at this
    · have := congrArg (fun s : ↥S => s.1.length) e
      simp [f, hlen] at this
  · refine (prEvent_three_cells t f Q).trans ?_
    rw [prEvent_three_draws]
    exact prob_first_chain W (W.decode sb) gm

/-- **The rounds' bad events have probability at most the largest round error**: the parse is
read off the history, so at most one round and one parse are possible. -/
theorem prob_round (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[FirstBad W (histOf c) t.1 (tableOf c g) ∨
      SecondBad W (histOf c) t.1 (tableOf c g) ∨ ThirdBad W (histOf c) t.1 (tableOf c g)] ≤
      (roundError P B : ℝ≥0∞) := by
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  have hcg : ∀ g, ∀ d ∈ histOf c, tableOf c g d = tableOf c g₀ d := fun g d hd =>
    tableOf_eq_of_mem c hd g g₀
  by_cases h1 : ∃ sb gm, ParseFirst W (histOf c) t.1 (tableOf c g₀) sb gm
  · obtain ⟨sb, gm, hp⟩ := h1
    have hlen : t.1.length = 96 := by
      obtain ⟨st₀, r₁, -, -, hx, -⟩ := hp
      rw [hx]
      simp
    refine (prEvent_mono _ _ (fun g => FreshFirst W (histOf c) t.1 (tableOf c g) sb gm)
      fun g h => ?_).trans (prob_freshFirst W hS₀ c t ht hlen sb gm)
    rcases h with ⟨sb', gm', hp', hf⟩ | ⟨sb', gm', R, c', hp', -⟩ | ⟨sb', gm', R, c', tt, v, hp', -⟩
    · rw [parseFirst_congr (hcg g)] at hp'
      obtain ⟨rfl, rfl⟩ := parseFirst_unique hp' hp
      exact hf
    · rw [parseSecond_congr (hcg g)] at hp'
      exact (parseFirst_parseSecond hp hp').elim
    · rw [parseThird_congr (hcg g)] at hp'
      exact (parseFirst_parseThird hp hp').elim
  by_cases h2 : ∃ sb gm R c', ParseSecond W (histOf c) t.1 (tableOf c g₀) sb gm R c'
  · obtain ⟨sb, gm, R, c', hp⟩ := h2
    refine (prEvent_mono _ _ (fun g => ¬ State₃ (W.decode sb) gm c' R ∧
      State₄ (W.decode sb) gm c' R (W.chal (g t))) fun g h => ?_).trans ?_
    · rcases h with ⟨sb', gm', hp', -⟩ | ⟨sb', gm', R', c'', hp', hf⟩ |
        ⟨sb', gm', R', c'', tt, v, hp', -⟩
      · rw [parseFirst_congr (hcg g)] at hp'
        exact (parseFirst_parseSecond hp' hp).elim
      · rw [parseSecond_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := parseSecond_unique hp' hp
        rwa [tableOf_fresh c ht g] at hf
      · rw [parseThird_congr (hcg g)] at hp'
        exact (parseSecond_parseThird hp hp').elim
    · exact (prEvent_cell t (fun u => ¬ State₃ (W.decode sb) gm c' R ∧
        State₄ (W.decode sb) gm c' R (W.chal u))).trans (prob_second_chain W _ gm c' R)
  by_cases h3 : ∃ sb gm R c' tt v, ParseThird W (histOf c) t.1 (tableOf c g₀) sb gm R c' tt v
  · obtain ⟨sb, gm, R, c', tt, v, hp⟩ := h3
    refine (prEvent_mono _ _ (fun g => ¬ State₄ (W.decode sb) gm c' R tt ∧
      State₆ (W.decode sb) gm c' R tt v (W.chal (g t))) fun g h => ?_).trans ?_
    · rcases h with ⟨sb', gm', hp', -⟩ | ⟨sb', gm', R', c'', hp', -⟩ |
        ⟨sb', gm', R', c'', tt', v', hp', hf⟩
      · rw [parseFirst_congr (hcg g)] at hp'
        exact (parseFirst_parseThird hp' hp).elim
      · rw [parseSecond_congr (hcg g)] at hp'
        exact (parseSecond_parseThird hp' hp).elim
      · rw [parseThird_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := parseThird_unique hp' hp
        rwa [tableOf_fresh c ht g] at hf
    · exact (prEvent_cell t (fun u => ¬ State₄ (W.decode sb) gm c' R tt ∧
        State₆ (W.decode sb) gm c' R tt v (W.chal u))).trans (prob_third_chain W _ gm c' R tt v)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun g h => ?_]
    · simp
    rcases h with ⟨sb, gm, hp, -⟩ | ⟨sb, gm, R, c', hp, -⟩ | ⟨sb, gm, R, c', tt, v, hp, -⟩
    · exact h1 ⟨sb, gm, (parseFirst_congr (hcg g) _ _ _).mp hp⟩
    · exact h2 ⟨sb, gm, R, c', (parseSecond_congr (hcg g) _ _ _ _ _).mp hp⟩
    · exact h3 ⟨sb, gm, R, c', tt, v, (parseThird_congr (hcg g) _ _ _ _ _ _ _).mp hp⟩

/-- **A fresh query is bad with probability at most `roundError + (3 |H| + 2) / 2^256`.** -/
theorem prob_chainBad (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[chainBad W (histOf c) t.1 (tableOf c g)] ≤
      ((3 * (histOf c).card + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (roundError P B : ℝ≥0∞) :=
  (prEvent_or_le _ _ _).trans (add_le_add (prob_coll c t ht) (prob_round W hS₀ c t ht))

end Probability

end QuotientRpm
