-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Fresh.Opening

/-!
# Fresh Fiat–Shamir inputs: the whole skeleton

`trip_skel`: off *bad*, and if the witness table's first row is not an initial input, the honest
prover's flag stays down: every Fiat–Shamir input of `skel sh` is fresh.

* **The reduction's chain**: its first input `st₀ ‖ rootWords root` holds the witness table's root,
  a fresh answer (`trip_tree₀_key`) that is the last half of no 96-byte input (the label, of 112
  bytes, is not one); each later input begins with the previous state, a fresh answer that begins no
  input (`trip_chalH_fresh`): the quotient table's tree in between logs only nodes (64 bytes) and
  rows (longer than 192), not 96-byte inputs.
* **The openings** (`trip_opening`): the fourth and fifth states' draws checked the claims' windows
  against the initial inputs (`NoHitC`), so `WFact` holds for each opening; the openings' prefixes
  are distinct; nothing before the first opening is a permutation input (`Seeds []`).
-/

open OracleComp OracleSpec QuotientRpm
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false

section Skel

variable {S : Type} {P : Proto S Inp Out Msg Tbl Pos} {s : S} {cw : Fin 3 → Bytes32 → List UInt8}
  {K0 : List Inp}

/-- **A chain query of a fresh input**: a fresh state, which begins no input; at the claims'
challenges, no initial input has a claim window of it. -/
theorem trip_chalH_fresh (m : List UInt8) (st₀ : DSt) (hm : (.inl m : Inp) ∉ dom K0 st₀)
    (hn : st₀.hist.length < P.n) :
    Trip P s cw K0 (fun st => st = st₀) (chalH m)
      (fun x st => ∃ u : Out, u.1 = x ∧ st.hist = st₀.hist ++ [u] ∧ st.fs = st₀.fs ∧
        st.log = .inl m :: st₀.log ∧
        (∀ y ∈ dom K0 st, ∀ b, y = .inl b → b.take 32 ≠ x.toList) ∧
        (Inc P.n (.chal (.inl m)) st₀ →
          ∀ y ∈ K0, ∀ b, y = .inl b → ∀ j, (b.drop 76).take 24 ≠ cw j x)) := by
  refine (trip_chalH m _).mono (fun st hst => ?_) (fun _ _ h => h)
  subst hst
  refine ⟨hm, fun u hu hc => ⟨u, rfl, by simp [addH, hn], rfl, rfl, fun y hy b hb =>
    hu.left y ((mem_dom_addH K0 P.n st _ u y).mp hy) b hb, fun hi y hy b hb j =>
      hc hi y (Or.inr (List.mem_append_left _ hy)) b hb j⟩⟩

/-- A claims window of an initial input with a prefix of 76 bytes is the window after it. -/
theorem wFact_of {pre : List UInt8} (hpre : pre.length = 76) {w : List UInt8}
    (h : ∀ y ∈ K0, ∀ b, y = .inl b → (b.drop 76).take 24 ≠ w) : WFact K0 pre w := fun c hc => by
  have := h _ hc _ rfl
  rwa [List.drop_left' hpre] at this

/-- Inputs logged so far are all Keccak-256 inputs: no seed yet. -/
theorem seeds_nil {st : DSt} (h : ∀ y ∈ st.log, IsInl y) : Seeds [] st := fun y hy w hw _ => by
  obtain ⟨b, rfl⟩ := h y hy
  cases hw

/-- The skeleton's shapes: secret witness and quotient tables, a public wiring table; the
openings' shapes and prefixes. -/
structure SkelOK (sh : Shape) : Prop where
  witness : sh.witness.secret = some 0
  depth : 1 ≤ sh.witness.depth₀
  quotient : sh.quotient.secret = some 1
  wiring : sh.wiring.secret = none
  okW : ShapeOK sh.witness
  okσ : ShapeOK sh.wiring
  okQ : ShapeOK sh.quotient
  preW : sh.witness.ivPrefix.length = 76
  preσ : sh.wiring.ivPrefix.length = 76
  preQ : sh.quotient.ivPrefix.length = 76
  neWσ : sh.witness.ivPrefix ≠ sh.wiring.ivPrefix
  neWQ : sh.witness.ivPrefix ≠ sh.quotient.ivPrefix
  neσQ : sh.wiring.ivPrefix ≠ sh.quotient.ivPrefix

theorem keyD_len {K0 : List Inp} {st st' : DSt} {Φ : Inp → Prop} {h : Bytes32} (hk : KeyD K0 st h)
    (he : Ext Φ st st') (hΦ : ∀ y, Φ y → ∃ b, y = .inl b ∧ b.length ≠ 64 ∧ b.length ≠ 96) :
    KeyD K0 st' h := hk.ext he fun y hy b hb => by
  obtain ⟨b', rfl, h1, h2⟩ := hΦ y hy
  cases hb
  exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem key96_ext {K0 : List Inp} {st st' : DSt} {Φ : Inp → Prop} {x : Bytes32}
    (hk : ∀ y ∈ dom K0 st, ∀ b, y = .inl b → b.length = 96 → b.take 32 ≠ x.toList)
    (he : Ext Φ st st') (hΦ : ∀ y, Φ y → ∃ b, y = .inl b ∧ b.length ≠ 96) :
    ∀ y ∈ dom K0 st', ∀ b, y = .inl b → b.length = 96 → b.take 32 ≠ x.toList :=
  fun y hy b hb hl => (he.mem_dom hy).elim (fun hy => hk y hy b hb hl) fun hy => by
    obtain ⟨b', rfl, h1⟩ := hΦ y hy
    cases hb
    exact absurd hl h1

theorem logInl_ext {st st' : DSt} {Φ : Inp → Prop} (h : ∀ y ∈ st.log, IsInl y) (he : Ext Φ st st')
    (hΦ : ∀ y, Φ y → IsInl y) : ∀ y ∈ st'.log, IsInl y := fun y hy => by
  obtain ⟨n, h1, p1⟩ := he.log
  rw [h1] at hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hΦ y (p1 y hy)
  · exact h y hy

/-- **The skeleton**: off *bad*, if the witness table's first row is not an initial input, the
flag stays down. -/
theorem trip_skel (sh : Shape) (hsh : SkelOK sh) (hrow : ∀ h k x, RowLike (P.rowFn s h k x))
    (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0))
    (hclσ : ClaimsAt P (5 + openChals sh.witness) 3 (cw 1))
    (hclQ : ClaimsAt P (5 + openChals sh.witness + openChals sh.wiring) 3 (cw 2))
    (hn : 5 + openChals sh.witness + openChals sh.wiring ≤ P.n) (st₀ : DSt) :
    Trip P s cw K0
      (fun st => st = st₀ ∧ st₀.log = [] ∧ st₀.hist = [] ∧ st₀.fs = false ∧
        P.rowFn s [] 0 0 ∉ K0)
      (skel sh) (fun _ st => st.fs = false) := by
  unfold skel
  refine Trip.intro fun st' ⟨h1, hlog, hhist, hfs, hr0⟩ => ?_
  subst h1
  have h0 : P.rowFn s [] 0 0 ∉ dom K0 st' := by simpa [dom, hlog] using hr0
  obtain ⟨d, hd⟩ : ∃ d, sh.witness.depth₀ = d + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hsh.depth).symm⟩
  -- the witness table's tree
  refine Trip.bind (trip_tree₀_key sh.witness 0 hsh.witness d hd st' hrow hcK h0) fun lvW =>
    Trip.intro fun st₁ ⟨he₁, hl₁, hk₁⟩ => ?_
  -- the label
  refine Trip.bind (trip_hashH_ext (kcTag ++ sh.st.indexRoot.toList ++ sh.st.stmt.toList)
    (fun y => ∃ b, y = .inl b ∧ b.length ≠ 64 ∧ b.length ≠ 96) ⟨_, rfl, by simp [kcTag],
      by simp [kcTag]⟩ st₁) fun d₀ => Trip.intro fun st₂ ⟨he₂, _⟩ => ?_
  have hk₂ : KeyD K0 st₂ (rootOf lvW) := keyD_len hk₁ he₂.1 fun y h => h
  have hlog₂ : ∀ y ∈ st₂.log, IsInl y := logInl_ext (logInl_ext (by simp [hlog]) he₁.1
    fun y h => h.elim Len64.isInl RowLike.isInl) he₂.1 fun y ⟨b, hb, _⟩ => ⟨b, hb⟩
  have hh₂ : st₂.hist = [] := by rw [he₂.2, he₁.2, hhist]
  have hfs₂ : st₂.fs = false := by rw [he₂.1.fs, he₁.1.fs, hfs]
  -- the first challenges
  have ht₁ : (.inl (d₀.toList ++ rootWords (rootOf lvW)) : Inp) ∉ dom K0 st₂ := fun hm =>
    (hk₂ _ hm _ rfl).2 (by simp) (by simp)
  refine Trip.bind (trip_chalH_fresh _ st₂ ht₁ (by rw [hh₂]; simp; omega)) fun x₁ =>
    Trip.intro fun st₃ ⟨u₁, hu₁, hh₃, hfs₃, hlog₃, hk₃, _⟩ => ?_
  have ht₂ : (.inl x₁.toList : Inp) ∉ dom K0 st₃ := fun hm => hk₃ _ hm _ rfl (by simp)
  refine Trip.bind (trip_chalH_fresh _ st₃ ht₂ (by rw [hh₃, hh₂]; simp; omega)) fun x₂ =>
    Trip.intro fun st₄ ⟨u₂, hu₂, hh₄, hfs₄, hlog₄, hk₄, _⟩ => ?_
  have ht₃ : (.inl x₂.toList : Inp) ∉ dom K0 st₄ := fun hm => hk₄ _ hm _ rfl (by simp)
  refine Trip.bind (trip_chalH_fresh _ st₄ ht₃ (by rw [hh₄, hh₃, hh₂]; simp; omega)) fun x₃ =>
    Trip.intro fun st₅ ⟨u₃, hu₃, hh₅, hfs₅, hlog₅, hk₅, _⟩ => ?_
  -- the quotient table's tree
  refine Trip.bind (trip_tree₀_secret sh.quotient 1 hsh.quotient st₅ hrow) fun lvQ =>
    Trip.intro fun st₆ ⟨he₆, hl₆⟩ => ?_
  have hk₆ := key96_ext (fun y hy b hb _ => hk₅ y hy b hb) he₆.1 fun y h => h.elim
    (fun ⟨b, hb, hl⟩ => ⟨b, hb, by omega⟩) (fun ⟨b, hb, hl⟩ => ⟨b, hb, by omega⟩)
  have ht₄ : (.inl (x₃.toList ++ rootWords (rootOf lvQ)) : Inp) ∉ dom K0 st₆ := fun hm =>
    hk₆ _ hm _ rfl (by simp) (by simp)
  have hh₆ : st₆.hist = [u₁, u₂, u₃] := by rw [he₆.2, hh₅, hh₄, hh₃, hh₂]; rfl
  refine Trip.bind (trip_chalH_fresh _ st₆ ht₄ (by rw [hh₆]; simp; omega)) fun x₄ =>
    Trip.intro fun st₇ ⟨u₄, hu₄, hh₇, hfs₇, hlog₇, hk₇, hc₇⟩ => ?_
  have hC₄ := hc₇ ⟨⟨_, rfl⟩, by rw [hh₆]; simp, by rw [hh₆]; simp; omega⟩
  -- the values
  refine Trip.bind (mid := fun m st => st = st₇) ((trip_getMsg _).mono (fun st h => h)
    (fun _ _ h => h)) fun m => Trip.intro fun st₈ h₈ => ?_
  subst st₈
  have ht₅ : (.inl (x₄.toList ++ (takeScalars m 5).1.flatMap scalarWord) : Inp) ∉ dom K0 st₇ :=
    fun hm => hk₇ _ hm _ rfl (by simp)
  refine Trip.bind (trip_chalH_fresh _ st₇ ht₅ (by rw [hh₇, hh₆]; simp; omega)) fun x₅ =>
    Trip.intro fun st₉ ⟨u₅, hu₅, hh₉, hfs₉, hlog₉, _, hc₉⟩ => ?_
  have hC₅ := hc₉ ⟨⟨_, rfl⟩, by rw [hh₇, hh₆]; simp, by rw [hh₇, hh₆]; simp; omega⟩
  have hh₉' : st₉.hist = [u₁, u₂, u₃, u₄, u₅] := by rw [hh₉, hh₇, hh₆]; rfl
  -- the wiring table's tree
  refine Trip.bind (trip_tree₀_public sh.wiring hsh.wiring st₉) fun lvσ =>
    Trip.intro fun st₁₀ ⟨he₁₀, hl₁₀⟩ => ?_
  have hlog₁₀ : ∀ y ∈ st₁₀.log, IsInl y := by
    refine logInl_ext ?_ he₁₀.1 fun y h => h
    intro y hy
    rw [hlog₉, hlog₇] at hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · have hy' : y ∈ st₆.log := hy
      refine logInl_ext ?_ he₆.1 (fun y h => h.elim Len64.isInl RowLike.isInl) y hy'
      intro y hy
      rw [hlog₅, hlog₄, hlog₃] at hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
      · exact hlog₂ y hy
  have hh₁₀ : st₁₀.hist = [u₁, u₂, u₃, u₄, u₅] := by rw [he₁₀.2, hh₉']
  have hfs₁₀ : st₁₀.fs = false := by
    rw [he₁₀.1.fs, hfs₉, hfs₇, he₆.1.fs, hfs₅, hfs₄, hfs₃, hfs₂]
  -- the witness table's opening
  refine Trip.bind ((trip_opening sh.witness hsh.okW lvW (by rw [hl₁]) 5 4 (cw 0) hclW []
    hsh.preW (by simp) st₁₀).mono (fun st hst => ⟨hst, by rw [hh₁₀]; rfl, ?_, seeds_nil hlog₁₀⟩)
    (fun _ _ h => h)) fun oW => Trip.intro fun st₁₁ ⟨he₁₁, hg₁₁, hs₁₁⟩ => ?_
  · have e : ([u₁, u₂, u₃, u₄, u₅].getD 4 default).1 = x₅ := by simp [hu₅]
    rw [hh₁₀, e]
    exact wFact_of hsh.preW fun y hy b hb => hC₅ y hy b hb 0
  -- the wiring table's opening
  have hlen₁₁ : st₁₁.hist.length = 5 + openChals sh.witness := by
    unfold HistGrow at hg₁₁; rw [hg₁₁, hh₁₀]; simp; omega
  obtain ⟨e₁₁, he₁₁h⟩ := he₁₁.hist
  refine Trip.bind ((trip_opening sh.wiring hsh.okσ lvσ (by rw [hl₁₀]) _ 3 (cw 1) hclσ
    [sh.witness.ivPrefix] hsh.preσ (by simp [hsh.preW, hsh.neWσ]) st₁₁).mono
    (fun st hst => ⟨hst, hlen₁₁, ?_, hs₁₁⟩) (fun _ _ h => h)) fun oσ =>
      Trip.intro fun st₁₂ ⟨he₁₂, hg₁₂, hs₁₂⟩ => ?_
  · have e : (([u₁, u₂, u₃, u₄, u₅] ++ e₁₁).getD 3 default).1 = x₄ := by simp [hu₄]
    rw [he₁₁h, hh₁₀, e]
    exact wFact_of hsh.preσ fun y hy b hb => hC₄ y hy b hb 1
  -- the quotient table's opening
  have hlen₁₂ : st₁₂.hist.length = 5 + openChals sh.witness + openChals sh.wiring := by
    unfold HistGrow at hg₁₂; rw [hg₁₂, hlen₁₁]; omega
  obtain ⟨e₁₂, he₁₂h⟩ := he₁₂.hist
  refine Trip.bind ((trip_opening sh.quotient hsh.okQ lvQ (by rw [hl₆]) _ 3 (cw 2) hclQ
    [sh.witness.ivPrefix, sh.wiring.ivPrefix] hsh.preQ
    (by simp [hsh.preW, hsh.preσ, hsh.neWQ, hsh.neσQ]) st₁₂).mono
    (fun st hst => ⟨hst, hlen₁₂, ?_, by simpa using hs₁₂⟩) (fun _ _ h => h)) fun oQ =>
      Trip.intro fun st₁₃ ⟨he₁₃, _, _⟩ => ?_
  · have e : (([u₁, u₂, u₃, u₄, u₅] ++ e₁₁ ++ e₁₂).getD 3 default).1 = x₄ := by simp [hu₄]
    rw [he₁₂h, he₁₁h, hh₁₀, e]
    exact wFact_of hsh.preQ fun y hy b hb => hC₄ y hy b hb 2
  exact (Trip.pure _ _).mono (fun st hst => by
    subst hst; rw [he₁₃.fs, he₁₂.fs, he₁₁.fs, hfs₁₀]) (fun _ _ h => h)

end Skel

end QuotientZk.Deployed.Fresh
