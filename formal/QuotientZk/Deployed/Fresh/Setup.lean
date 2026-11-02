-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Fresh

/-!
# Fresh Fiat–Shamir inputs with a setup (`FSFresh` for the statement's prover)

The statement's prover computes the circuit's commitment (the wiring table's Merkle tree) over the
oracle **before** the reduction, and labels the reduction's chain with its root: its skeleton is
`tree₀ w >>= fun lv => skel (shOf lv)` (`PcsQuotient.EndToEnd.skelWith`, `skelSetup` for the
deployed shapes). **`fsFresh_setup`**: for a public opening shape `w` (`w.secret = none`) and shapes
`shOf lv` of the deployed form, the honest prover's Fiat–Shamir inputs are fresh but with
probability

  `epsFS (|c₀| + |w.pubRows|) (tree0Bound w + n) εc δ₀`,  `n ≥ skelBound (shOf lv)`,

under `fsFresh_deployed`'s conditions on the prover. At the deployed sizes (**`fsFresh_setup_deployed`**,
**`fsFresh_setup_deployed_bits`**, with the empty cache before the proof): the wiring table's
`2^19` public rows, at most `2^24` operations for its tree and `2^70` for the skeleton,
`εFS' = epsFS (2^19) (2^24 + 2^70) 2^-191 2^-2368 ≤ 2^-113`. The skeletons are stated unfolded:
`PcsQuotient.EndToEnd.skelWith w shOf` and `skelSetup stmtBytes idW idσ idQ rowsW` are these by
definition, and the theorems apply to them as they are (`exact`).

**Why.** The setup's tree is public: it makes no Fiat–Shamir query, needs no secret and draws no
challenge, so the run is tracked from the start by the same `implB` (`Fresh/Core.lean`) and its
answers count in the bad-event budget like any other operation (`prEvent_bad_le` at
`tree0Bound w + n` operations: the setup's operations in `Q`). Its logged inputs are the public rows
and 64-byte nodes (`trip_tree₀_pub`). The rest of `trip_skel`'s argument (`trip_skel_from`) only
needs every logged input to be a Keccak-256 input (no permutation state yet, so no opening seed is
held), no challenge drawn, and the witness table's first row not held:

* **the chain's first input** `H(label) ‖ rootWords(witness root)`: the label is
  `kcTag ‖ rootOf lv ‖ stmt` (112 bytes; its state may be anything, the setup's root in it is
  public), and the input is fresh because the witness root is (`trip_tree₀_key`): its first leaf is
  a row not held, so its digest and every node above it are fresh answers, and a fresh answer is the
  start of no 64-byte input and the root words of no 96-byte input held then, the setup's included
  (`NoHit` quantifies over every input held). The first row is not held unless it is an initial
  input or one of the setup's public rows (nodes are 64 bytes, rows longer than 192): the term
  `(|c₀| + |w.pubRows|) δ₀` (`2^19 · 2^-2368` deployed; the rows are public, fixed before the
  prover's randomness);
* every later chain input and the openings are as in `trip_skel`: the wiring table's tree in `skel`
  is the setup's again (its queries now hit the cache).
-/

open OracleComp OracleSpec QuotientRpm
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false

/-! ## The setup's tree -/

/-- A public row of the opening shape `w`, as a Keccak-256 input. -/
def PubRow (w : OpenShape) (y : Inp) : Prop := ∃ b ∈ w.pubRows, y = .inl b

section Triples

variable {S : Type} {P : Proto S Inp Out Msg Tbl Pos} {s : S} {cw : Fin 3 → Bytes32 → List UInt8}
  {K0 : List Inp}

/-- `List.mapM`, with an invariant of the outputs so far, for the list's elements. -/
theorem trip_mapM_mem {α β : Type} (f : α → OracleComp DSpec β) (I : List β → DSt → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∀ acc, Trip P s cw K0 (I acc) (f a) (fun b st => I (acc ++ [b]) st)) →
      ∀ (acc : List β),
        Trip P s cw K0 (I acc) (l.mapM f) (fun bs st => I (acc ++ bs) st ∧ bs.length = l.length)
  | [], _, acc => by
    simp only [List.mapM_nil]
    exact (Trip.pure [] _).mono (fun st h => by simpa using h) (fun _ _ h => h)
  | a :: l, h, acc => by
    rw [List.mapM_cons]
    refine Trip.bind (h a List.mem_cons_self acc) fun b =>
      Trip.bind (trip_mapM_mem f I l (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) (acc ++ [b]))
        fun bs => ?_
    exact (Trip.pure (b :: bs) _).mono (fun st hst => by simpa using hst) (fun _ _ h => h)

/-- **A public tree** logs only its rows and 64-byte nodes; `depth₀ + 1` levels. -/
theorem trip_tree₀_pub (w : OpenShape) (hw : w.secret = none) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀) (tree₀ w)
      (fun lv st => ExtP (fun y => Len64 y ∨ PubRow w y) st₀ st ∧ lv.length = w.depth₀ + 1) := by
  simp only [tree₀, hw]
  have h := trip_mapM_mem (P := P) (s := s) (cw := cw) (K0 := K0) hashH
    (fun _ st => ExtP (fun y => Len64 y ∨ PubRow w y) st₀ st) w.pubRows
    (fun a ha acc => Trip.intro fun st₁ he₁ =>
      (trip_hashH_ext a (fun y => Len64 y ∨ PubRow w y) (Or.inr ⟨a, ha, rfl⟩) st₁).mono
        (fun st h => h) (fun b st ⟨he, _⟩ => he₁.trans he)) []
  refine Trip.bind (h.mono (fun st hst => by subst hst; exact ExtP.refl _) (fun _ _ h => h))
    fun leaves => Trip.intro fun st₁ ⟨he₁, _⟩ => ?_
  exact (trip_levels w.depth₀ leaves st₁).mono (fun st h => h) (fun lv st ⟨he, hl⟩ =>
    ⟨he₁.trans (he.mono fun y h => Or.inl h), hl⟩)

/-! ## The skeleton after a setup -/

/-- **The skeleton, from a state whose logged inputs are Keccak-256 inputs** (`trip_skel` with
the log not empty): off *bad*, if the witness table's first row is not held, the flag stays down. -/
theorem trip_skel_from (sh : Shape) (hsh : SkelOK sh) (hrow : ∀ h k x, RowLike (P.rowFn s h k x))
    (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0))
    (hclσ : ClaimsAt P (5 + openChals sh.witness) 3 (cw 1))
    (hclQ : ClaimsAt P (5 + openChals sh.witness + openChals sh.wiring) 3 (cw 2))
    (hn : 5 + openChals sh.witness + openChals sh.wiring ≤ P.n) (st₀ : DSt) :
    Trip P s cw K0
      (fun st => st = st₀ ∧ (∀ y ∈ st₀.log, IsInl y) ∧ st₀.hist = [] ∧ st₀.fs = false ∧
        P.rowFn s [] 0 0 ∉ dom K0 st₀)
      (skel sh) (fun _ st => st.fs = false) := by
  unfold skel
  refine Trip.intro fun st' ⟨h1, hlog, hhist, hfs, h0⟩ => ?_
  subst h1
  obtain ⟨d, hd⟩ : ∃ d, sh.witness.depth₀ = d + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hsh.depth).symm⟩
  -- the witness table's tree
  refine Trip.bind (trip_tree₀_key sh.witness 0 hsh.witness d hd st' hrow hcK h0) fun lvW =>
    Trip.intro fun st₁ ⟨he₁, hl₁, hk₁⟩ => ?_
  -- the label
  refine Trip.bind (trip_hashH_ext (kcTag ++ sh.st.indexRoot.toList ++ sh.st.stmt.toList)
    (fun y => ∃ b, y = .inl b ∧ b.length ≠ 64 ∧ b.length ≠ 96) ⟨_, rfl, by simp [kcTag],
      by simp [kcTag]⟩ st₁) fun d₀ => Trip.intro fun st₂ ⟨he₂, _⟩ => ?_
  have hk₂ : KeyD K0 st₂ (rootOf lvW) := keyD_len hk₁ he₂.1 fun y h => h
  have hlog₂ : ∀ y ∈ st₂.log, IsInl y := logInl_ext (logInl_ext hlog he₁.1
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

/-- **The setup, then the skeleton**: off *bad*, from the initial state, if the witness table's
first row is neither an initial input nor one of the setup's public rows, the flag stays down. -/
theorem trip_setup (w : OpenShape) (hw : w.secret = none)
    (shOf : List (List Bytes32) → Shape) (hsh : ∀ lv, SkelOK (shOf lv))
    (hrow : ∀ h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0))
    (hclσ : ∀ lv, ClaimsAt P (5 + openChals (shOf lv).witness) 3 (cw 1))
    (hclQ : ∀ lv, ClaimsAt P (5 + openChals (shOf lv).witness + openChals (shOf lv).wiring) 3
      (cw 2))
    (hn : ∀ lv, 5 + openChals (shOf lv).witness + openChals (shOf lv).wiring ≤ P.n) (st₀ : DSt) :
    Trip P s cw K0
      (fun st => st = st₀ ∧ st₀.log = [] ∧ st₀.hist = [] ∧ st₀.fs = false ∧
        P.rowFn s [] 0 0 ∉ K0 ++ w.pubRows.map Sum.inl)
      (tree₀ w >>= fun lv => skel (shOf lv)) (fun _ st => st.fs = false) := by
  refine Trip.intro fun st' ⟨h1, hlog, hhist, hfs, hr0⟩ => ?_
  subst h1
  refine Trip.bind (trip_tree₀_pub w hw st') fun lv => Trip.intro fun st₁ ⟨he₁, _⟩ => ?_
  refine (trip_skel_from (shOf lv) (hsh lv) hrow hcK hclW (hclσ lv) (hclQ lv) (hn lv) st₁).mono
    (fun st hst => ⟨hst, ?_, by rw [he₁.2, hhist], by rw [he₁.1.fs, hfs], ?_⟩) (fun _ _ h => h)
  · exact logInl_ext (by simp [hlog]) he₁.1 fun y h =>
      h.elim Len64.isInl fun ⟨b, _, hb⟩ => ⟨b, hb⟩
  · intro hm
    obtain ⟨b, hb, hbl⟩ := hrow [] 0 0
    rcases he₁.1.mem_dom hm with hm | hm
    · simp only [dom, hlog, List.append_nil] at hm
      exact hr0 (List.mem_append_left _ hm)
    · rcases hm with ⟨b', hb', hl'⟩ | ⟨b', hmem, hb'⟩
      · rw [hb] at hb'
        cases hb'
        omega
      · exact hr0 (List.mem_append_right _ (List.mem_map.mpr ⟨b', hmem, hb'.symm⟩))

end Triples

/-! ## The probability -/

section General

variable {S : Type} [SampleableType S]

/-- **`FSFresh` from a triple**: a computation of at most `Q` operations whose runs, from the
initial state, keep the flag down off *bad* whenever the witness table's first row avoids the list
`L`, has fresh Fiat–Shamir inputs but with probability
`Q · 6 (|c₀| + Q) / 2^256 + 2 (|c₀| + Q) · 3 εc + |L| δ₀`. -/
theorem fsFresh_of_trip {α : Type} (oa : OracleComp DSpec α) (Q : ℕ)
    (hqb : IsTotalQueryBound oa Q) (P : Proto S Inp Out Msg Tbl Pos) (c₀ : List (Inp × Out))
    (cw : Fin 3 → Bytes32 → List UInt8) (εc δ₀ : ℝ≥0∞)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc) (L : List Inp)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ δ₀)
    (htrip : ∀ s, P.rowFn s [] 0 0 ∉ L →
      Trip P s cw (c₀.map Prod.fst) (fun st => st = St.init c₀) oa (fun _ st => st.fs = false)) :
    FSFresh P oa c₀
      ((Q : ℝ≥0∞) * (6 * ((c₀.length + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        2 * (((c₀.length + Q : ℕ) : ℝ≥0∞) * (3 * εc)) + L.length * δ₀) := by
  classical
  set K0 := c₀.map Prod.fst with hK0
  set B := (Q : ℝ≥0∞) * (6 * ((c₀.length + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    2 * (((c₀.length + Q : ℕ) : ℝ≥0∞) * (3 * εc))
  unfold FSFresh
  have hlen : K0.length = c₀.length := by simp [hK0]
  have hmain : Pr{let x ← (do
      let s ← $ᵗ S
      let z ← (simulateQ (implReal P s) oa).run (St.init c₀)
      return z.2.fs)}[x = true] ≤ B + Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 ∈ L] := by
    refine prEvent_bind_le_add _ _ _ _ B fun s => ?_
    -- the tracked run
    have hproj := run_proj P s cw K0 oa (St.init c₀) false
    have e1 : Pr{let x ← (do
          let z ← (simulateQ (implReal P s) oa).run (St.init c₀)
          return z.2.fs)}[x = true] =
        Pr{let z ← (simulateQ (implB P s cw K0) oa).run (St.init c₀, false)}[
          z.2.1.fs = true] := by
      rw [show (do
          let z ← (simulateQ (implReal P s) oa).run (St.init c₀)
          return z.2.fs : ProbComp Bool) =
          (fun z => z.2.fs) <$> (simulateQ (implReal P s) oa).run (St.init c₀) by
        simp [map_eq_bind_pure_comp], prEvent_map, ← hproj.prEvent_eq, prEvent_map]
      rfl
    rw [e1]
    have hbad := prEvent_bad_le P s cw K0 εc hcw oa Q hqb (St.init c₀) rfl rfl
    rw [hlen] at hbad
    have hsplit : Pr{let z ← (simulateQ (implB P s cw K0) oa).run (St.init c₀, false)}[
          z.2.1.fs = true] ≤
        Pr{let z ← (simulateQ (implB P s cw K0) oa).run (St.init c₀, false)}[z.2.2 = true] +
        Pr{let z ← (simulateQ (implB P s cw K0) oa).run (St.init c₀, false)}[
          z.2.1.fs = true ∧ z.2.2 = false] := by
      refine le_trans (prEvent_mono _ _ _ fun z hz => ?_) (prEvent_or_le _ _ _)
      by_cases hb : z.2.2 = true
      · exact Or.inl hb
      · exact Or.inr ⟨hz, by simpa using hb⟩
    refine hsplit.trans (add_le_add hbad ?_)
    split_ifs with hr
    · exact prEvent_le_one _
    · refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hfs => ?_)
      have := htrip s hr (St.init c₀) (GInv.init P.n c₀) rfl z hz hfs.2
      rw [this] at hfs
      exact Bool.false_ne_true hfs.1
  refine hmain.trans (add_le_add le_rfl ?_)
  exact le_trans (prEvent_mono _ _ _ fun s hs => ⟨_, hs, rfl⟩)
    (pr_exists_mem_le ($ᵗ S) L (fun y s => P.rowFn s [] 0 0 = y) δ₀ fun y _ => hrow₀ y)

/-- **`FSFresh` for a skeleton with a setup**: the tree of a public opening shape `w`, then the
skeleton at shapes `shOf lv` of the deployed form, of at most `n` operations. -/
theorem fsFresh_setup (w : OpenShape) (hw : w.secret = none)
    (shOf : List (List Bytes32) → Shape) (n : ℕ) (hsh : ∀ lv, SkelOK (shOf lv))
    (hQ : ∀ lv, skelBound (shOf lv) ≤ n) (P : Proto S Inp Out Msg Tbl Pos)
    (c₀ : List (Inp × Out)) (cw : Fin 3 → Bytes32 → List UInt8) (εc δ₀ : ℝ≥0∞)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ δ₀)
    (hrow : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0))
    (hclσ : ∀ lv, ClaimsAt P (5 + openChals (shOf lv).witness) 3 (cw 1))
    (hclQ : ∀ lv, ClaimsAt P (5 + openChals (shOf lv).witness + openChals (shOf lv).wiring) 3
      (cw 2))
    (hn : ∀ lv, 5 + openChals (shOf lv).witness + openChals (shOf lv).wiring ≤ P.n) :
    FSFresh P (tree₀ w >>= fun lv => skel (shOf lv)) c₀
      (epsFS (c₀.length + w.pubRows.length) (tree0Bound w + n) εc δ₀) := by
  have h := fsFresh_of_trip (tree₀ w >>= fun lv => skel (shOf lv)) (tree0Bound w + n)
    (isTotalQueryBound_bind (qb_tree₀ w) fun lv => (skel_queryBound (shOf lv)).mono (hQ lv))
    P c₀ cw εc δ₀ hcw (c₀.map Prod.fst ++ w.pubRows.map Sum.inl) hrow₀ fun s hr =>
      (trip_setup w hw shOf hsh (hrow s) hcK hclW hclσ hclQ hn (St.init c₀)).mono
        (fun st hst => ⟨hst, rfl, rfl, rfl, hr⟩) (fun _ _ h => h)
  refine h.trans ?_
  have hL : (c₀.map Prod.fst ++ w.pubRows.map Sum.inl).length = c₀.length + w.pubRows.length := by
    simp
  have hcQ : ((c₀.length + (tree0Bound w + n) : ℕ) : ℝ≥0∞) ≤
      ((c₀.length + w.pubRows.length + (tree0Bound w + n) : ℕ) : ℝ≥0∞) :=
    Nat.cast_le.mpr (by omega)
  rw [hL]
  unfold epsFS
  gcongr

end General

/-! ## The deployed shapes -/

theorem epsFS_mono {c c' Q Q' : ℕ} (hc : c ≤ c') (hQ : Q ≤ Q') (εc δ₀ : ℝ≥0∞) :
    epsFS c Q εc δ₀ ≤ epsFS c' Q' εc δ₀ := by
  have hcQ : ((c + Q : ℕ) : ℝ≥0∞) ≤ ((c' + Q' : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr (by omega)
  have hQ' : (Q : ℝ≥0∞) ≤ Q' := Nat.cast_le.mpr hQ
  have hc' : (c : ℝ≥0∞) ≤ c' := Nat.cast_le.mpr hc
  unfold epsFS
  gcongr

/-- The wiring table's tree at `2^19` rows makes `20 · 2^19 ≤ 2^24` operations. -/
theorem tree0Bound_wiringShape (idσ : Bytes32) (rows : List (List UInt8))
    (hrows : rows.length = 2 ^ 19) : tree0Bound (wiringShape idσ rows) ≤ 2 ^ 24 := by
  simp only [tree0Bound, wiringShape, hrows]
  norm_num

section Deployed

variable {S : Type} [SampleableType S]

/-- **`FSFresh` for the statement's prover's skeleton**: the wiring table's tree (`2^19` public
rows), then the deployed skeleton whose chain is labelled with that tree's root and the statement's
bytes `stmtBytes` (`PcsQuotient.EndToEnd.skelSetup`), under `fsFresh_deployed`'s conditions:
`εFS' = epsFS (|c₀| + 2^19) (2^24 + 2^70) εc δ₀`. -/
theorem fsFresh_setup_deployed (stmtBytes : Vector UInt8 64) (idW idσ idQ : Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (P : Proto S Inp Out Msg Tbl Pos) (c₀ : List (Inp × Out)) (cw : Fin 3 → Bytes32 → List UInt8)
    (εc δ₀ : ℝ≥0∞) (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ δ₀)
    (hrow : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0)) (hclσ : ClaimsAt P 128 3 (cw 1))
    (hclQ : ClaimsAt P 242 3 (cw 2)) (hn : 242 ≤ P.n) :
    FSFresh P (tree₀ (wiringShape idσ rowsW) >>= fun lv =>
        skel (deployedShape ⟨rootOf lv, stmtBytes⟩ idW idσ idQ rowsW)) c₀
      (epsFS (c₀.length + 2 ^ 19) (2 ^ 24 + 2 ^ 70) εc δ₀) :=
  le_trans (fsFresh_setup (wiringShape idσ rowsW) rfl
      (fun lv => deployedShape ⟨rootOf lv, stmtBytes⟩ idW idσ idQ rowsW) (2 ^ 70)
      (fun lv => skelOK_deployed _ idW idσ idQ rowsW)
      (fun lv => skelBound_deployed _ idW idσ idQ rowsW hrows) P c₀ cw εc δ₀ hcw hrow₀ hrow hcK
      hclW (fun lv => by simpa [deployedShape, openChals_witness] using hclσ)
      (fun lv => by simpa [deployedShape, openChals_witness, openChals_wiring] using hclQ)
      (fun lv => by simp [deployedShape, openChals_witness, openChals_wiring]; omega))
    (epsFS_mono (by simp [wiringShape, hrows])
      (Nat.add_le_add_right (tree0Bound_wiringShape idσ rowsW hrows) _) εc δ₀)

end Deployed

/-- `epsFS c Q 2^-191 2^-2368 ≤ 2^-k'` once `Q · 6 (c + Q) + 2 (c + Q) · 3 · 2^65 + c ≤ 2^k` and
`k' + k = 256`. -/
theorem epsFS_le_of (c Q k k' : ℕ) (hk : k' + k = 256)
    (hN : Q * 6 * (c + Q) + 2 * (c + Q) * 3 * 2 ^ 65 + c ≤ 2 ^ k) :
    epsFS c Q ((2 : ℝ≥0∞) ^ 191)⁻¹ ((2 : ℝ≥0∞) ^ 2368)⁻¹ ≤ ((2 : ℝ≥0∞) ^ k')⁻¹ := by
  have e1 : ((2 : ℝ≥0∞) ^ 191)⁻¹ = 2 ^ 65 * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
    two_pow_inv_split 191 65 256 rfl
  have e2 : ((2 : ℝ≥0∞) ^ k')⁻¹ = 2 ^ k * ((2 : ℝ≥0∞) ^ 256)⁻¹ := two_pow_inv_split k' k 256 hk
  have e3 : ((2 : ℝ≥0∞) ^ 2368)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
    ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by norm_num))
  unfold epsFS
  rw [e1, e2, div_eq_mul_inv]
  set U := ((2 : ℝ≥0∞) ^ 256)⁻¹
  calc _ ≤ (Q : ℝ≥0∞) * (6 * ((c + Q : ℕ) : ℝ≥0∞) * U) +
        2 * (((c + Q : ℕ) : ℝ≥0∞) * (3 * (2 ^ 65 * U))) + c * U := by gcongr
    _ = ((Q * 6 * (c + Q) + 2 * (c + Q) * 3 * 2 ^ 65 + c : ℕ) : ℝ≥0∞) * U := by push_cast; ring
    _ ≤ ((2 ^ k : ℕ) : ℝ≥0∞) * U := by gcongr
    _ = 2 ^ k * U := by norm_num

set_option exponentiation.threshold 4000 in
/-- **At the deployed sizes**: `epsFS (2^19) (2^24 + 2^70) 2^-191 2^-2368 ≤ 2^-113`. -/
theorem epsFS_setup_le :
    epsFS (2 ^ 19) (2 ^ 24 + 2 ^ 70) ((2 : ℝ≥0∞) ^ 191)⁻¹ ((2 : ℝ≥0∞) ^ 2368)⁻¹ ≤
      ((2 : ℝ≥0∞) ^ 113)⁻¹ :=
  epsFS_le_of _ _ 143 113 rfl (by norm_num)

section DeployedBits

variable {S : Type} [SampleableType S]

/-- **`FSFresh` for the statement's prover's skeleton at our sizes**, with the empty cache before
the proof: the claims' windows of min-entropy `2^-191` and the first witness row's `2^-2368` give
`εFS' ≤ 2^-113`. -/
theorem fsFresh_setup_deployed_bits (stmtBytes : Vector UInt8 64) (idW idσ idQ : Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (P : Proto S Inp Out Msg Tbl Pos) (cw : Fin 3 → Bytes32 → List UInt8)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ ((2 : ℝ≥0∞) ^ 2368)⁻¹)
    (hrow : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0)) (hclσ : ClaimsAt P 128 3 (cw 1))
    (hclQ : ClaimsAt P 242 3 (cw 2)) (hn : 242 ≤ P.n) :
    FSFresh P (tree₀ (wiringShape idσ rowsW) >>= fun lv =>
        skel (deployedShape ⟨rootOf lv, stmtBytes⟩ idW idσ idQ rowsW)) [] ((2 : ℝ≥0∞) ^ 113)⁻¹ := by
  have h := fsFresh_setup_deployed stmtBytes idW idσ idQ rowsW hrows P [] cw _ _ hcw hrow₀ hrow hcK
    hclW hclσ hclQ hn
  rw [List.length_nil, Nat.zero_add] at h
  exact h.trans epsFS_setup_le

end DeployedBits

/-- info: 'QuotientZk.Deployed.Fresh.fsFresh_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fsFresh_setup

/-- info: 'QuotientZk.Deployed.Fresh.fsFresh_setup_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fsFresh_setup_deployed

/-- info: 'QuotientZk.Deployed.Fresh.fsFresh_setup_deployed_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fsFresh_setup_deployed_bits

end QuotientZk.Deployed.Fresh
