-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Fresh.Duplex
import QuotientZk.Deployed.Fresh.Prob

/-!
# Fresh Fiat–Shamir inputs: an opening

The steps of `recursive_prover` (`sendK`, `drawO`, `rounds`, `drawMany`, `commitNext`, `ood`,
`queryPhase`, `middle`) keep the duplex's capacity fresh (`CapFresh`), so every draw's input is
fresh; they count their draws (`HistGrow`, `qpCount`, `middleChals`) and the scalars waiting
(`absorbN`): at every grinding there are two or three (`ShapeOK`).

**The opening's first draw** (`trip_opening`). Its seed is the permutation of `seedInput iv`, `iv` the
digest of the prefix and the claims. The claims' first 24 bytes are a window read off a chain
state (`ClaimsAt`), and no initial input with this opening's prefix has that window (`WFact`, from
the chain state's draw): so the prefix and the claims are a logged input, and its digest `iv` is a
logged answer. Its seed state is no initial input (`GInv.seed`), and no logged one: the logged states
of zero capacity are the seeds of the openings before (`Seeds`), of other prefixes, whose digests
differ from `iv` (`GInv.dig`). The seed's answer is fresh: so is the duplex's capacity from then on.
-/

open OracleComp OracleSpec QuotientRpm
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false

/-! ## Counting -/

/-- The positions' draws for `q` queries in a tree of `len` levels. -/
def posDraws (len q : ℕ) : ℕ := (q + 192 / max (len - 1) 1 - 1) / (192 / max (len - 1) 1)

/-- A query phase's draws, at level `lvl` of commitments of `lens` levels. -/
def qpCount (lens : List ℕ) (lvl q : ℕ) : ℕ := posDraws (lens.getD lvl 0) q + 1

/-- The draws of the levels between the first and the last. -/
def middleChals : List ℕ → ℕ → List (ℕ × ℕ × ℕ) → List ℕ → ℕ
  | _, _, [], _ => 0
  | lens, lvl, (folds, depth, oodN) :: rest, q :: qs =>
    folds + oodN + qpCount (lens ++ [depth + 1]) lvl q + middleChals (lens ++ [depth + 1]) (lvl + 1) rest qs
  | _, _, _ :: _, [] => 0

/-- The commitments' levels after them. -/
def middleLens : List ℕ → List (ℕ × ℕ × ℕ) → List ℕ → List ℕ
  | lens, [], _ => lens
  | lens, (_, depth, _) :: rest, _ :: qs => middleLens (lens ++ [depth + 1]) rest qs
  | lens, _ :: _, [] => lens

/-- **An opening's draws.** -/
def openChals (sh : OpenShape) : ℕ :=
  1 + 6 + sh.ood₀ + qpCount [sh.depth₀ + 1, sh.depth₁ + 1] 0 (sh.queries.headD 0) +
    middleChals [sh.depth₀ + 1, sh.depth₁ + 1] 1 sh.levels (sh.queries.drop 1) + sh.lastFolds +
    qpCount (middleLens [sh.depth₀ + 1, sh.depth₁ + 1] sh.levels (sh.queries.drop 1))
      (sh.levels.length + 1) (sh.queries.getLastD 0) + (sh.residualVars - 1) + 1

/-- The shapes whose grindings find two or three scalars waiting. -/
def ShapeOK (sh : OpenShape) : Prop :=
  1 ≤ sh.ood₀ ∧ (∀ e ∈ sh.levels, 1 ≤ e.2.2) ∧ absorbN 2 (2 ^ sh.residualVars) < 4

theorem getD_map_length (l : List (List (List Bytes32))) (i : ℕ) :
    (l.map List.length).getD i 0 = (l.getD i []).length := by
  rw [show (0 : ℕ) = List.length ([] : List (List Bytes32)) from rfl, List.getD_map]

/-! ## The steps -/

section OSteps

variable {S : Type} {P : Proto S Inp Out Msg Tbl Pos} {s : S} {cw : Fin 3 → Bytes32 → List UInt8}
  {K0 : List Inp}

/-- **Sending scalars**: absorbed. -/
theorem trip_sendK (o : OSt) (k : ℕ) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ CapFresh K0 st₀ o.dx) (sendK o k)
      (fun o' st => ExtP DFrame st₀ st ∧ CapFresh K0 st o'.dx ∧
        o'.dx.pend.length = absorbN o.dx.pend.length k ∧ o'.trees = o.trees) := by
  unfold sendK
  refine Trip.bind (trip_absorbAll o.dx _ st₀) fun dx => ?_
  exact (Trip.pure _ _).mono (fun st ⟨he, hc, hp⟩ => ⟨he, hc, by
    rw [hp]; show absorbN _ (takeScalars o.items k).1.length = _; rw [takeScalars_length], rfl⟩)
    (fun _ _ h => h)

/-- **A draw**, then the next message. -/
theorem trip_drawO (o : OSt) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ InpFresh K0 st₀ o.dx) (drawO o)
      (fun r st => Ext DFrame st₀ st ∧ HistGrow P.n 1 st₀ st ∧ CapFresh K0 st r.2.dx ∧
        r.2.dx.pend = [] ∧ r.2.trees = o.trees) := by
  unfold drawO
  refine Trip.bind (trip_draw o.dx st₀) fun r => Trip.intro fun st₁ hr => ?_
  refine Trip.bind (mid := fun m st => st = st₁) ((trip_getMsg _).mono (fun st h => h)
    (fun _ _ h => h)) fun m => ?_
  exact (Trip.pure _ _).mono (fun st hst => by subst hst; exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, rfl⟩)
    (fun _ _ h => h)

/-- **Rounds**: draw, send two scalars. -/
theorem trip_rounds : ∀ (o : OSt) (k : ℕ) (st₀ : DSt),
    Trip P s cw K0 (fun st => st = st₀ ∧ CapFresh K0 st₀ o.dx) (rounds o k)
      (fun o' st => Ext DFrame st₀ st ∧ HistGrow P.n k st₀ st ∧ CapFresh K0 st o'.dx ∧
        o'.dx.pend.length = (if k = 0 then o.dx.pend.length else 2) ∧ o'.trees = o.trees)
  | o, 0, st₀ => by
    unfold rounds
    exact Trip.ginv ((Trip.pure _ _).mono (fun st ⟨hg, hst, hc⟩ => by
      subst hst; exact ⟨Ext.refl _, HistGrow.refl hg.hist, hc, by simp, rfl⟩) (fun _ _ h => h))
  | o, k + 1, st₀ => by
    unfold rounds
    refine Trip.bind ((trip_drawO o st₀).mono (fun st ⟨h1, h2⟩ => ⟨h1, h2.inp⟩) (fun _ _ h => h))
      fun r => Trip.intro fun st₁ ⟨he₁, hh₁, hc₁, hp₁, ht₁⟩ => ?_
    refine Trip.bind ((trip_sendK r.2 2 st₁).mono (fun st h => ⟨h, hc₁⟩) (fun _ _ h => h))
      fun o₂ => Trip.intro fun st₂ ⟨he₂, hc₂, hp₂, ht₂⟩ => ?_
    refine ((trip_rounds o₂ k st₂).mono (fun st h => ⟨h, hc₂⟩) fun o' st ⟨he, hh, hc, hp, ht⟩ =>
      ⟨he₁.trans (he₂.1.trans he), ?_, hc, ?_, by rw [ht, ht₂, ht₁]⟩)
    · have := (hh₁.trans (HistGrow.of_eq he₂.2 (by unfold HistGrow at hh₁; omega) rfl)).trans hh
      simpa [Nat.add_comm] using this
    · rw [hp]; simp [hp₂, hp₁, absorbN, absorb1]

/-- **Draws**. -/
theorem trip_drawMany : ∀ (o : OSt) (m : ℕ) (st₀ : DSt),
    Trip P s cw K0 (fun st => st = st₀ ∧ InpFresh K0 st₀ o.dx) (drawMany o m)
      (fun r st => Ext DFrame st₀ st ∧ HistGrow P.n m st₀ st ∧ r.2.trees = o.trees ∧
        ((m = 0 ∧ st = st₀ ∧ r.2.dx = o.dx) ∨ (1 ≤ m ∧ CapFresh K0 st r.2.dx ∧ r.2.dx.pend = [])))
  | o, 0, st₀ => by
    unfold drawMany
    exact Trip.ginv ((Trip.pure _ _).mono (fun st ⟨hg, hst, _⟩ => by
      subst hst; exact ⟨Ext.refl _, HistGrow.refl hg.hist, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩)
      (fun _ _ h => h))
  | o, m + 1, st₀ => by
    unfold drawMany
    refine Trip.bind (trip_drawO o st₀) fun r => Trip.intro fun st₁ ⟨he₁, hh₁, hc₁, hp₁, ht₁⟩ => ?_
    refine Trip.bind ((trip_drawMany r.2 m st₁).mono (fun st h => ⟨h, hc₁.inp⟩) (fun _ _ h => h))
      fun r' => Trip.intro fun st₂ ⟨he₂, hh₂, ht₂, hor⟩ => ?_
    refine (Trip.pure _ _).mono (fun st hst => ?_) (fun _ _ h => h)
    subst hst
    refine ⟨he₁.trans he₂, by simpa [Nat.add_comm] using hh₁.trans hh₂, by rw [ht₂, ht₁], Or.inr
      ⟨by omega, ?_⟩⟩
    rcases hor with ⟨-, rfl, hdx⟩ | ⟨-, hc, hp⟩
    · simp only [hdx]; exact ⟨hc₁, hp₁⟩
    · exact ⟨hc, hp⟩

theorem HistGrow.cast {n c c' : ℕ} {st st' : DSt} (h : HistGrow n c st st') (hc : c = c') :
    HistGrow n c' st st' := hc ▸ h

theorem HistGrow.congr {n c : ℕ} {st st' st'' : DSt} (h : HistGrow n c st st')
    (he : st''.hist = st'.hist) : HistGrow n c st st'' := by
  unfold HistGrow at *; rw [he]; exact h

/-- **A commitment**: a tree (Keccak-256 inputs), its root absorbed. -/
theorem trip_commitNext (o : OSt) (depth : ℕ) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ CapFresh K0 st₀ o.dx) (commitNext o depth)
      (fun o' st => ExtP DFrame st₀ st ∧ CapFresh K0 st o'.dx ∧
        o'.dx.pend.length = absorbN o.dx.pend.length 2 ∧
        o'.trees.map List.length = o.trees.map List.length ++ [depth + 1]) := by
  unfold commitNext
  refine Trip.intro fun st' ⟨h1, hc⟩ => ?_
  subst h1
  have hm := trip_mapM (P := P) (s := s) (cw := cw) (K0 := K0)
    (fun i => hashH ((takeRows o.items).1.getD i []))
    (fun _ st => ExtP IsInl st' st)
    (fun a acc => Trip.intro fun st₁ he₁ => (trip_hashH_inl _ st₁).mono (fun st h => h)
      (fun b st ⟨he, _⟩ => he₁.trans he)) (List.range (2 ^ depth)) []
  refine Trip.bind (hm.mono (fun st hst => by subst hst; exact ExtP.refl _) (fun _ _ h => h))
    fun leaves => Trip.intro fun st₁ ⟨he₁, _⟩ => ?_
  refine Trip.bind (trip_levels depth leaves st₁) fun lv => Trip.intro fun st₂ ⟨he₂, hl₂⟩ => ?_
  have he₁₂ : ExtP IsInl st' st₂ := he₁.trans (he₂.mono fun y h => h.isInl)
  have hc₂ : CapFresh K0 st₂ o.dx := ⟨hc.1.ext he₁₂.1 (fun y h => h), hc.2⟩
  refine Trip.bind ((trip_absorbAll o.dx _ st₂).mono (fun st h => ⟨h, hc₂⟩) (fun _ _ h => h))
    fun dx => ?_
  exact (Trip.pure _ _).mono (fun st ⟨he, hc', hp⟩ => ⟨(he₁₂.mono fun y h => Or.inl h).trans he,
    hc', by simp [hp, rootLimbs], by simp [hl₂]⟩) (fun _ _ h => h)

/-- **An out-of-domain sample**: draws, then three scalars sent. -/
theorem trip_ood (o : OSt) (m : ℕ) (hm : 1 ≤ m) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ CapFresh K0 st₀ o.dx) (ood o m)
      (fun o' st => Ext DFrame st₀ st ∧ HistGrow P.n m st₀ st ∧ CapFresh K0 st o'.dx ∧
        o'.dx.pend.length = 3 ∧ o'.trees = o.trees) := by
  unfold ood
  refine Trip.bind ((trip_drawMany o m st₀).mono (fun st ⟨h1, h2⟩ => ⟨h1, h2.inp⟩)
    (fun _ _ h => h)) fun r => Trip.intro fun st₁ ⟨he₁, hh₁, ht₁, hor⟩ => ?_
  rcases hor with ⟨h0, -, -⟩ | ⟨-, hc₁, hp₁⟩
  · omega
  exact (trip_sendK r.2 3 st₁).mono (fun st h => ⟨h, hc₁⟩) fun o' st ⟨he, hc, hp, ht⟩ =>
    ⟨he₁.trans he.1, hh₁.congr he.2, hc, by rw [hp, hp₁]; rfl, by rw [ht, ht₁]⟩

/-- **A query phase**: grinding, the positions' draws, `λ`, two scalars sent. -/
theorem trip_queryPhase (o : OSt) (lvl q : ℕ) (st₀ : DSt) (hp : o.dx.pend.length < 4) :
    Trip P s cw K0 (fun st => st = st₀ ∧ CapFresh K0 st₀ o.dx) (queryPhase o lvl q)
      (fun o' st => Ext DFrame st₀ st ∧
        HistGrow P.n (qpCount (o.trees.map List.length) lvl q) st₀ st ∧
        CapFresh K0 st o'.dx ∧ o'.dx.pend.length = 2 ∧ o'.trees = o.trees) := by
  unfold queryPhase
  refine Trip.ginv (Trip.intro fun st' ⟨hg, h1, hc⟩ => ?_)
  subst h1
  refine Trip.bind ((trip_grind o.dx hp hc.1.2 (2 ^ 64) 0 st' (by norm_num)).mono
    (fun st hst => ⟨hst, GrindInv.of_capOK hc.1⟩) (fun _ _ h => h)) fun r =>
      Trip.intro fun st₁ ⟨he₁, hi₁, hp₁⟩ => ?_
  refine Trip.bind ((trip_drawMany _ (posDraws (o.trees.getD lvl []).length q) st₁).mono
    (fun st h => ⟨h, hi₁⟩) (fun _ _ h => h)) fun r₂ => Trip.intro fun st₂ ⟨he₂, hh₂, ht₂, hor⟩ => ?_
  have hi₂ : InpFresh K0 st₂ r₂.2.dx := by
    rcases hor with ⟨-, rfl, hdx⟩ | ⟨-, hc, -⟩
    · rw [hdx]; exact hi₁
    · exact hc.inp
  refine Trip.bind ((trip_drawO r₂.2 st₂).mono (fun st h => ⟨h, hi₂⟩) (fun _ _ h => h))
    fun r₃ => Trip.intro fun st₃ ⟨he₃, hh₃, hc₃, hp₃, ht₃⟩ => ?_
  refine (trip_sendK _ 2 st₃).mono (fun st h => ⟨h, hc₃⟩) fun o' st ⟨he, hc, hp, ht⟩ =>
    ⟨he₁.1.trans (he₂.trans (he₃.trans he.1)), ?_, hc, by rw [hp]; simp [hp₃, absorbN, absorb1],
      by rw [ht]; simp [ht₃, ht₂]⟩
  have key := (((HistGrow.of_eq he₁.2 hg.hist rfl).trans hh₂).trans hh₃).congr he.2
  exact key.cast (by simp only [qpCount, Nat.zero_add]; rw [getD_map_length])

/-- **The levels between the first and the last**: two scalars waiting before and after. -/
theorem trip_middle : ∀ (o : OSt) (lvl : ℕ) (ls : List (ℕ × ℕ × ℕ)) (qs : List ℕ) (st₀ : DSt),
    (∀ e ∈ ls, 1 ≤ e.2.2) →
    Trip P s cw K0 (fun st => st = st₀ ∧ CapFresh K0 st₀ o.dx ∧ o.dx.pend.length = 2)
      (middle o lvl ls qs)
      (fun o' st => Ext DFrame st₀ st ∧
        HistGrow P.n (middleChals (o.trees.map List.length) lvl ls qs) st₀ st ∧
        CapFresh K0 st o'.dx ∧ o'.dx.pend.length = 2 ∧
        o'.trees.map List.length = middleLens (o.trees.map List.length) ls qs)
  | o, lvl, [], qs, st₀, _ => by
    unfold middle
    exact Trip.ginv ((Trip.pure _ _).mono (fun st ⟨hg, hst, hc, hp⟩ => by
      subst hst; exact ⟨Ext.refl _, by simpa [middleChals] using HistGrow.refl hg.hist, hc, hp,
        by simp [middleLens]⟩) (fun _ _ h => h))
  | o, lvl, (folds, depth, oodN) :: rest, q :: qs, st₀, hl => by
    unfold middle
    refine Trip.intro fun st' ⟨h1, hc, hp⟩ => ?_
    subst h1
    refine Trip.bind ((trip_rounds o folds st').mono (fun st h => ⟨h, hc⟩) (fun _ _ h => h))
      fun o₁ => Trip.intro fun st₁ ⟨he₁, hh₁, hc₁, hp₁, ht₁⟩ => ?_
    refine Trip.bind ((trip_commitNext o₁ depth st₁).mono (fun st h => ⟨h, hc₁⟩) (fun _ _ h => h))
      fun o₂ => Trip.intro fun st₂ ⟨he₂, hc₂, hp₂, ht₂⟩ => ?_
    refine Trip.bind ((trip_ood o₂ oodN (hl (folds, depth, oodN) (by simp)) st₂).mono (fun st h => ⟨h, hc₂⟩)
      (fun _ _ h => h)) fun o₃ => Trip.intro fun st₃ ⟨he₃, hh₃, hc₃, hp₃, ht₃⟩ => ?_
    refine Trip.bind ((trip_queryPhase o₃ lvl q st₃ (by omega)).mono (fun st h => ⟨h, hc₃⟩)
      (fun _ _ h => h)) fun o₄ => Trip.intro fun st₄ ⟨he₄, hh₄, hc₄, hp₄, ht₄⟩ => ?_
    have hT : o₄.trees.map List.length = o.trees.map List.length ++ [depth + 1] := by
      rw [ht₄, ht₃, ht₂, ht₁]
    have hT₃ : o₃.trees.map List.length = o.trees.map List.length ++ [depth + 1] := by
      rw [ht₃, ht₂, ht₁]
    refine (trip_middle o₄ (lvl + 1) rest qs st₄ (fun e he => hl e (by simp [he]))).mono
      (fun st h => ⟨h, hc₄, hp₄⟩) fun o' st ⟨he, hh, hc, hp, ht⟩ =>
        ⟨he₁.trans (he₂.1.trans (he₃.trans (he₄.trans he))), ?_, hc, hp, by
          rw [ht, hT]; simp [middleLens]⟩
    rw [hT] at hh
    rw [hT₃] at hh₄
    have key := (((hh₁.trans (HistGrow.of_eq he₂.2 (by unfold HistGrow at hh₁; omega) rfl)).trans
      hh₃).trans hh₄).trans hh
    exact key.cast (by simp [middleChals])
  | o, lvl, _ :: _, [], st₀, _ => by
    unfold middle
    exact Trip.ginv ((Trip.pure _ _).mono (fun st ⟨hg, hst, hc, hp⟩ => by
      subst hst; exact ⟨Ext.refl _, by simpa [middleChals] using HistGrow.refl hg.hist, hc, hp,
        by simp [middleLens]⟩) (fun _ _ h => h))

end OSteps

/-! ## The opening's seed -/

/-- **An opening's claims read a challenge**: at its start (`n₀` challenges drawn), the prover's
message begins with the claims, whose first 24 bytes are the window `cwj` read off the `k`-th
challenge's chain state. -/
def ClaimsAt {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (n₀ k : ℕ) (cwj : Bytes32 → List UInt8) :
    Prop :=
  ∀ s h, h.length = n₀ → ∃ b rest, P.msgFn s h = .bytes b :: rest ∧
    b.take 24 = cwj (h.getD k default).1

/-- No initial input with the prefix `pre` has the window `w` after it. -/
def WFact (K0 : List Inp) (pre w : List UInt8) : Prop :=
  ∀ c, (.inl (pre ++ c) : Inp) ∈ K0 → c.take 24 ≠ w

/-- The logged states of zero capacity are the seeds of inputs with the prefixes `pres`. -/
def Seeds (pres : List (List UInt8)) (st : DSt) : Prop :=
  ∀ y ∈ st.log, ∀ w, y = .inr w → capOf w = zeroCap →
    ∃ p ∈ pres, ∃ c v, st.cache (.inl (p ++ c)) = some v ∧ w = seedInput v.1

theorem Seeds.ext {pres : List (List UInt8)} {st st' : DSt} (h : Seeds pres st)
    (he : Ext DFrame st st') : Seeds pres st' := by
  intro y hy w hw hz
  obtain ⟨n, h1, p1⟩ := he.log
  rw [h1] at hy
  rcases List.mem_append.mp hy with hy | hy
  · rcases p1 y hy with ⟨b, rfl⟩ | ⟨w', rfl, hw'⟩
    · cases hw
    · cases hw; exact absurd hz hw'
  · obtain ⟨p, hp, c, v, hv, hwv⟩ := h y hy w hw hz
    exact ⟨p, hp, c, v, he.cache _ _ hv, hwv⟩

theorem capOf_seedInput (iv : Bytes32) : capOf (seedInput iv) = zeroCap := by
  unfold capOf seedInput zeroCap
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_drop, Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_replicate]
  rw [if_neg (by omega)]

theorem inl_prefix_ne {p p' c c' : List UInt8} (hp : p.length = 76) (hp' : p'.length = 76)
    (hne : p ≠ p') : (.inl (p ++ c) : Inp) ≠ .inl (p' ++ c') := by
  intro h
  have := congrArg (List.take 76) (Sum.inl.inj h)
  simp [List.take_left' hp, List.take_left' hp'] at this
  exact hne this

section Opening

variable {S : Type} {P : Proto S Inp Out Msg Tbl Pos} {s : S} {cw : Fin 3 → Bytes32 → List UInt8}
  {K0 : List Inp}

/-- **The IV and the seed**: the seed's input is fresh. -/
theorem trip_ivSeed (pre b : List UInt8) (pres : List (List UInt8)) (hpre : pre.length = 76)
    (hpres : ∀ p ∈ pres, p.length = 76 ∧ p ≠ pre) (hx : (.inl (pre ++ b) : Inp) ∉ K0)
    (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀ ∧ Seeds pres st₀)
      (hashH (pre ++ b) >>= seed)
      (fun dx st => ExtP (fun _ => True) st₀ st ∧ CapFresh K0 st dx ∧ dx.pend = [] ∧
        Seeds (pres ++ [pre]) st) := by
  refine Trip.bind (mid := fun iv st => ExtP IsInl st₀ st ∧ Seeds pres st₀ ∧
      ∃ v, st.cache (.inl (pre ++ b)) = some v ∧ v.1 = iv)
    ((trip_hashH _ _).mono (fun st ⟨hst, hs⟩ => ?_) (fun _ _ h => h)) fun iv => ?_
  · subst hst
    exact ⟨fun v hv => ⟨ExtP.refl _, hs, v, hv, rfl⟩, fun hc u _ =>
      ⟨ExtP.of_addE u hc ⟨_, rfl⟩, hs, u, by simp [addE_cache], rfl⟩⟩
  refine Trip.ginv (Trip.intro fun st₁ ⟨hg, h1, hs, v, hv, hiv⟩ => ?_)
  have hs₁ : Seeds pres st₁ := hs.ext (h1.1.mono fun y h => Or.inl h)
  have hxlog : (.inl (pre ++ b) : Inp) ∈ st₁.log := by
    have := hg.dom_of (.inl (pre ++ b)) (by rw [hv]; rfl)
    simp only [dom, List.mem_append] at this
    exact this.resolve_left hx
  have hfresh : (.inr (seedInput iv) : Inp) ∉ dom K0 st₁ := by
    intro hm
    simp only [dom, List.mem_append] at hm
    rcases hm with hm | hm
    · exact hg.seed _ hxlog v hv (hiv ▸ hm)
    · obtain ⟨p, hp, c, v', hv', hw⟩ := hs₁ _ hm _ rfl (capOf_seedInput iv)
      have hvv : v'.1 = iv := (seedInput_injective hw).symm
      exact hg.dig _ hxlog _ (inl_prefix_ne hpre (hpres p hp).1 (hpres p hp).2.symm) v v' hv hv'
        (hiv.trans hvv.symm)
  refine (trip_seed iv st₁).mono (fun st hst => ⟨hst, hfresh⟩) fun dx st ⟨he, hc, hp⟩ =>
    ⟨(h1.mono fun _ _ => trivial).trans (he.mono fun _ _ => trivial), hc, hp, ?_⟩
  intro y hy w hw hz
  obtain ⟨n, hn, pn⟩ := he.1.log
  rw [hn] at hy
  rcases List.mem_append.mp hy with hy | hy
  · have hyy := pn y hy
    subst hyy
    obtain rfl := Sum.inr.inj hw
    exact ⟨pre, by simp, b, v, he.1.cache _ _ hv, by rw [hiv]⟩
  · obtain ⟨p, hp, c, v', hv', hwv⟩ := hs₁ y hy w hw hz
    exact ⟨p, by simp [hp], c, v', he.1.cache _ _ hv', hwv⟩

end Opening

end QuotientZk.Deployed.Fresh
