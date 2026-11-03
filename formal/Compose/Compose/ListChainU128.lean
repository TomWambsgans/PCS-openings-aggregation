-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/Compose/Compose/ListChainU.lean` of this repository step by step (its walk back,
-- parse, bad events, union bound and trace); only what reads the tag is copied, the tag replaced by
-- the label's first 32 bytes. Everything else of `ListChainU.lean` is reused as it is.
import Compose.ListChainU

/-!
# The list chain over any encoding, separated by the label's first 32 bytes

`ListChainU.lean` separates the seed (the label) from a step's input by a 16-byte tag: a step's
input is a label only if a state starts with the tag, and a fresh answer starting with it is bad
(`TagBad`, `2^-128` a query, `N · 2^-128 = 2^-64` at `2^64` queries). Here the separation is per
statement: a step's input `stepIn (T z) b` starts with the 32 bytes of the state `T z`, so it is the
label `y` only if `(T z).toList = y.take 32`. The parse asks that **no answer of the history is the
label's first 32 bytes** (`NoPre`), and no event pays for it: `trace_coreU'` takes it as a
hypothesis (`hseed`), which the composition discharges (`ListChainUDoom128.lean`: the univariate
label's first 32 bytes are `name ‖ iv[0:16]`, `iv` an answer, so a violation is a pair of answers,
`PairTr`, `SeedPair.lean`).

* **`chain_uniqueU'`**: `chain_uniqueU` with `NoPre y H T`, `NoPre y' H T` for the tag;
* **`ParseU'`**, **`parseU_unique'`** (from both parses' `NoPre`), **`RoundBadU'`**,
  **`listBadU' = CollU ∨ RoundBadU'`** (no tag);
* **`prob_listBadU'`**: each fresh query is bad with probability at most
  `(|H| + nRf (|H| + 1)) / 2^256 + maxErrK`;
* **`trace_coreU'`**: a run lost at the start and won at the end, whose log holds no answer equal
  to the label's first 32 bytes, asks a bad fresh query.

`ChainSpecU`'s `tag`, `tag_le` and `label_tag` are not read here.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm

/-! ## The walk back, separated by the label's first 32 bytes -/

section Walk

/-- **No answer of the history is the label's first 32 bytes.** -/
def NoPre (lab : List UInt8) (H : Hist) (T : Table) : Prop :=
  ∀ z ∈ H, (T z).toList ≠ lab.take 32

theorem NoPre.mono {lab : List UInt8} {H H' : Hist} {T : Table} (h : NoPre lab H' T)
    (hs : ∀ z ∈ H, z ∈ H') : NoPre lab H T := fun z hz => h z (hs z hz)

theorem noPre_congr {lab : List UInt8} {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) :
    NoPre lab H T ↔ NoPre lab H T' := by
  unfold NoPre
  constructor
  · intro hn z hz
    rw [← h z hz]
    exact hn z hz
  · intro hn z hz
    rw [h z hz]
    exact hn z hz

/-- A step's input's first 32 bytes are the state. -/
theorem take_stepIn_32 (st : Bytes32) (e : List UInt8) : (stepIn st e).take 32 = st.toList := by
  rw [take_stepIn_le st e le_rfl]
  exact List.take_of_length_le (by simp)

/-- **The chain before an input is determined by the input**, through injective answers, when no
answer of the history is the first 32 bytes of either label: a step's input (a state, then bytes)
is then never a label. -/
theorem chain_uniqueU' (T : Table) {H : Hist} (hi : Set.InjOn T ↑H) :
    ∀ (es es' : List (List UInt8)) (y y' : List UInt8),
      NoPre y H T → NoPre y' H T →
      (∀ z ∈ prevIn T y es, z ∈ H) → (∀ z ∈ prevIn T y' es', z ∈ H) →
      lastIn T y es = lastIn T y' es' → y = y' ∧ es = es' := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
    intro es' y y' hy _ _ hH' h
    rcases List.eq_nil_or_concat es' with rfl | ⟨L, b, rfl⟩
    · exact ⟨h, rfl⟩
    · simp only [List.concat_eq_append] at *
      exfalso
      rw [lastIn_concat] at h
      have hz : lastIn T y' L ∈ H := hH' _ (by
        rw [prevIn_concat, allIn_eq]
        simp)
      have ht := congrArg (List.take 32) h
      rw [take_stepIn_32] at ht
      exact hy _ hz ht.symm
  | append_singleton es₀ e ih =>
    intro es' y y' hy hy' hH hH' h
    rcases List.eq_nil_or_concat es' with rfl | ⟨L, b, rfl⟩
    · exfalso
      rw [lastIn_concat] at h
      have hz : lastIn T y es₀ ∈ H := hH _ (by
        rw [prevIn_concat, allIn_eq]
        simp)
      have ht := congrArg (List.take 32) h
      rw [take_stepIn_32] at ht
      exact hy' _ hz ht
    · simp only [List.concat_eq_append] at *
      rw [lastIn_concat, lastIn_concat] at h
      obtain ⟨hT, heb⟩ := stepIn_inj h
      have ha : lastIn T y es₀ ∈ H := hH _ (by
        rw [prevIn_concat, allIn_eq]
        simp)
      have ha' : lastIn T y' L ∈ H := hH' _ (by
        rw [prevIn_concat, allIn_eq]
        simp)
      have hsub : ∀ z ∈ prevIn T y es₀, z ∈ H := fun z hz => hH z (by
        rw [prevIn_concat, allIn_eq]
        exact List.mem_append_left _ hz)
      have hsub' : ∀ z ∈ prevIn T y' L, z ∈ H := fun z hz => hH' z (by
        rw [prevIn_concat, allIn_eq]
        exact List.mem_append_left _ hz)
      obtain ⟨rfl, rfl⟩ := ih L y y' hy hy' hsub hsub' (hi ha ha' hT)
      exact ⟨rfl, by rw [heb]⟩

end Walk

/-! ## The bad events -/

section Bad

variable {F St M : Type} [SampleableType F] (U : ChainSpecU F St) (C : ℕ → ListCommit M)
  (R : Piop U.K M)

/-- **`x` is round `j`'s first input**: `ParseU` with no answer of the history equal to the
label's first 32 bytes (`NoPre`) in place of the tag. -/
def ParseU' (H : Hist) (x : List UInt8) (T : Table) (j : ℕ) (s : St) (ms : List (RMsg F))
    (m : RMsg F) : Prop :=
  j < U.K.rounds.length ∧ FitsAll (U.K.rounds.take j) ms ∧ m.Fits (U.K.spec j) ∧
    x = lastIn T (U.label s) (U.absorbsS s (U.K.rounds.take j) ms ++ [U.encAt s j m]) ∧
    (∀ y ∈ prevIn T (U.label s) (U.absorbsS s (U.K.rounds.take j) ms ++ [U.encAt s j m]),
      y ∈ H) ∧
    Set.InjOn T ↑H ∧ NoPre (U.label s) H T

/-- **Round `j` is bad at its first input** (`RoundBadU` on `ParseU'`). -/
def RoundBadU' (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ j s ms m, ParseU' U H x T j s ms m ∧
    (∀ y ∈ (U.K.sqIns T x j).tail, y ∉ H) ∧ (U.K.sqIns T x j).Nodup ∧
    ∃ cs c, List.Forall₂ (· ∈ ·) cs (candLists C H T 0 ms) ∧ c ∈ optC (C j) H T m ∧
      ¬ R.pre s (opened cs ms (U.chalsT T s (U.K.rounds.take j) ms)) (c, m.2) ∧
      R.post s (opened cs ms (U.chalsT T s (U.K.rounds.take j) ms)) (c, m.2)
        (((U.K.sqIns T x j).map T).map (chalL U.K.lim))

/-- **A bad fresh query**: a collision or a bad round (no tag). -/
def listBadU' (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  U.CollU H x T ∨ RoundBadU' U C R H x T

variable {U}

theorem parseU'_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x : List UInt8)
    (j : ℕ) (s : St) (ms : List (RMsg F)) (m : RMsg F) :
    ParseU' U H x T j s ms m ↔ ParseU' U H x T' j s ms m := by
  unfold ParseU'
  constructor
  · rintro ⟨h1, h2, h3, hx, hH, hi, hn⟩
    obtain ⟨e1, e2⟩ := chain_congr (T := T) (T' := T') _ _ fun z hz => h z (hH z hz)
    refine ⟨h1, h2, h3, hx.trans e2.symm, fun y hy => hH y (by rwa [e1] at hy),
      (injOn_congr h).mp hi, (noPre_congr h).mp hn⟩
  · rintro ⟨h1, h2, h3, hx, hH, hi, hn⟩
    obtain ⟨e1, e2⟩ := chain_congr (T := T') (T' := T) _ _ fun z hz => (h z (hH z hz)).symm
    refine ⟨h1, h2, h3, hx.trans e2.symm, fun y hy => hH y (by rwa [e1] at hy),
      (injOn_congr h).mpr hi, (noPre_congr h).mpr hn⟩

theorem ParseU'.length_eq {H : Hist} {x : List UInt8} {T : Table} {j : ℕ} {s : St}
    {ms : List (RMsg F)} {m : RMsg F} (h : ParseU' U H x T j s ms m) : ms.length = j := by
  rw [h.2.1.length_eq, List.length_take]
  exact min_eq_left (le_of_lt h.1)

/-- The chain before round `j`'s first input was asked. -/
theorem ParseU'.allIn_sub {H : Hist} {x : List UInt8} {T : Table} {j : ℕ} {s : St}
    {ms : List (RMsg F)} {m : RMsg F} (h : ParseU' U H x T j s ms m) :
    ∀ z ∈ allIn T (U.label s) (U.absorbsS s (U.K.rounds.take j) ms), z ∈ H := by
  intro z hz
  refine h.2.2.2.2.1 z ?_
  rw [prevIn_concat]
  exact hz

/-- **The parse is unique**, from both parses' `NoPre`. -/
theorem parseU_unique' {H : Hist} {x : List UInt8} {T : Table} {j j' : ℕ} {s s' : St}
    {ms ms' : List (RMsg F)} {m m' : RMsg F} (h : ParseU' U H x T j s ms m)
    (h' : ParseU' U H x T j' s' ms' m') : j = j' ∧ s = s' ∧ ms = ms' ∧ m = m' := by
  obtain ⟨hj, hf, hm, hx, hH, hi, hn⟩ := h
  obtain ⟨hj', hf', hm', hx', hH', -, hn'⟩ := h'
  obtain ⟨hlab, hes⟩ := chain_uniqueU' T hi _ _ _ _ hn hn' hH hH' (hx.symm.trans hx')
  have hl := congrArg List.length hes
  simp only [ChainSpecU.absorbsS, List.length_append, List.length_singleton,
    length_absorbsI] at hl
  have hjj : j = j' := nSteps_take_inj U.K.rounds j j' (le_of_lt hj) (le_of_lt hj') (by omega)
  subst hjj
  obtain ⟨ha, he⟩ := List.append_inj hes (by simp [ChainSpecU.absorbsS, length_absorbsI])
  simp only [List.cons.injEq, and_true] at he
  -- The statement: from the label and the bytes before round `0`'s message.
  have hpre : U.pre s = U.pre s' := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact (U.encAt_zero s s' m m' he).1
    · obtain ⟨r₀, rest, hr⟩ : ∃ r₀ rest, U.K.rounds.take j = r₀ :: rest := by
        rcases htk : U.K.rounds.take j with _ | ⟨r₀, rest⟩
        · rw [List.take_eq_nil_iff] at htk
          rcases htk with htk | htk
          · omega
          · rw [htk] at hj
            simp at hj
        · exact ⟨r₀, rest, rfl⟩
      rw [hr] at hf hf' ha
      rcases ms with _ | ⟨m₀, ms₀⟩
      · exact hf.elim
      rcases ms' with _ | ⟨m₀', ms₀'⟩
      · exact hf'.elim
      simp only [ChainSpecU.absorbsS, absorbsI, List.headD_cons, List.cons.injEq] at ha
      exact (U.encAt_zero s s' m₀ m₀' ha.1).1
  have hs : s = s' := U.stmt_inj s s' hlab hpre
  subst hs
  refine ⟨rfl, rfl, ?_, U.encAt_inj hm hm' he⟩
  exact absorbsI_inj (U.encAt s) (fun _ _ _ _ h1 h2 h3 => U.encAt_inj h1 h2 h3) hf hf' ha

variable (U)

/-- **`listBadU'` reads the table on the inputs asked, at the fresh input, and at the 32-byte
inputs** (the states its rounds' lookahead hashes). -/
theorem listBadU'_congr {H : Hist} {x : List UInt8} {T T' : Table} (hH : ∀ d ∈ H, T d = T' d)
    (hx : T x = T' x) (hs : ∀ v : Bytes32, T v.toList = T' v.toList) :
    listBadU' U C R H x T ↔ listBadU' U C R H x T' := by
  have hcoll : U.CollU H x T ↔ U.CollU H x T' := by
    unfold ChainSpecU.CollU
    rw [hx]
    constructor
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).symm.trans h⟩
      · exact Or.inr h
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).trans h⟩
      · exact Or.inr h
  have hsq : ∀ j, U.K.sqIns T' x j = U.K.sqIns T x j ∧
      (U.K.sqIns T' x j).map T' = (U.K.sqIns T x j).map T :=
    fun j => allIn_replicate_congr hs _ x hx
  have hround : ∀ T₁ T₂ : Table, (∀ d ∈ H, T₁ d = T₂ d) →
      (∀ j, U.K.sqIns T₂ x j = U.K.sqIns T₁ x j ∧
        (U.K.sqIns T₂ x j).map T₂ = (U.K.sqIns T₁ x j).map T₁) →
      RoundBadU' U C R H x T₁ → RoundBadU' U C R H x T₂ := by
    intro T₁ T₂ h12 hsq12 hb
    obtain ⟨j, s, ms, m, hp, h1, h2, cs, c, hcs, hc, h3, h4⟩ := hb
    have hch : U.chalsT T₂ s (U.K.rounds.take j) ms = U.chalsT T₁ s (U.K.rounds.take j) ms :=
      chalsTI_congr _ U.K.lim 0 _ _ _ fun z hz => h12 z (hp.allIn_sub z hz)
    refine ⟨j, s, ms, m, (parseU'_congr h12 x j s ms m).mp hp, by rw [(hsq12 j).1]; exact h1,
      by rw [(hsq12 j).1]; exact h2, cs, c, by rwa [← candLists_congr C h12], by
        rwa [← optC_congr (C j) h12], by rw [hch]; exact h3, ?_⟩
    rw [hch, (hsq12 j).2]
    exact h4
  unfold listBadU'
  rw [hcoll]
  exact or_congr_right ⟨hround T T' hH hsq, hround T' T
    (fun d hd => (hH d hd).symm) fun j => ⟨(hsq j).1.symm, (hsq j).2.symm⟩⟩

/-! ### Each fresh query is bad with small probability -/

variable [Fintype F] [DecidableEq F]

variable {S : Finset (List UInt8)}

/-- **A round is bad with probability at most its error times its factor** (`prob_roundBadU` on
`ParseU'`). -/
theorem prob_roundBadU' (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[RoundBadU' U C R (histOf c) t.1 (tableOf c g)] ≤
      maxErrK U.K C R := by
  classical
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  have hcg : ∀ g, ∀ d ∈ histOf c, tableOf c g d = tableOf c g₀ d := fun g _ hd =>
    tableOf_eq_of_mem c hd g g₀
  by_cases hp : ∃ j s ms m, ParseU' U (histOf c) t.1 (tableOf c g₀) j s ms m
  · obtain ⟨j, s, ms, m, hp⟩ := hp
    have hj : j < U.K.rounds.length := hp.1
    let T₀ := tableOf c g₀
    let chs := U.chalsT T₀ s (U.K.rounds.take j) ms
    let Ls := candLists C (histOf c) T₀ 0 ms
    let oc := optC (C j) (histOf c) T₀ m
    let E : List (Option M) → (↥S → Bytes32) → Prop := fun cs g => ∃ c' ∈ oc,
      (∀ y ∈ (allIn (tableOf c g) t.1 (List.replicate (U.K.spec j).ns [])).tail, y ∉ histOf c) ∧
      (allIn (tableOf c g) t.1 (List.replicate (U.K.spec j).ns [])).Nodup ∧
      (¬ R.pre s (opened cs ms chs) (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2)
        (((allIn (tableOf c g) t.1 (List.replicate (U.K.spec j).ns [])).map (tableOf c g)).map
          (chalL U.K.lim)))
    refine (prEvent_mono _ _ (fun g => ∃ cs, List.Forall₂ (· ∈ ·) cs Ls ∧ E cs g)
      fun g hg => ?_).trans ?_
    · obtain ⟨j', s', ms', m', hp', h1, h2, cs, c', hcs, hc', h3, h4⟩ := hg
      rw [parseU'_congr (hcg g)] at hp'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := parseU_unique' hp hp'
      have hch : U.chalsT (tableOf c g) s (U.K.rounds.take j) ms = chs :=
        chalsTI_congr _ U.K.lim 0 _ _ _ fun z hz => (hcg g z (hp.allIn_sub z hz)).symm
      rw [candLists_congr C (hcg g)] at hcs
      rw [optC_congr (C j) (hcg g)] at hc'
      rw [hch] at h3 h4
      exact ⟨cs, hcs, c', hc', h1, h2, h3, h4⟩
    · have hone : ∀ cs, List.Forall₂ (· ∈ ·) cs Ls → ∀ c' ∈ oc,
          Pr{let g ← $ᵗ (↥S → Bytes32)}[
            (∀ y ∈ (allIn (tableOf c g) t.1 (List.replicate (U.K.spec j).ns [])).tail,
              y ∉ histOf c) ∧
            (allIn (tableOf c g) t.1 (List.replicate (U.K.spec j).ns [])).Nodup ∧
            (¬ R.pre s (opened cs ms chs) (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2)
              (((allIn (tableOf c g) t.1 (List.replicate (U.K.spec j).ns [])).map
                (tableOf c g)).map (chalL U.K.lim)))] ≤ R.err j := by
        intro cs hcs c' _
        have hlen : (opened cs ms chs).length = j := by
          rw [length_opened cs ms chs (hcs.length_eq.trans (length_candLists C _ _ 0 ms)),
            hp.length_eq]
        refine (prEvent_round hS₀ c t ht (U.K.spec j).ns (fun l => ¬ R.pre s (opened cs ms chs)
          (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2) (l.map (chalL U.K.lim)))).trans ?_
        rw [prEvent_draws_chalL U.K.lim ((U.K.spec j).ns + 1) (fun l => ¬ R.pre s
          (opened cs ms chs) (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2) l)]
        exact R.sound j s _ _ hj hlen
      refine (prEvent_forall₂_le _ E ((oc.length : ℝ≥0∞) * R.err j) Ls fun cs hcs =>
        prEvent_exists_mem_le _ _ _ oc fun c' hc' => hone cs hcs c' hc').trans ?_
      have hf1 := prod_candLists_le C (histOf c) T₀ 0 _ ms hp.2.1
      have hf2 := length_optC_le (C j) (histOf c) T₀ hp.2.2.1
      have hfac : (Ls.map List.length).prod * oc.length ≤ facL C 0 (U.K.rounds.take (j + 1)) := by
        rw [facL_take_succ U.K C j hj]
        exact Nat.mul_le_mul hf1 hf2
      calc ((Ls.map List.length).prod : ℝ≥0∞) * ((oc.length : ℝ≥0∞) * R.err j)
          = (((Ls.map List.length).prod * oc.length : ℕ) : ℝ≥0∞) * R.err j := by
            push_cast
            ring
        _ ≤ (facL C 0 (U.K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j := by
            gcongr
        _ ≤ maxErrK U.K C R :=
            Finset.le_sup (f := fun j => (facL C 0 (U.K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j)
              (Finset.mem_range.mpr hj)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun g hg => ?_]
    · exact bot_le
    obtain ⟨j, s, ms, m, hp', -⟩ := hg
    exact hp ⟨j, s, ms, m, (parseU'_congr (hcg g) _ _ _ _ _).mp hp'⟩

/-- **A fresh query is bad with probability at most `(|H| + nRf (|H| + 1)) / 2^256 + maxErrK`**:
no tag term. -/
theorem prob_listBadU' (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[listBadU' U C R (histOf c) t.1 (tableOf c g)] ≤
      (((histOf c).card + U.nRf * ((histOf c).card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        maxErrK U.K C R :=
  (prEvent_or_le _ _ _).trans
    (add_le_add (prob_collU U c t ht) (prob_roundBadU' U C R hS₀ c t ht))

end Bad

/-! ## The trace: a winning run asks a bad fresh query -/

section Trace

variable {F St M : Type} [SampleableType F] (U : ChainSpecU F St) (C : ℕ → ListCommit M)
  (R : Piop U.K M)

variable {U C R} in
/-- No collision makes the order of the queries the order of what they refer to (`Rf`). -/
theorem rf_beforeU' {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBadU' U C R) T ∅ L) :
    ∀ y ∈ L, ∀ z ∈ L, U.Rf z (T y) → y ∈ before L z := by
  have nb : ∀ y ∈ L, ¬ listBadU' U C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadU' U C R) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy z hz h
  by_contra hb
  by_cases hyz : y = z
  · subst hyz
    exact nb y hy (Or.inl (Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩))
  · rcases before_trichotomy L y z hy hz hyz with h' | h'
    · exact hb h'
    · exact nb y hy (Or.inl (Or.inr ⟨z, Finset.mem_insert_of_mem h', h⟩))

variable {U C R} in
/-- No collision: the table is injective on the log. -/
theorem injOn_of_not_freshBadU' {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBadU' U C R) T ∅ L) : Set.InjOn T ↑L.toFinset := by
  have nb : ∀ y ∈ L, ¬ listBadU' U C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadU' U C R) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy w hw hyw
  have hy' := List.mem_toFinset.mp hy
  have hw' := List.mem_toFinset.mp hw
  by_contra hne
  rcases before_trichotomy L y w hy' hw' hne with h | h
  · exact nb w hw' (Or.inl (Or.inl ⟨y, h, hyw⟩))
  · exact nb y hy' (Or.inl (Or.inl ⟨w, h, hyw.symm⟩))

open Classical in
/-- **The trace, on a log**: if the log holds the chain's inputs, no answer of the log is the
label's first 32 bytes (`hseed`), and some candidates of the rounds' roots, read off the log, make
the transcript lost at the start and won at the end, then some fresh input of the log is bad. -/
theorem trace_coreU' (L : List (List UInt8)) (T : Table) (s : St) (ms : List (RMsg F))
    (cs : List (Option M)) (hfit : FitsAll U.K.rounds ms)
    (hmem : ∀ y ∈ allIn T (U.label s) (U.absorbsS s U.K.rounds ms), y ∈ L)
    (hcs : List.Forall₂ (· ∈ ·) cs (candLists C L.toFinset T 0 ms))
    (hwin : R.LostWon s (opened cs ms (U.chalsT T s U.K.rounds ms)))
    (hseed : ∀ z ∈ L, (T z).toList ≠ (U.label s).take 32) :
    FreshBad (listBadU' U C R) T ∅ L := by
  by_contra hnb
  have nb : ∀ y ∈ L, ¬ listBadU' U C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadU' U C R) T ∅ L hnb y hy (Finset.notMem_empty _)
  have hinj : ∀ y ∈ L, ∀ z ∈ L, T y = T z → y = z := by
    intro y hy z hz hyz
    by_contra hne
    rcases before_trichotomy L y z hy hz hne with h | h
    · exact nb z hz (Or.inl (Or.inl ⟨y, h, hyz⟩))
    · exact nb y hy (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))
  have hordF := rf_beforeU' hnb
  have hord : ∀ y ∈ L, ∀ z ∈ L, Refers z (T y) → y ∈ before L z :=
    fun y hy z hz h => hordF y hy z hz (U.refers_rf _ _ h)
  have injB : ∀ y, Set.InjOn T ↑(before L y) := fun y a ha b hb hab =>
    hinj a (mem_of_mem_before L a y ha) b (mem_of_mem_before L b y hb) hab
  have nopre : ∀ y, NoPre (U.label s) (before L y) T := fun y z hz =>
    hseed z (mem_of_mem_before L z y hz)
  -- After a root is absorbed, its candidates are the ones the history already fixed.
  have stab : ∀ {N : Type} (Cn : ListCommit N) (r : Bytes32) (y z : List UInt8), y ∈ L →
      U.Rf y r → (y = z ∨ y ∈ before L z) →
        Cn.cands L.toFinset T r = Cn.cands (before L z) T r := by
    intro N Cn r y z hy hry hyz
    have hsub : ∀ w, w ∈ before L y → w ∈ before L z := by
      rcases hyz with rfl | h
      · exact fun w hw => hw
      · exact fun w hw => before_subset_of_mem L y z h hw
    refine Cn.stable (before L z) L.toFinset T r (fun w hw => List.mem_toFinset.mpr
      (mem_of_mem_before L w z hw)) (fun w hw hwr => ?_) (fun y' hy' w hw h => ?_)
    · rw [← hwr] at hry
      exact hsub w (hordF w (List.mem_toFinset.mp hw) y hy hry)
    · exact before_subset_of_mem L y' z hy' (hord w (List.mem_toFinset.mp hw) y'
        (mem_of_mem_before L y' z hy') h)
  -- The round that turns the state from lost to won.
  obtain ⟨p, m', c', rest, hfull, hpre, hpost⟩ := R.exists_bad_of_lostWon s _ hwin
  obtain ⟨cs₀, c, cs₁, ms₀, m, ms₁, chs₀, ch, chs₁, ecs, ems, echs, l1, l2, l3, ep, em, ec⟩ :=
    opened_eq_append_cons p cs ms _ m' c' rest
      (by rw [ChainSpecU.chalsT, chalsTI, length_groupK, hfit.length_eq]) hfull
  rw [ems] at hfit
  obtain ⟨rs₀, s₁, rs₁, ers, hf0, hfm, hf1⟩ := fitsAll_split U.K.rounds ms₀ m ms₁ hfit
  have hl0 : ms₀.length = rs₀.length := hf0.length_eq
  have htake : U.K.rounds.take rs₀.length = rs₀ := by
    rw [ers]
    exact List.take_left' rfl
  have hspec : U.K.spec rs₀.length = s₁ := by
    rw [ChainSpec.spec, ers, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
    simp
  have hjlt : rs₀.length < U.K.rounds.length := by
    rw [ers]
    simp
  -- The round's first input and its squeezes.
  set lab := U.label s
  set e := U.encAt s
  set y₀ := lastIn T lab (absorbsI e 0 rs₀ ms₀)
  set x := stepIn (T y₀) (e rs₀.length m) with hx
  have hxl : x = lastIn T lab (absorbsI e 0 rs₀ ms₀ ++ [e rs₀.length m]) := by
    rw [lastIn_concat]
  -- The challenges split at the round.
  have hchs : U.chalsT T s U.K.rounds ms =
      chalsTI e U.K.lim 0 T lab rs₀ ms₀ ++
        (((allIn T x (List.replicate s₁.ns [])).map T).map (chalL U.K.lim) ::
          chalsTI e U.K.lim (rs₀.length + 1) T
            (lastIn T y₀ (absorbsI e rs₀.length [s₁] [m])) rs₁ ms₁) := by
    rw [ChainSpecU.chalsT, ers, ems,
      chalsTI_append e U.K.lim 0 T lab rs₀ (s₁ :: rs₁) ms₀ (m :: ms₁) hl0, chalsTI_cons,
      Nat.zero_add]
  rw [echs] at hchs
  have hl0' : chs₀.length = (chalsTI e U.K.lim 0 T lab rs₀ ms₀).length := by
    rw [l3, ← l2, hl0, chalsTI, length_groupK]
  obtain ⟨hc0, hc1⟩ := List.append_inj hchs hl0'
  simp only [List.cons.injEq] at hc1
  -- The chain's inputs, up to the round's first input and its squeezes.
  have hchain : allIn T lab (U.absorbsS s U.K.rounds ms) =
      prevIn T lab (absorbsI e 0 rs₀ ms₀ ++ [e rs₀.length m]) ++
        (allIn T x (List.replicate s₁.ns []) ++
          (allIn T (lastIn T x (List.replicate s₁.ns []))
            (absorbsI e (rs₀.length + 1) rs₁ ms₁)).tail) := by
    rw [ChainSpecU.absorbsS, ers, ems, absorbsI_append e 0 rs₀ (s₁ :: rs₁) ms₀ (m :: ms₁) hl0]
    rw [show absorbsI e (0 + rs₀.length) (s₁ :: rs₁) (m :: ms₁) =
      [e rs₀.length m] ++ (List.replicate s₁.ns [] ++ absorbsI e (rs₀.length + 1) rs₁ ms₁) by
        simp [absorbsI]]
    rw [← List.append_assoc, allIn_append, ← hxl, allIn_append']
  have hpw := chain_pairwise hord _ _ hmem
  rw [hchain, List.pairwise_append, List.pairwise_append] at hpw
  obtain ⟨-, ⟨hsq, -, -⟩, hcross⟩ := hpw
  have hxmem : x ∈ L := hmem x (by rw [hchain]; simp [head_mem_allIn])
  -- The chain before `x` was asked before it.
  have hprev : ∀ z ∈ prevIn T lab (absorbsI e 0 rs₀ ms₀ ++ [e rs₀.length m]), z ∈ before L x :=
    fun z hz => hcross z hz x (List.mem_append_left _ (head_mem_allIn _ _ _))
  -- The round's squeezes after `x` are fresh, and distinct.
  rw [allIn_cons_tail, List.pairwise_cons] at hsq
  have hfresh : ∀ z ∈ (allIn T x (List.replicate s₁.ns [])).tail, z ∉ before L x :=
    fun z hz => not_mem_before_of_mem_before (hsq.1 z hz)
  have hnodup : (allIn T x (List.replicate s₁.ns [])).Nodup := by
    rw [allIn_cons_tail]
    refine List.nodup_cons.mpr ⟨fun hx' => not_mem_before_self L x (hsq.1 x hx'), ?_⟩
    exact hsq.2.imp fun {a b} (h : a ∈ before L b) (e : a = b) =>
      not_mem_before_self L b (e ▸ h)
  -- The candidates of the rounds up to `j`, read off the history before `x`.
  have hroots : ∀ m₂ ∈ ms₀ ++ [m], ∀ r, m₂.1 = some r → ∀ k,
      (C k).cands L.toFinset T r = (C k).cands (before L x) T r := by
    intro m₂ hm₂ r hr k
    obtain ⟨i, hi, hmi⟩ := List.mem_iff_getElem.mp hm₂
    have he : e i m₂ ∈ absorbsI e 0 rs₀ ms₀ ++ [e rs₀.length m] := by
      rcases Nat.lt_or_ge i ms₀.length with hi0 | hi0
      · have h0 := getElem_mem_absorbsI e 0 rs₀ ms₀ hl0 i hi0
        rw [List.getElem_append_left hi0] at hmi
        rw [Nat.zero_add, hmi] at h0
        exact List.mem_append_left _ h0
      · have hi' : i = ms₀.length := by
          simp only [List.length_append, List.length_singleton] at hi
          omega
        subst hi'
        have hm₂m : m₂ = m := by
          rw [← hmi]
          simp
        rw [hm₂m, hl0]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    obtain ⟨st, hst⟩ := step_mem_allIn T lab _ _ he
    obtain ⟨o, l'⟩ := m₂
    simp only at hr
    subst hr
    rw [allIn_eq, ← hxl] at hst
    have hy : stepIn st (e i (some r, l')) ∈ L := by
      rcases List.mem_append.mp hst with h | h
      · exact mem_of_mem_before L _ x (hprev _ h)
      · rw [List.mem_singleton.mp h]
        exact hxmem
    have hrf : U.Rf (stepIn st (e i (some r, l'))) r := by
      show U.Rf (stepIn st (U.encAt s i (some r, l'))) r
      unfold ChainSpecU.encAt
      split_ifs
      · exact U.rf_pre s st r l'
      · exact U.rf_enc st r l'
    refine stab (C k) r _ x hy hrf ?_
    rcases List.mem_append.mp hst with h | h
    · exact Or.inr (hprev _ h)
    · exact Or.inl (List.mem_singleton.mp h)
  rw [ecs, ems, candLists_append] at hcs
  have hlc : cs₀.length = (candLists C L.toFinset T 0 ms₀).length := by
    rw [length_candLists, l1, l2]
  obtain ⟨hcs0, hcs1⟩ := forall₂_append_split hlc hcs
  simp only [candLists, Nat.zero_add] at hcs1
  have hc : c ∈ optC (C ms₀.length) L.toFinset T m := by
    cases hcs1 with
    | cons h _ => exact h
  rw [candLists_stable C 0 ms₀ fun m₂ hm₂ => hroots m₂ (List.mem_append_left _ hm₂)] at hcs0
  rw [optC_stable (C ms₀.length) m fun r hr => hroots m (by simp) r hr _] at hc
  -- The bad round.
  refine nb x hxmem (Or.inr ⟨rs₀.length, s, ms₀, m, ⟨hjlt, by rw [htake]; exact hf0,
    by rw [hspec]; exact hfm, by rw [ChainSpecU.absorbsS, htake]; exact hxl, fun z hz => by
      rw [ChainSpecU.absorbsS, htake] at hz
      exact hprev z hz, injB x, nopre x⟩, ?_, ?_, cs₀, c, hcs0, ?_, ?_, ?_⟩)
  · rw [ChainSpec.sqIns, hspec]
    exact hfresh
  · rw [ChainSpec.sqIns, hspec]
    exact hnodup
  · rwa [hl0] at hc
  · rw [ChainSpecU.chalsT, htake, ← hc0, ← ep, ← em]
    exact hpre
  · rw [ChainSpecU.chalsT, htake, ← hc0, ← ep, ← em, ChainSpec.sqIns, hspec, ← hc1.1, ← ec]
    exact hpost

end Trace

end Compose

/-- info: 'Compose.prob_listBadU'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prob_listBadU'

/-- info: 'Compose.trace_coreU'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_coreU'
