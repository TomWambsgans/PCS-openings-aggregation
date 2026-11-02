-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Generalises `formal/Compose/Compose/ListChainK.lean` of this repository (its chain, parse, bad
-- events, union bound and trace, whose structure follows `formal/QuotientRpm/ChainRom.lean`) to a
-- chain whose messages are hashed by any injective encoding; the lemmas of `ListChainK.lean` that
-- do not read the encoding (the chain on a table, the paths, the protocol, the candidates) are
-- reused as they are.
import Compose.ListChainKDoom

/-!
# The list chain over any encoding

`ListChainK.lean`'s chain is `crates/quotient/src/transcript.rs`'s: every scalar a 32-byte word,
a root two such words, the label of a length `≢ 0 mod 32`, so that a step's input (the state and
whole words) is never a label (`chain_unique`). The univariate verifier's chain
(`crates/leanvm_flock_gas/src/transcript.rs`, `KeccakChannel`) is not of that form: a scalar is 24
bytes, a root its digest's two 16-byte halves each reversed, the seed `name ‖ iv ‖ input` (80
bytes, the length of a step absorbing two scalars), and the first round's message follows the
statement's row counts. Here the chain is any chain whose messages are hashed by an encoding
(`ChainSpecU`):

* `enc`, injective on the messages of a round (`enc_inj`); the first round's message after the
  statement's bytes `pre s` (of one length, `pre_len`; `encAt`); the label and `pre` together
  determine the statement (`stmt_inj`);
* **every label starts with a tag** (`label_tag`; the univariate `name`): a label is a step's input
  only if a state starts with the tag. A fresh answer starting with the tag is a bad event
  (`TagBad`, probability `256^(32 − |tag|) / 2^256`, `tagBound`), and the parse asks that no answer
  of the history start with it (`NoTag`): then the walk back from an input stops at the label
  only (`chain_uniqueU`), with no length argument;
* **what an input refers to** (`Rf`, at most `nRf` digests an input, `refs`) contains `Refers` (a
  Merkle node's children, `ListCommit.stable`'s reading) and the roots as `enc` writes them after
  a state (`rf_enc`, `rf_pre`): a collision (`CollU`) is a fresh answer repeating one, or one an
  input asked before refers to.

The protocol (`Piop`), the candidates (`candLists`), the union bound's factor (`maxErrK`) are
`ListChainK.lean`'s, on the rounds of `U.K` (a `ChainSpec` whose label and encoding are not read).
**`prob_listBadU`**: each fresh query is bad with probability at most
`(|H| + nRf (|H| + 1)) / 2^256 + tagBound + maxErrK`; **`trace_coreU`**: a run lost at the start
and won at the end asks a bad fresh query.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm

/-! ## Round-indexed encodings -/

section Enc

variable {F : Type}

/-- **The bytes each step absorbs**, a round's first step its message as `e` encodes it at the
round's index (from `i`), its other steps nothing. -/
def absorbsI (e : ℕ → RMsg F → List UInt8) : ℕ → List RoundSpec → List (RMsg F) →
    List (List UInt8)
  | _, [], _ => []
  | i, s :: rs, ms => e i (ms.headD (none, [])) ::
      (List.replicate s.ns [] ++ absorbsI e (i + 1) rs ms.tail)

variable (e : ℕ → RMsg F → List UInt8)

theorem length_absorbsI : ∀ (i : ℕ) (rs : List RoundSpec) (ms : List (RMsg F)),
    (absorbsI e i rs ms).length = nSteps rs
  | _, [], _ => rfl
  | i, s :: rs, ms => by
    simp only [absorbsI, nSteps, List.length_cons, List.length_append, List.length_replicate,
      length_absorbsI (i + 1) rs ms.tail]
    omega

theorem absorbsI_append : ∀ (i : ℕ) (rs₁ rs₂ : List RoundSpec) (ms₁ ms₂ : List (RMsg F)),
    ms₁.length = rs₁.length →
      absorbsI e i (rs₁ ++ rs₂) (ms₁ ++ ms₂) =
        absorbsI e i rs₁ ms₁ ++ absorbsI e (i + rs₁.length) rs₂ ms₂
  | i, [], _, [], _, _ => by simp [absorbsI]
  | i, s :: rs₁, rs₂, m :: ms₁, ms₂, h => by
    simp only [List.cons_append, absorbsI, List.headD_cons, List.tail_cons, List.append_assoc,
      absorbsI_append (i + 1) rs₁ rs₂ ms₁ ms₂ (by simpa using h), List.length_cons]
    rw [show i + 1 + rs₁.length = i + (rs₁.length + 1) by omega]
  | _, [], _, _ :: _, _, h => by simp at h
  | _, _ :: _, _, [], _, h => by simp at h

theorem absorbsI_single (i : ℕ) (s : RoundSpec) (m : RMsg F) :
    absorbsI e i [s] [m] = e i m :: List.replicate s.ns [] := by
  simp [absorbsI]

/-- **The messages are determined by the bytes the steps absorb**, given the rounds, for an
encoding injective on each round's messages. -/
theorem absorbsI_inj
    (he : ∀ j {sp : RoundSpec} {m m' : RMsg F}, m.Fits sp → m'.Fits sp → e j m = e j m' → m = m') :
    ∀ {i : ℕ} {rs : List RoundSpec} {ms ms' : List (RMsg F)}, FitsAll rs ms → FitsAll rs ms' →
      absorbsI e i rs ms = absorbsI e i rs ms' → ms = ms'
  | _, [], [], [], _, _, _ => rfl
  | i, s :: rs, m :: ms, m' :: ms', h, h', hq => by
    simp only [absorbsI, List.headD_cons, List.tail_cons, List.cons.injEq] at hq
    obtain ⟨h1, h2⟩ := hq
    rw [he i h.1 h'.1 h1, absorbsI_inj he h.2 h'.2 (List.append_cancel_left h2)]
  | _, [], _ :: _, _, h, _, _ => h.elim
  | _, [], [], _ :: _, _, h', _ => h'.elim
  | _, _ :: _, [], _, h, _, _ => h.elim
  | _, _ :: _, _ :: _, [], _, h', _ => h'.elim

/-- A round's message, at its index, is among the bytes the steps absorb. -/
theorem getElem_mem_absorbsI : ∀ (i₀ : ℕ) (rs : List RoundSpec) (ms : List (RMsg F)),
    ms.length = rs.length → ∀ i (h : i < ms.length), e (i₀ + i) ms[i] ∈ absorbsI e i₀ rs ms
  | _, [], [], _, i, h => by simp at h
  | i₀, s :: rs, m :: ms, _, 0, _ => by simp [absorbsI]
  | i₀, s :: rs, m :: ms, hl, i + 1, h => by
    simp only [absorbsI, List.headD_cons, List.tail_cons, List.getElem_cons_succ, List.mem_cons,
      List.mem_append]
    refine Or.inr (Or.inr ?_)
    have := getElem_mem_absorbsI (i₀ + 1) rs ms (by simpa using hl) i (by simpa using h)
    rwa [show i₀ + 1 + i = i₀ + (i + 1) by omega] at this
  | _, [], _ :: _, hl, _, _ => by simp at hl
  | _, _ :: _, [], hl, _, _ => by simp at hl

/-- **The challenges of a chain on a table**, one list per round, the messages encoded by `e`
from round `i`: the states after each step, read as field elements. -/
def chalsTI (lim : F ≃ Limbs) (i : ℕ) (T : Table) (y : List UInt8) (rs : List RoundSpec)
    (ms : List (RMsg F)) : List (List F) :=
  groupK rs (((allIn T y (absorbsI e i rs ms)).tail.map T).map (chalL lim))

theorem chalsTI_append (lim : F ≃ Limbs) (i : ℕ) (T : Table) (y : List UInt8)
    (rs₀ rs₂ : List RoundSpec) (ms₀ ms₂ : List (RMsg F)) (h : ms₀.length = rs₀.length) :
    chalsTI e lim i T y (rs₀ ++ rs₂) (ms₀ ++ ms₂) =
      chalsTI e lim i T y rs₀ ms₀ ++
        chalsTI e lim (i + rs₀.length) T (lastIn T y (absorbsI e i rs₀ ms₀)) rs₂ ms₂ := by
  unfold chalsTI
  rw [absorbsI_append e i rs₀ rs₂ ms₀ ms₂ h, tail_allIn_append, List.map_append,
    List.map_append, groupK_append]
  rw [List.length_map, List.length_map, length_tail_allIn, length_absorbsI]

theorem chalsTI_single (lim : F ≃ Limbs) (i : ℕ) (T : Table) (y : List UInt8) (s : RoundSpec)
    (m : RMsg F) : chalsTI e lim i T y [s] [m] =
      [((allIn T (stepIn (T y) (e i m)) (List.replicate s.ns [])).map T).map (chalL lim)] := by
  unfold chalsTI
  rw [absorbsI_single]
  simp only [allIn, List.tail_cons]
  exact groupK_single s _ (by simp [length_allIn_replicate])

theorem chalsTI_cons (lim : F ≃ Limbs) (i : ℕ) (T : Table) (y : List UInt8) (s : RoundSpec)
    (rs : List RoundSpec) (m : RMsg F) (ms : List (RMsg F)) :
    chalsTI e lim i T y (s :: rs) (m :: ms) =
      ((allIn T (stepIn (T y) (e i m)) (List.replicate s.ns [])).map T).map (chalL lim) ::
        chalsTI e lim (i + 1) T (lastIn T y (absorbsI e i [s] [m])) rs ms := by
  have h := chalsTI_append e lim i T y [s] rs [m] ms rfl
  simp only [List.singleton_append] at h
  rw [h, chalsTI_single]
  rfl

theorem chalsTI_congr {T T' : Table} (lim : F ≃ Limbs) (i : ℕ) (y : List UInt8)
    (rs : List RoundSpec) (ms : List (RMsg F))
    (h : ∀ z ∈ allIn T y (absorbsI e i rs ms), T z = T' z) :
    chalsTI e lim i T' y rs ms = chalsTI e lim i T y rs ms := by
  obtain ⟨e1, e2⟩ := allIn_congr y _ h
  have e3 : (allIn T' y (absorbsI e i rs ms)).tail.map T' =
      (allIn T y (absorbsI e i rs ms)).tail.map T := by
    rw [e1]
    exact List.map_congr_left fun z hz => (h z (List.mem_of_mem_tail hz)).symm
  unfold chalsTI
  rw [e3]

end Enc

/-! ## The walk back, separated by a tag -/

section Walk

/-- **No answer of the history starts with the tag.** -/
def NoTag (tag : List UInt8) (H : Hist) (T : Table) : Prop :=
  ∀ z ∈ H, (T z).toList.take tag.length ≠ tag

theorem take_stepIn_le (st : Bytes32) (e : List UInt8) {k : ℕ} (hk : k ≤ 32) :
    (stepIn st e).take k = st.toList.take k := by
  show (st.toList ++ e).take k = st.toList.take k
  exact List.take_append_of_le_length (by simpa using hk)

theorem NoTag.mono {tag : List UInt8} {H H' : Hist} {T : Table} (h : NoTag tag H' T)
    (hs : ∀ z ∈ H, z ∈ H') : NoTag tag H T := fun z hz => h z (hs z hz)

theorem noTag_congr {tag : List UInt8} {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) :
    NoTag tag H T ↔ NoTag tag H T' := by
  unfold NoTag
  constructor
  · intro hn z hz
    rw [← h z hz]
    exact hn z hz
  · intro hn z hz
    rw [h z hz]
    exact hn z hz

/-- **The chain before an input is determined by the input**, through injective answers, when the
labels start with a tag no answer of the history starts with: a step's input (a state, then
bytes) is then never a label. -/
theorem chain_uniqueU (T : Table) {H : Hist} {tag : List UInt8} (htag : tag.length ≤ 32)
    (hi : Set.InjOn T ↑H) (hn : NoTag tag H T) :
    ∀ (es es' : List (List UInt8)) (y y' : List UInt8),
      y.take tag.length = tag → y'.take tag.length = tag →
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
      have ht := congrArg (List.take tag.length) h
      rw [take_stepIn_le _ _ htag] at ht
      exact hn _ hz (ht.symm.trans hy)
  | append_singleton es₀ e ih =>
    intro es' y y' hy hy' hH hH' h
    rcases List.eq_nil_or_concat es' with rfl | ⟨L, b, rfl⟩
    · exfalso
      rw [lastIn_concat] at h
      have hz : lastIn T y es₀ ∈ H := hH _ (by
        rw [prevIn_concat, allIn_eq]
        simp)
      have ht := congrArg (List.take tag.length) h
      rw [take_stepIn_le _ _ htag] at ht
      exact hn _ hz (ht.trans hy')
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

/-! ## The chain's specification -/

/-- **A chain over an encoding**: the rounds and the limbs (`K`, a `ChainSpec` whose label is not
the chain's), the label of a statement (every label starting with `tag`), the statement's bytes
before round `0`'s message (`pre`), the messages' encoding (`enc`), and what an input refers to
(`Rf`: `Refers`, and the roots as `enc` writes them after a state, at most `nRf` digests an
input). -/
structure ChainSpecU (F St : Type) where
  K : ChainSpec F St
  label : St → List UInt8
  tag : List UInt8
  tag_le : tag.length ≤ 32
  label_tag : ∀ s, (label s).take tag.length = tag
  pre : St → List UInt8
  pre_len : ∀ s s', (pre s).length = (pre s').length
  stmt_inj : ∀ s s', label s = label s' → pre s = pre s' → s = s'
  enc : RMsg F → List UInt8
  enc_inj : ∀ {sp : RoundSpec} {m m' : RMsg F}, m.Fits sp → m'.Fits sp → enc m = enc m' → m = m'
  Rf : List UInt8 → Bytes32 → Prop
  nRf : ℕ
  refs : List UInt8 → List Bytes32
  rf_refs : ∀ y d, Rf y d → d ∈ refs y
  length_refs : ∀ y, (refs y).length ≤ nRf
  refers_rf : ∀ y d, Refers y d → Rf y d
  rf_enc : ∀ (st r : Bytes32) (l : List F), Rf (stepIn st (enc (some r, l))) r
  rf_pre : ∀ (s : St) (st r : Bytes32) (l : List F), Rf (stepIn st (pre s ++ enc (some r, l))) r

namespace ChainSpecU

variable {F St : Type} (U : ChainSpecU F St)

/-- Round `j`'s message as the chain hashes it: round `0`'s after the statement's bytes. -/
def encAt (s : St) (j : ℕ) (m : RMsg F) : List UInt8 :=
  if j = 0 then U.pre s ++ U.enc m else U.enc m

/-- The bytes the steps of the rounds `rs` absorb, for the statement `s`. -/
def absorbsS (s : St) (rs : List RoundSpec) (ms : List (RMsg F)) : List (List UInt8) :=
  absorbsI (U.encAt s) 0 rs ms

/-- The challenges of the chain of the statement `s` on a table, over the rounds `rs`. -/
def chalsT (T : Table) (s : St) (rs : List RoundSpec) (ms : List (RMsg F)) : List (List F) :=
  chalsTI (U.encAt s) U.K.lim 0 T (U.label s) rs ms

/-- **The chain** of a statement and its messages, over a hash `H`. -/
def chain {m : Type → Type} [Monad m] (H : List UInt8 → m Bytes32) (s : St)
    (ms : List (RMsg F)) : m (List (List F)) :=
  U.K.chalsOf <$> runM H (U.label s) (U.absorbsS s U.K.rounds ms)

/-- **A fresh answer starts with the tag.** -/
def TagBad (x : List UInt8) (T : Table) : Prop := (T x).toList.take U.tag.length = U.tag

/-- **A collision**: the fresh answer repeats an earlier one, or an input asked before, or `x`,
refers to it. -/
def CollU (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  (∃ y ∈ H, T y = T x) ∨ ∃ y ∈ insert x H, U.Rf y (T x)

/-- The probability of a tag: `256^(32 − |tag|) / 2^256`. -/
noncomputable def tagBound : ℝ≥0∞ := ((256 ^ (32 - U.tag.length) : ℕ) : ℝ≥0∞) / 2 ^ 256

theorem encAt_inj {s : St} {j : ℕ} {sp : RoundSpec} {m m' : RMsg F} (h : m.Fits sp)
    (h' : m'.Fits sp) (he : U.encAt s j m = U.encAt s j m') : m = m' := by
  unfold encAt at he
  split_ifs at he
  · exact U.enc_inj h h' (List.append_cancel_left he)
  · exact U.enc_inj h h' he

theorem encAt_zero (s s' : St) (m m' : RMsg F) (he : U.encAt s 0 m = U.encAt s' 0 m') :
    U.pre s = U.pre s' ∧ U.enc m = U.enc m' := by
  simp only [encAt, ite_true] at he
  exact List.append_inj he (U.pre_len s s')

end ChainSpecU

/-! ## The bad events -/

section Bad

variable {F St M : Type} [SampleableType F] (U : ChainSpecU F St) (C : ℕ → ListCommit M)
  (R : Piop U.K M)

/-- **`x` is round `j`'s first input**: for a statement `s`, the messages `ms` of the rounds before
and `m` of round `j`, fitting them, the chain before `x` was asked (its inputs in `H`), without
collision, and no answer of the history starts with the tag. -/
def ParseU (H : Hist) (x : List UInt8) (T : Table) (j : ℕ) (s : St) (ms : List (RMsg F))
    (m : RMsg F) : Prop :=
  j < U.K.rounds.length ∧ FitsAll (U.K.rounds.take j) ms ∧ m.Fits (U.K.spec j) ∧
    x = lastIn T (U.label s) (U.absorbsS s (U.K.rounds.take j) ms ++ [U.encAt s j m]) ∧
    (∀ y ∈ prevIn T (U.label s) (U.absorbsS s (U.K.rounds.take j) ms ++ [U.encAt s j m]),
      y ∈ H) ∧
    Set.InjOn T ↑H ∧ NoTag U.tag H T

/-- **Round `j` is bad at its first input**: the inputs after it fresh and distinct, and its
challenges turn the state from lost to won for some candidates of the roots of the rounds up to
`j`, read off the history. -/
def RoundBadU (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ j s ms m, ParseU U H x T j s ms m ∧
    (∀ y ∈ (U.K.sqIns T x j).tail, y ∉ H) ∧ (U.K.sqIns T x j).Nodup ∧
    ∃ cs c, List.Forall₂ (· ∈ ·) cs (candLists C H T 0 ms) ∧ c ∈ optC (C j) H T m ∧
      ¬ R.pre s (opened cs ms (U.chalsT T s (U.K.rounds.take j) ms)) (c, m.2) ∧
      R.post s (opened cs ms (U.chalsT T s (U.K.rounds.take j) ms)) (c, m.2)
        (((U.K.sqIns T x j).map T).map (chalL U.K.lim))

/-- **A bad fresh query**: a collision, a tag, or a bad round. -/
def listBadU (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  U.CollU H x T ∨ U.TagBad x T ∨ RoundBadU U C R H x T

variable {U}

theorem parseU_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x : List UInt8)
    (j : ℕ) (s : St) (ms : List (RMsg F)) (m : RMsg F) :
    ParseU U H x T j s ms m ↔ ParseU U H x T' j s ms m := by
  unfold ParseU
  constructor
  · rintro ⟨h1, h2, h3, hx, hH, hi, hn⟩
    obtain ⟨e1, e2⟩ := chain_congr (T := T) (T' := T') _ _ fun z hz => h z (hH z hz)
    refine ⟨h1, h2, h3, hx.trans e2.symm, fun y hy => hH y (by rwa [e1] at hy),
      (injOn_congr h).mp hi, (noTag_congr h).mp hn⟩
  · rintro ⟨h1, h2, h3, hx, hH, hi, hn⟩
    obtain ⟨e1, e2⟩ := chain_congr (T := T') (T' := T) _ _ fun z hz => (h z (hH z hz)).symm
    refine ⟨h1, h2, h3, hx.trans e2.symm, fun y hy => hH y (by rwa [e1] at hy),
      (injOn_congr h).mpr hi, (noTag_congr h).mpr hn⟩

theorem ParseU.length_eq {H : Hist} {x : List UInt8} {T : Table} {j : ℕ} {s : St}
    {ms : List (RMsg F)} {m : RMsg F} (h : ParseU U H x T j s ms m) : ms.length = j := by
  rw [h.2.1.length_eq, List.length_take]
  exact min_eq_left (le_of_lt h.1)

/-- The chain before round `j`'s first input was asked. -/
theorem ParseU.allIn_sub {H : Hist} {x : List UInt8} {T : Table} {j : ℕ} {s : St}
    {ms : List (RMsg F)} {m : RMsg F} (h : ParseU U H x T j s ms m) :
    ∀ z ∈ allIn T (U.label s) (U.absorbsS s (U.K.rounds.take j) ms), z ∈ H := by
  intro z hz
  refine h.2.2.2.2.1 z ?_
  rw [prevIn_concat]
  exact hz

/-- **The parse is unique.** -/
theorem parseU_unique {H : Hist} {x : List UInt8} {T : Table} {j j' : ℕ} {s s' : St}
    {ms ms' : List (RMsg F)} {m m' : RMsg F} (h : ParseU U H x T j s ms m)
    (h' : ParseU U H x T j' s' ms' m') : j = j' ∧ s = s' ∧ ms = ms' ∧ m = m' := by
  obtain ⟨hj, hf, hm, hx, hH, hi, hn⟩ := h
  obtain ⟨hj', hf', hm', hx', hH', -, -⟩ := h'
  obtain ⟨hlab, hes⟩ := chain_uniqueU T U.tag_le hi hn _ _ _ _ (U.label_tag s) (U.label_tag s')
    hH hH' (hx.symm.trans hx')
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

/-- **`listBadU` reads the table on the inputs asked, at the fresh input, and at the 32-byte
inputs** (the states its rounds' lookahead hashes). -/
theorem listBadU_congr {H : Hist} {x : List UInt8} {T T' : Table} (hH : ∀ d ∈ H, T d = T' d)
    (hx : T x = T' x) (hs : ∀ v : Bytes32, T v.toList = T' v.toList) :
    listBadU U C R H x T ↔ listBadU U C R H x T' := by
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
  have htag : U.TagBad x T ↔ U.TagBad x T' := by
    unfold ChainSpecU.TagBad
    rw [hx]
  have hsq : ∀ j, U.K.sqIns T' x j = U.K.sqIns T x j ∧
      (U.K.sqIns T' x j).map T' = (U.K.sqIns T x j).map T :=
    fun j => allIn_replicate_congr hs _ x hx
  have hround : ∀ T₁ T₂ : Table, (∀ d ∈ H, T₁ d = T₂ d) →
      (∀ j, U.K.sqIns T₂ x j = U.K.sqIns T₁ x j ∧
        (U.K.sqIns T₂ x j).map T₂ = (U.K.sqIns T₁ x j).map T₁) →
      RoundBadU U C R H x T₁ → RoundBadU U C R H x T₂ := by
    intro T₁ T₂ h12 hsq12 hb
    obtain ⟨j, s, ms, m, hp, h1, h2, cs, c, hcs, hc, h3, h4⟩ := hb
    have hch : U.chalsT T₂ s (U.K.rounds.take j) ms = U.chalsT T₁ s (U.K.rounds.take j) ms :=
      chalsTI_congr _ U.K.lim 0 _ _ _ fun z hz => h12 z (hp.allIn_sub z hz)
    refine ⟨j, s, ms, m, (parseU_congr h12 x j s ms m).mp hp, by rw [(hsq12 j).1]; exact h1,
      by rw [(hsq12 j).1]; exact h2, cs, c, by rwa [← candLists_congr C h12], by
        rwa [← optC_congr (C j) h12], by rw [hch]; exact h3, ?_⟩
    rw [hch, (hsq12 j).2]
    exact h4
  unfold listBadU
  rw [hcoll, htag]
  exact or_congr_right (or_congr_right ⟨hround T T' hH hsq, hround T' T
    (fun d hd => (hH d hd).symm) fun j => ⟨(hsq j).1.symm, (hsq j).2.symm⟩⟩)

/-! ### Each fresh query is bad with small probability -/

variable [Fintype F] [DecidableEq F]

variable {S : Finset (List UInt8)}

/-- **A collision has probability at most `(|H| + nRf (|H| + 1)) / 2^256`.** -/
theorem prob_collU (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[U.CollU (histOf c) t.1 (tableOf c g)] ≤
      (((histOf c).card + U.nRf * ((histOf c).card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  let Bad : Finset Bytes32 := (histOf c).image (tableOf c g₀) ∪
    (insert t.1 (histOf c)).biUnion fun y => (U.refs y).toFinset
  refine (prEvent_mono _ _ (fun g => g t ∈ Bad) fun g h => ?_).trans ?_
  · rw [← tableOf_fresh c ht g]
    rcases h with ⟨y, hy, hyx⟩ | ⟨y, hy, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨y, hy, by rw [tableOf_eq_of_mem c hy g₀ g, hyx]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨y, hy, List.mem_toFinset.mpr (U.rf_refs y _ h)⟩)
  · refine (prEvent_cell t (fun u => u ∈ Bad)).trans ?_
    rw [SampleableType.prEvent_uniformSample, card_bytes32]
    have hc : Bad.card ≤ (histOf c).card + U.nRf * ((histOf c).card + 1) := by
      refine (Finset.card_union_le _ _).trans ?_
      have h2 := Finset.card_biUnion_le (s := insert t.1 (histOf c))
        (t := fun y => (U.refs y).toFinset)
      have h3 : ∑ y ∈ insert t.1 (histOf c), (U.refs y).toFinset.card ≤
          (insert t.1 (histOf c)).card * U.nRf := by
        simpa using Finset.sum_le_card_nsmul _ _ U.nRf fun y _ =>
          (List.toFinset_card_le _).trans (U.length_refs y)
      have h4 := Finset.card_insert_le t.1 (histOf c)
      have h5 := Finset.card_image_le (s := histOf c) (f := tableOf c g₀)
      have h6 : (insert t.1 (histOf c)).card * U.nRf ≤ ((histOf c).card + 1) * U.nRf :=
        Nat.mul_le_mul_right _ h4
      nlinarith
    have : ((Finset.univ.filter fun u : Bytes32 => u ∈ Bad).card : ℝ≥0∞) ≤
        (((histOf c).card + U.nRf * ((histOf c).card + 1) : ℕ) : ℝ≥0∞) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact_mod_cast hc
    rw [Nat.cast_pow, Nat.cast_ofNat]
    gcongr

-- The linter runs out of recursion depth on this proof.
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- The 32-byte strings that start with a tag: at most `256^(32 − |tag|)`. -/
theorem card_tag_le (tag : List UInt8) :
    (Finset.univ.filter fun d : Bytes32 => d.toList.take tag.length = tag).card ≤
      256 ^ (32 - tag.length) := by
  let f : Bytes32 → Vector UInt8 (32 - tag.length) := fun d =>
    ⟨(d.toList.drop tag.length).toArray, by simp⟩
  have hinj : Set.InjOn f ↑(Finset.univ.filter fun d : Bytes32 =>
      d.toList.take tag.length = tag) := by
    intro a ha b hb hab
    have ha : a.toList.take tag.length = tag := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb : b.toList.take tag.length = tag := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    have hd : a.toList.drop tag.length = b.toList.drop tag.length := by
      have := congrArg (fun v : Vector UInt8 (32 - tag.length) => v.toList) hab
      simpa [f] using this
    apply Vector.toList_inj.mp
    rw [← List.take_append_drop tag.length a.toList, ← List.take_append_drop tag.length b.toList,
      ha, hb, hd]
  calc _ ≤ (Finset.univ : Finset (Vector UInt8 (32 - tag.length))).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
    _ = 256 ^ (32 - tag.length) := by rw [Finset.card_univ, Common.card_vector_uInt8]

/-- **A fresh answer starts with the tag with probability at most `tagBound`.** -/
theorem prob_tagBad (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[U.TagBad t.1 (tableOf c g)] ≤ U.tagBound := by
  let Bad : Finset Bytes32 := Finset.univ.filter fun d : Bytes32 =>
    d.toList.take U.tag.length = U.tag
  refine (prEvent_mono _ _ (fun g => g t ∈ Bad) fun g h => ?_).trans ?_
  · simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← tableOf_fresh c ht g]
    exact h
  · refine (prEvent_cell t (fun u => u ∈ Bad)).trans ?_
    rw [SampleableType.prEvent_uniformSample, card_bytes32]
    have : ((Finset.univ.filter fun u : Bytes32 => u ∈ Bad).card : ℝ≥0∞) ≤
        ((256 ^ (32 - U.tag.length) : ℕ) : ℝ≥0∞) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact_mod_cast card_tag_le U.tag
    unfold ChainSpecU.tagBound
    rw [Nat.cast_pow (2 : ℕ) 256, Nat.cast_ofNat]
    gcongr

/-- **A round is bad with probability at most its error times its factor**: the parse is read off
the history, so at most one round and one parse are possible, the candidates and the challenges
before are fixed by the history, and the round's challenges are uniform. -/
theorem prob_roundBadU (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[RoundBadU U C R (histOf c) t.1 (tableOf c g)] ≤
      maxErrK U.K C R := by
  classical
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  have hcg : ∀ g, ∀ d ∈ histOf c, tableOf c g d = tableOf c g₀ d := fun g _ hd =>
    tableOf_eq_of_mem c hd g g₀
  by_cases hp : ∃ j s ms m, ParseU U (histOf c) t.1 (tableOf c g₀) j s ms m
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
      rw [parseU_congr (hcg g)] at hp'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := parseU_unique hp hp'
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
    exact hp ⟨j, s, ms, m, (parseU_congr (hcg g) _ _ _ _ _).mp hp'⟩

/-- **A fresh query is bad with probability at most
`(|H| + nRf (|H| + 1)) / 2^256 + tagBound + maxErrK`.** -/
theorem prob_listBadU (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[listBadU U C R (histOf c) t.1 (tableOf c g)] ≤
      (((histOf c).card + U.nRf * ((histOf c).card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 + U.tagBound +
        maxErrK U.K C R :=
  (prEvent_or_le _ _ _).trans (by
    rw [add_assoc]
    exact add_le_add (prob_collU U c t ht) ((prEvent_or_le _ _ _).trans
      (add_le_add (prob_tagBad U c t ht) (prob_roundBadU U C R hS₀ c t ht))))

end Bad

/-! ## The trace: a winning run asks a bad fresh query -/

section Trace

variable {F St M : Type} [SampleableType F] (U : ChainSpecU F St) (C : ℕ → ListCommit M)
  (R : Piop U.K M)

variable {U C R} in
/-- No collision makes the order of the queries the order of what they refer to (`Rf`). -/
theorem rf_beforeU {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBadU U C R) T ∅ L) :
    ∀ y ∈ L, ∀ z ∈ L, U.Rf z (T y) → y ∈ before L z := by
  have nb : ∀ y ∈ L, ¬ listBadU U C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadU U C R) T ∅ L hnb y hy (Finset.notMem_empty _)
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
theorem injOn_of_not_freshBadU {L : List (List UInt8)} {T : Table}
    (hnb : ¬ FreshBad (listBadU U C R) T ∅ L) : Set.InjOn T ↑L.toFinset := by
  have nb : ∀ y ∈ L, ¬ listBadU U C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadU U C R) T ∅ L hnb y hy (Finset.notMem_empty _)
  intro y hy w hw hyw
  have hy' := List.mem_toFinset.mp hy
  have hw' := List.mem_toFinset.mp hw
  by_contra hne
  rcases before_trichotomy L y w hy' hw' hne with h | h
  · exact nb w hw' (Or.inl (Or.inl ⟨y, h, hyw⟩))
  · exact nb y hy' (Or.inl (Or.inl ⟨w, h, hyw.symm⟩))

open Classical in
/-- **The trace, on a log**: if the log holds the chain's inputs, and some candidates of the
rounds' roots, read off the log, make the transcript lost at the start and won at the end, then
some fresh input of the log is bad. -/
theorem trace_coreU (L : List (List UInt8)) (T : Table) (s : St) (ms : List (RMsg F))
    (cs : List (Option M)) (hfit : FitsAll U.K.rounds ms)
    (hmem : ∀ y ∈ allIn T (U.label s) (U.absorbsS s U.K.rounds ms), y ∈ L)
    (hcs : List.Forall₂ (· ∈ ·) cs (candLists C L.toFinset T 0 ms))
    (hwin : R.LostWon s (opened cs ms (U.chalsT T s U.K.rounds ms))) :
    FreshBad (listBadU U C R) T ∅ L := by
  by_contra hnb
  have nb : ∀ y ∈ L, ¬ listBadU U C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadU U C R) T ∅ L hnb y hy (Finset.notMem_empty _)
  have hinj : ∀ y ∈ L, ∀ z ∈ L, T y = T z → y = z := by
    intro y hy z hz hyz
    by_contra hne
    rcases before_trichotomy L y z hy hz hne with h | h
    · exact nb z hz (Or.inl (Or.inl ⟨y, h, hyz⟩))
    · exact nb y hy (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))
  have hordF := rf_beforeU hnb
  have hord : ∀ y ∈ L, ∀ z ∈ L, Refers z (T y) → y ∈ before L z :=
    fun y hy z hz h => hordF y hy z hz (U.refers_rf _ _ h)
  have injB : ∀ y, Set.InjOn T ↑(before L y) := fun y a ha b hb hab =>
    hinj a (mem_of_mem_before L a y ha) b (mem_of_mem_before L b y hb) hab
  have notag : ∀ y, NoTag U.tag (before L y) T := fun y z hz h =>
    nb z (mem_of_mem_before L z y hz) (Or.inr (Or.inl h))
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
  refine nb x hxmem (Or.inr (Or.inr ⟨rs₀.length, s, ms₀, m, ⟨hjlt, by rw [htake]; exact hf0,
    by rw [hspec]; exact hfm, by rw [ChainSpecU.absorbsS, htake]; exact hxl, fun z hz => by
      rw [ChainSpecU.absorbsS, htake] at hz
      exact hprev z hz, injB x, notag x⟩, ?_, ?_, cs₀, c, hcs0, ?_, ?_, ?_⟩))
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
