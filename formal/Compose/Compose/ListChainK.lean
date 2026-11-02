-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Generalises `formal/Compose/Compose/ListChain.lean` of this repository (two roots, three
-- challenge groups, hard-wired) to any number of rounds and roots: the structure (bad fresh queries
-- parsed from the history, each round union-bounded over the candidates of the roots before it, the
-- trace of a winning run) is that file's, which follows `formal/QuotientRpm/ChainRom.lean`; the
-- lemmas `Coll`, `prob_coll`, `Refers`, `ListCommit`, `prEvent_exists_mem_le` are reused as they are.
import Compose.ListChain

/-!
# The list chain, `k` rounds over any roots

`ListChain.lean`'s chain is `quotient::protocol`'s: the label, a root and three challenges, a
root and one challenge, five values and one challenge, its bad events written out round by round.
Here the chain is any chain of `crates/quotient/src/transcript.rs`'s form, given by its rounds
(`RoundSpec`): in round `j` the prover sends a root (two scalars, `rootWords`) if the round has
one, then `nv` values (one scalar each, `scalarWord`); the verifier draws `ns + 1` challenges,
the first the low 192 bits of the hash of the state and the round's scalars, each next the hash
of the state alone (`absorbs`: one step per challenge, the round's first step absorbing its
message). The label (`ChainSpec.label`, the statement's bytes) is hashed first.

**The protocol's soundness is a parameter** (`Piop`): the round-by-round knowledge soundness of
the PIOP the chain makes non-interactive. A round's *opened* message is its root's candidate (a
table the root may stand for) and its values; `pre s p m` is the state before round `p.length`'s
challenges, after the opened rounds `p` and the opened message `m`; `post s p m c` after its
challenges `c` (`pre_post`: the next round's state implies it). `err j` bounds the probability, over
`ns + 1` independent uniform challenges (`draws`), that round `j` turns `pre` false into `post`
true, for every prefix and message.

**Each round is union-bounded over the product of the candidate lists of the roots before it**:
a root's candidates are a `ListCommit` (`C j` for round `j`'s root, at most `(C j).bound`), read
off the inputs asked so far, so round `j`'s error is multiplied by `facL C 0 (rounds.take (j+1))`,
the product of the bounds of the roots of rounds `0..j` (`1` for a round without a root). A fresh
query is bad (`listBadK`) when its answer collides (`Coll`, as in `ListChain.lean`), or when it
is a round's first input (the chain before it asked, without collision, `ParseK`), the round's
other inputs are fresh, and its challenges turn, for **some** tuple of candidates of the roots of
the rounds so far, `pre` false into `post` true (`RoundBadK`). The parse is unique given the
history (`parseK_unique`: an input determines the input before it through the history's injective
answers, the label's length, `≢ 0 mod 32`, ends the walk, and the rounds' sizes fix the
messages), so each fresh query is bad with probability at most
`(4 |H| + 3) / 2^256 + max_j facL_j · err j` (`prob_listBadK`). A run whose candidates, read off
the inputs asked, are lost at the start (`¬ pre s [] m₀`) and won at the end (`post` of the last
round) asks a bad fresh query (`trace_coreK`), by the round-by-round argument (`LostWon`).

`ListChainKAdv.lean` runs it in mumbai's two-oracle model with the adversary's log, and
`ListChainKInstance.lean` derives `ListChain.lean`'s and `AdversaryLog.lean`'s statements from it.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm

/-! ## The rounds -/

/-- **A round of the chain**: the prover sends a root (two scalars) if `root`, then `nv` values
(one scalar each); the verifier then draws `ns + 1` challenges. -/
structure RoundSpec where
  root : Bool
  nv : ℕ
  ns : ℕ

/-- A round's message as the proof carries it: the root, if the round has one, and the values. -/
abbrev RMsg (F : Type) := Option Bytes32 × List F

variable {F : Type}

/-- A message fits its round: a root exactly when the round has one, and `nv` values. -/
def RMsg.Fits (s : RoundSpec) (m : RMsg F) : Prop := m.1.isSome = s.root ∧ m.2.length = s.nv

/-- The messages fit the rounds, one each. -/
def FitsAll : List RoundSpec → List (RMsg F) → Prop
  | [], [] => True
  | s :: rs, m :: ms => m.Fits s ∧ FitsAll rs ms
  | _, _ => False

theorem FitsAll.length_eq : ∀ {rs : List RoundSpec} {ms : List (RMsg F)}, FitsAll rs ms →
    ms.length = rs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [h.2.length_eq]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem fitsAll_append : ∀ {rs₁ rs₂ : List RoundSpec} {ms₁ ms₂ : List (RMsg F)},
    FitsAll rs₁ ms₁ → FitsAll rs₂ ms₂ → FitsAll (rs₁ ++ rs₂) (ms₁ ++ ms₂)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, fitsAll_append h.2 h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

/-- The values as the chain hashes them, one word each. -/
def scalarsOf (lim : F ≃ Limbs) (l : List F) : List UInt8 :=
  (l.map fun x => scalarWord (lim x)).flatten

/-- **A round's message as the chain hashes it**: the root's two words, then the values'. -/
def encM (lim : F ≃ Limbs) (m : RMsg F) : List UInt8 :=
  (match m.1 with
    | some r => rootWords r
    | none => []) ++ scalarsOf lim m.2

/-- A step's input: the state, then the bytes the step absorbs. -/
def stepIn (st : Bytes32) (e : List UInt8) : List UInt8 := st.toList ++ e

@[simp] theorem stepIn_nil (st : Bytes32) : stepIn st [] = st.toList := List.append_nil _

/-- **The bytes each step absorbs**, round by round: a round's first step its message, its other
`ns` steps nothing. -/
def absorbs (lim : F ≃ Limbs) : List RoundSpec → List (RMsg F) → List (List UInt8)
  | [], _ => []
  | s :: rs, ms => encM lim (ms.headD (none, [])) ::
      (List.replicate s.ns [] ++ absorbs lim rs ms.tail)

/-- The number of steps: one per challenge. -/
def nSteps : List RoundSpec → ℕ
  | [] => 0
  | s :: rs => s.ns + 1 + nSteps rs

/-- The challenges, one list per round. -/
def groupK {α : Type} : List RoundSpec → List α → List (List α)
  | [], _ => []
  | s :: rs, l => l.take (s.ns + 1) :: groupK rs (l.drop (s.ns + 1))

/-! ### Encodings -/

section Encoding

variable (lim : F ≃ Limbs)

theorem length_scalarsOf (l : List F) : (scalarsOf lim l).length = 32 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [scalarsOf, List.map_cons, List.flatten_cons, List.length_append,
      length_scalarWord, List.length_cons] at ih ⊢
    rw [ih]
    ring

theorem scalarsOf_inj : ∀ {l l' : List F}, l.length = l'.length →
    scalarsOf lim l = scalarsOf lim l' → l = l'
  | [], [], _, _ => rfl
  | a :: l, a' :: l', hl, h => by
    simp only [scalarsOf, List.map_cons, List.flatten_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    have e1 : a = a' := lim.injective (scalarWord_injective h1)
    have e2 : l = l' := scalarsOf_inj (by simpa using hl) h2
    rw [e1, e2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem dvd_length_encM (m : RMsg F) : 32 ∣ (encM lim m).length := by
  obtain ⟨r, l⟩ := m
  cases r <;> simp [encM, length_scalarsOf, Nat.dvd_add, Nat.dvd_mul_right] <;> omega

/-- **A message is determined by its bytes**, among the messages of a round. -/
theorem encM_inj {s : RoundSpec} {m m' : RMsg F} (h : m.Fits s) (h' : m'.Fits s)
    (he : encM lim m = encM lim m') : m = m' := by
  obtain ⟨r, l⟩ := m
  obtain ⟨r', l'⟩ := m'
  obtain ⟨hr, hl⟩ := h
  obtain ⟨hr', hl'⟩ := h'
  simp only at hr hl hr' hl'
  have hll : l.length = l'.length := hl.trans hl'.symm
  cases r with
  | none =>
    cases r' with
    | none =>
      simp only [encM, List.nil_append] at he
      rw [scalarsOf_inj lim hll he]
    | some _ => exact absurd (hr.trans hr'.symm) (by simp)
  | some a =>
    cases r' with
    | none => exact absurd (hr.trans hr'.symm) (by simp)
    | some a' =>
      simp only [encM] at he
      obtain ⟨h1, h2⟩ := List.append_inj he (by simp)
      rw [rootWords_injective h1, scalarsOf_inj lim hll h2]

theorem length_absorbs : ∀ (rs : List RoundSpec) (ms : List (RMsg F)),
    (absorbs lim rs ms).length = nSteps rs
  | [], _ => rfl
  | s :: rs, ms => by
    simp only [absorbs, nSteps, List.length_cons, List.length_append, List.length_replicate,
      length_absorbs rs ms.tail]
    omega

theorem dvd_of_mem_absorbs : ∀ (rs : List RoundSpec) (ms : List (RMsg F)) (e : List UInt8),
    e ∈ absorbs lim rs ms → 32 ∣ e.length
  | [], _, e, h => by simp [absorbs] at h
  | s :: rs, ms, e, h => by
    simp only [absorbs, List.mem_cons, List.mem_append, List.mem_replicate] at h
    rcases h with rfl | ⟨-, rfl⟩ | h
    · exact dvd_length_encM lim _
    · simp
    · exact dvd_of_mem_absorbs rs ms.tail e h

/-- **The messages are determined by the bytes the steps absorb**, given the rounds. -/
theorem absorbs_inj : ∀ {rs : List RoundSpec} {ms ms' : List (RMsg F)}, FitsAll rs ms →
    FitsAll rs ms' → absorbs lim rs ms = absorbs lim rs ms' → ms = ms'
  | [], [], [], _, _, _ => rfl
  | s :: rs, m :: ms, m' :: ms', h, h', he => by
    simp only [absorbs, List.headD_cons, List.tail_cons, List.cons.injEq] at he
    obtain ⟨h1, h2⟩ := he
    rw [encM_inj lim h.1 h'.1 h1, absorbs_inj h.2 h'.2 (List.append_cancel_left h2)]
  | [], _ :: _, _, h, _, _ => h.elim
  | [], [], _ :: _, _, h', _ => h'.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, h', _ => h'.elim

theorem absorbs_append : ∀ (rs₁ rs₂ : List RoundSpec) (ms₁ ms₂ : List (RMsg F)),
    ms₁.length = rs₁.length →
      absorbs lim (rs₁ ++ rs₂) (ms₁ ++ ms₂) = absorbs lim rs₁ ms₁ ++ absorbs lim rs₂ ms₂
  | [], _, [], _, _ => rfl
  | s :: rs₁, rs₂, m :: ms₁, ms₂, h => by
    simp only [List.cons_append, absorbs, List.headD_cons, List.tail_cons, List.append_assoc,
      absorbs_append rs₁ rs₂ ms₁ ms₂ (by simpa using h)]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

theorem absorbs_single (s : RoundSpec) (m : RMsg F) :
    absorbs lim [s] [m] = encM lim m :: List.replicate s.ns [] := by
  simp [absorbs]

theorem nSteps_take_succ : ∀ (rs : List RoundSpec) (j : ℕ) (h : j < rs.length),
    nSteps (rs.take (j + 1)) = nSteps (rs.take j) + (rs[j]'h).ns + 1
  | s :: rs, 0, _ => by simp [nSteps]
  | s :: rs, j + 1, h => by
    simp only [List.take_succ_cons, nSteps, List.getElem_cons_succ]
    rw [nSteps_take_succ rs j (by simpa using h)]
    omega

/-- **The number of steps before a round determines the round.** -/
theorem nSteps_take_inj : ∀ (rs : List RoundSpec) (j j' : ℕ), j ≤ rs.length → j' ≤ rs.length →
    nSteps (rs.take j) = nSteps (rs.take j') → j = j'
  | _, 0, 0, _, _, _ => rfl
  | [], _ + 1, _, h, _, _ => by simp at h
  | [], _, _ + 1, _, h, _ => by simp at h
  | s :: rs, 0, j' + 1, _, _, h => by simp only [List.take_succ_cons, List.take_zero, nSteps] at h; omega
  | s :: rs, j + 1, 0, _, _, h => by simp only [List.take_succ_cons, List.take_zero, nSteps] at h; omega
  | s :: rs, j + 1, j' + 1, h₁, h₂, h => by
    simp only [List.take_succ_cons, nSteps] at h
    rw [nSteps_take_inj rs j j' (by simpa using h₁) (by simpa using h₂) (by omega)]

theorem length_groupK {α : Type} : ∀ (rs : List RoundSpec) (l : List α),
    (groupK rs l).length = rs.length
  | [], _ => rfl
  | s :: rs, l => by simp [groupK, length_groupK rs]

theorem groupK_append {α : Type} : ∀ (rs₁ rs₂ : List RoundSpec) (l₁ l₂ : List α),
    l₁.length = nSteps rs₁ → groupK (rs₁ ++ rs₂) (l₁ ++ l₂) = groupK rs₁ l₁ ++ groupK rs₂ l₂
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => by simp [nSteps] at h
  | s :: rs₁, rs₂, l₁, l₂, h => by
    simp only [nSteps] at h
    simp only [List.cons_append, groupK, List.cons.injEq]
    refine ⟨List.take_append_of_le_length (by omega), ?_⟩
    rw [List.drop_append_of_le_length (by omega)]
    exact groupK_append rs₁ rs₂ _ l₂ (by simp only [List.length_drop]; omega)

theorem groupK_single {α : Type} (s : RoundSpec) (l : List α) (h : l.length = s.ns + 1) :
    groupK [s] l = [l] := by
  simp [groupK, List.take_of_length_le (le_of_eq h)]

end Encoding

/-! ## The chain on a table -/

section Table

/-- The chain's inputs before its last, from the input `y`: each step's input the state (the
answer to the input before) and the step's bytes. -/
def prevIn (T : Table) : List UInt8 → List (List UInt8) → List (List UInt8)
  | _, [] => []
  | y, e :: es => y :: prevIn T (stepIn (T y) e) es

/-- The chain's last input, from the input `y`. -/
def lastIn (T : Table) : List UInt8 → List (List UInt8) → List UInt8
  | y, [] => y
  | y, e :: es => lastIn T (stepIn (T y) e) es

/-- **The chain's inputs**, from the input `y` (the label), one per step after it. -/
def allIn (T : Table) : List UInt8 → List (List UInt8) → List (List UInt8)
  | y, [] => [y]
  | y, e :: es => y :: allIn T (stepIn (T y) e) es

variable (T : Table)

theorem allIn_eq : ∀ (y : List UInt8) (es : List (List UInt8)),
    allIn T y es = prevIn T y es ++ [lastIn T y es]
  | _, [] => rfl
  | y, e :: es => by simp [allIn, prevIn, lastIn, allIn_eq _ es]

theorem lastIn_append : ∀ (y : List UInt8) (es₁ es₂ : List (List UInt8)),
    lastIn T y (es₁ ++ es₂) = lastIn T (lastIn T y es₁) es₂
  | _, [], _ => rfl
  | y, e :: es₁, es₂ => lastIn_append _ es₁ es₂

theorem prevIn_append : ∀ (y : List UInt8) (es₁ es₂ : List (List UInt8)),
    prevIn T y (es₁ ++ es₂) = prevIn T y es₁ ++ prevIn T (lastIn T y es₁) es₂
  | _, [], _ => rfl
  | y, e :: es₁, es₂ => by simp [prevIn, lastIn, prevIn_append _ es₁ es₂]

theorem lastIn_concat (y : List UInt8) (es : List (List UInt8)) (e : List UInt8) :
    lastIn T y (es ++ [e]) = stepIn (T (lastIn T y es)) e := by
  rw [lastIn_append]
  rfl

theorem prevIn_concat (y : List UInt8) (es : List (List UInt8)) (e : List UInt8) :
    prevIn T y (es ++ [e]) = allIn T y es := by
  rw [prevIn_append, allIn_eq]
  rfl

theorem allIn_append (y : List UInt8) (es₁ es₂ : List (List UInt8)) :
    allIn T y (es₁ ++ es₂) = prevIn T y es₁ ++ allIn T (lastIn T y es₁) es₂ := by
  rw [allIn_eq, allIn_eq, prevIn_append, lastIn_append, List.append_assoc]

theorem head_mem_allIn (y : List UInt8) (es : List (List UInt8)) : y ∈ allIn T y es := by
  cases es <;> simp [allIn]

theorem length_stepIn (st : Bytes32) (e : List UInt8) : (stepIn st e).length = 32 + e.length := by
  simp [stepIn]

theorem take_stepIn (st : Bytes32) (e : List UInt8) : (stepIn st e).take 32 = st.toList := by
  simp [stepIn, List.take_append]

theorem stepIn_inj {st st' : Bytes32} {e e' : List UInt8} (h : stepIn st e = stepIn st' e') :
    st = st' ∧ e = e' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, h2⟩

/-- The chain reads the table only at its inputs before the last. -/
theorem chain_congr {T T' : Table} : ∀ (y : List UInt8) (es : List (List UInt8)),
    (∀ z ∈ prevIn T y es, T z = T' z) →
      prevIn T' y es = prevIn T y es ∧ lastIn T' y es = lastIn T y es
  | _, [], _ => ⟨rfl, rfl⟩
  | y, e :: es, h => by
    have hy : T y = T' y := h y (by simp [prevIn])
    have ih := chain_congr (stepIn (T y) e) es fun z hz => h z (by simp [prevIn, hz])
    simp only [prevIn, lastIn, ← hy, ih.1, ih.2, and_self]

/-- **The chain before an input is determined by the input**, through injective answers: two
chains asked without collision ending at the same input start at the same label and absorb the
same bytes, when every step's bytes are whole words and the labels are not. -/
theorem chain_unique {H : Hist} (hi : Set.InjOn T ↑H) :
    ∀ (es es' : List (List UInt8)) (y y' : List UInt8),
      (∀ e ∈ es, 32 ∣ e.length) → (∀ e ∈ es', 32 ∣ e.length) → ¬ 32 ∣ y.length →
      ¬ 32 ∣ y'.length → (∀ z ∈ prevIn T y es, z ∈ H) → (∀ z ∈ prevIn T y' es', z ∈ H) →
      lastIn T y es = lastIn T y' es' → y = y' ∧ es = es' := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
    intro es' y y' _ hd' hy hy' _ _ h
    rcases List.eq_nil_or_concat es' with rfl | ⟨L, b, rfl⟩
    · exact ⟨h, rfl⟩
    · simp only [List.concat_eq_append] at *
      exfalso
      rw [lastIn_concat] at h
      have hl : y.length = 32 + b.length := (congrArg List.length h).trans (length_stepIn _ _)
      exact hy (by rw [hl]; exact Nat.dvd_add (by norm_num) (hd' b (by simp)))
  | append_singleton es₀ e ih =>
    intro es' y y' hd hd' hy hy' hH hH' h
    rcases List.eq_nil_or_concat es' with rfl | ⟨L, b, rfl⟩
    · exfalso
      rw [lastIn_concat] at h
      have hl : y'.length = 32 + e.length := (congrArg List.length h).symm.trans (length_stepIn _ _)
      exact hy' (by rw [hl]; exact Nat.dvd_add (by norm_num) (hd e (by simp)))
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
      obtain ⟨rfl, rfl⟩ := ih L y y' (fun e' he' => hd e' (by simp [he']))
        (fun e' he' => hd' e' (by simp [he'])) hy hy' hsub hsub' (hi ha ha' hT)
      exact ⟨rfl, by rw [heb]⟩

end Table

/-! ## The chain's specification, its challenges -/

/-- **What the chain is given**: how a field element is written (its three limbs), the label of a
statement (`¬ 32 ∣` its length: the label is not a step's input), and the rounds. -/
structure ChainSpec (F St : Type) where
  lim : F ≃ Limbs
  label : St → List UInt8
  label_injective : Function.Injective label
  label_len : ∀ s, ¬ 32 ∣ (label s).length
  rounds : List RoundSpec

/-- **A challenge**: the low 192 bits of a state, as a field element (`Wire.chal`). -/
def chalL (lim : F ≃ Limbs) (st : Bytes32) : F := lim.symm (stateLimbs st)

/-- **The challenges of a chain on a table**, one list per round: the states after each step,
read as field elements. -/
def chalsT (lim : F ≃ Limbs) (T : Table) (lab : List UInt8) (rs : List RoundSpec)
    (ms : List (RMsg F)) : List (List F) :=
  groupK rs (((allIn T lab (absorbs lim rs ms)).tail.map T).map (chalL lim))

/-- **The chain over a hash `H` in any monad**, from the input `y`: every answer, the first the
seed. -/
def runM {m : Type → Type} [Monad m] (H : List UInt8 → m Bytes32) :
    List UInt8 → List (List UInt8) → m (List Bytes32)
  | y, [] => H y >>= fun st => pure [st]
  | y, e :: es => H y >>= fun st => runM H (stepIn st e) es >>= fun rest => pure (st :: rest)

namespace ChainSpec

variable {St : Type} (K : ChainSpec F St)

/-- Round `j`'s specification. -/
def spec (j : ℕ) : RoundSpec := K.rounds.getD j ⟨false, 0, 0⟩

/-- The challenges, one list per round, from the chain's answers. -/
def chalsOf (sts : List Bytes32) : List (List F) := groupK K.rounds (sts.tail.map (chalL K.lim))

/-- **The chain** of a statement and its messages, over a hash `H`. -/
def chain {m : Type → Type} [Monad m] (H : List UInt8 → m Bytes32) (s : St)
    (ms : List (RMsg F)) : m (List (List F)) :=
  K.chalsOf <$> runM H (K.label s) (absorbs K.lim K.rounds ms)

/-- The chain's number of queries: the label and one per step. -/
def nQ : ℕ := nSteps K.rounds + 1

theorem spec_eq (j : ℕ) (h : j < K.rounds.length) : K.spec j = K.rounds[j] := by
  simp [spec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

end ChainSpec

/-! ## Uniform challenges -/

/-- **`n` independent uniform draws.** -/
def draws (α : Type) [SampleableType α] : ℕ → ProbComp (List α)
  | 0 => pure []
  | n + 1 => ($ᵗ α : ProbComp α) >>= fun a => draws α n >>= fun l => pure (a :: l)

section Chal

variable [Fintype F] [DecidableEq F] [SampleableType F]

theorem chalL_fiber (lim : F ≃ Limbs) (x : F) :
    (Finset.univ.filter fun st : Bytes32 => chalL lim st = x).card =
      (Finset.univ : Finset (Vector UInt8 8)).card := by
  have h : (Finset.univ.filter fun st : Bytes32 => chalL lim st = x) =
      Finset.univ.filter fun st : Bytes32 => stateLimbs st = lim x :=
    Finset.filter_congr fun st _ => by simp only [chalL, Equiv.symm_apply_eq]
  rw [h]
  exact stateLimbs_fiber (lim x)

/-- **The low 192 bits of a uniform state are uniform** (`prEvent_chal`, for any limbs). -/
theorem prEvent_chalL (lim : F ≃ Limbs) (p : F → Prop) :
    Pr{let st ← $ᵗ Bytes32}[p (chalL lim st)] = Pr{let x ← $ᵗ F}[p x] := by
  classical
  exact prEvent_uniform_balanced (chalL lim) _ (chalL_fiber lim) p

theorem chalL_evalDistEq (lim : F ≃ Limbs) :
    (chalL lim <$> ($ᵗ Bytes32 : ProbComp Bytes32)) =ᵈ ($ᵗ F : ProbComp F) := fun p => by
  rw [prEvent_map]
  exact prEvent_chalL lim p

/-- **`n` uniform states read as challenges are `n` uniform challenges.** -/
theorem draws_chalL_evalDistEq (lim : F ≃ Limbs) : ∀ n : ℕ,
    ((fun l => l.map (chalL lim)) <$> draws Bytes32 n) =ᵈ draws F n
  | 0 => by simp only [draws, map_pure, List.map_nil]; exact EvalDistEq.rfl
  | n + 1 => by
    have e1 : ((fun l => l.map (chalL lim)) <$> draws Bytes32 (n + 1)) =
        (chalL lim <$> ($ᵗ Bytes32 : ProbComp Bytes32)) >>= fun x =>
          (fun l => x :: l) <$> ((fun l => l.map (chalL lim)) <$> draws Bytes32 n) := by
      simp only [draws, map_bind, map_pure, List.map_cons, bind_map_left, Functor.map_map]
      simp only [map_eq_bind_pure_comp, Function.comp_def]
    have e2 : draws F (n + 1) = ($ᵗ F : ProbComp F) >>= fun x => (fun l => x :: l) <$> draws F n := by
      simp only [draws, map_eq_bind_pure_comp, Function.comp_def]
    rw [e1, e2]
    exact EvalDistEq.bind (chalL_evalDistEq lim) fun x => (draws_chalL_evalDistEq lim n).map _

theorem prEvent_draws_chalL (lim : F ≃ Limbs) (n : ℕ) (Q : List F → Prop) :
    Pr{let l ← draws Bytes32 n}[Q (l.map (chalL lim))] = Pr{let l ← draws F n}[Q l] := by
  rw [← prEvent_map]
  exact (draws_chalL_evalDistEq lim n).prEvent_eq Q

end Chal

/-! ## Cells along a path of a uniform table -/

section Path

variable {D Rg : Type} [DecidableEq D] [Fintype D] [SampleableType Rg] [SampleableType (D → Rg)]

/-- The cells of a path: `t`, then the cell `f` names from its answer, `n` of them. -/
def pathCells (g : D → Rg) (f : Rg → D) : D → ℕ → List D
  | _, 0 => []
  | t, n + 1 => t :: pathCells g f (f (g t)) n

/-- The answers along a path. -/
def pathAns (g : D → Rg) (f : Rg → D) : D → ℕ → List Rg
  | _, 0 => []
  | t, n + 1 => g t :: pathAns g f (f (g t)) n

theorem path_update (g : D → Rg) (f : Rg → D) (t : D) (a : Rg) : ∀ (n : ℕ) (y : D),
    t ∉ pathCells (Function.update g t a) f y n →
      pathCells (Function.update g t a) f y n = pathCells g f y n ∧
        pathAns (Function.update g t a) f y n = pathAns g f y n
  | 0, _, _ => ⟨rfl, rfl⟩
  | n + 1, y, h => by
    simp only [pathCells, List.mem_cons, not_or] at h
    have hu : Function.update g t a y = g y := Function.update_of_ne (Ne.symm h.1) _ _
    have ih := path_update g f t a n (f (Function.update g t a y)) h.2
    rw [hu] at ih
    simp only [pathCells, pathAns, hu, ih.1, ih.2, and_self]

/-- **`n` distinct cells along a path are `n` uniform draws** (`prEvent_three_cells`, for any
`n`). -/
theorem prEvent_path (f : Rg → D) : ∀ (n : ℕ) (t : D) (Q : List Rg → Prop),
    Pr{let g ← $ᵗ (D → Rg)}[(pathCells g f t n).Nodup ∧ Q (pathAns g f t n)] ≤
      Pr{let l ← draws Rg n}[Q l]
  | 0, t, Q => by
    classical
    simp only [pathCells, pathAns, List.nodup_nil, true_and, draws]
    by_cases hq : Q []
    · rw [prEvent_pure [] Q]
      simp only [hq, ite_true]
      exact prEvent_le_one _
    · rw [prEvent_const_of_not _ hq]
      exact bot_le
  | n + 1, t, Q => by
    rw [prEvent_uniformTable_update (R := fun _ => Rg) t]
    calc _ ≤ prEvent (($ᵗ Rg : ProbComp Rg) >>= fun a =>
          (fun l => Q (a :: l)) <$> draws Rg n) := by
          refine prEvent_bind_mono' _ _ _ fun a => ?_
          refine (prEvent_mono _ _ (fun g => (pathCells g f (f a) n).Nodup ∧
            Q (a :: pathAns g f (f a) n)) fun g h => ?_).trans
            (prEvent_path f n (f a) fun l => Q (a :: l))
          simp only [pathCells, pathAns, Function.update_self, List.nodup_cons] at h
          obtain ⟨⟨hn, hd⟩, hq⟩ := h
          obtain ⟨e1, e2⟩ := path_update g f t a n (f a) hn
          rw [e1] at hd
          rw [e2] at hq
          exact ⟨hd, hq⟩
      _ = Pr{let l ← draws Rg (n + 1)}[Q l] := by
          simp only [draws, map_bind, map_pure]
          simp only [map_eq_bind_pure_comp, Function.comp_def]

end Path

section CachePath

variable {S : Finset (List UInt8)}

/-- **A round's squeezes on a cache's completion are a path of the table**: its first input
fresh, the inputs after it not asked, the answers are the table's along the path. -/
theorem allIn_tableOf (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (g : ↥S → Bytes32) :
    ∀ (n : ℕ) (t : ↥S), c t = none →
      (∀ y ∈ (allIn (tableOf c g) t.1 (List.replicate n [])).tail, y ∉ histOf c) →
        allIn (tableOf c g) t.1 (List.replicate n []) =
            (pathCells g (fun u => ⟨u.toList, hS₀ u⟩) t (n + 1)).map Subtype.val ∧
          (allIn (tableOf c g) t.1 (List.replicate n [])).map (tableOf c g) =
            pathAns g (fun u => ⟨u.toList, hS₀ u⟩) t (n + 1)
  | 0, t, ht, _ => by
    simp [allIn, pathCells, pathAns, tableOf_fresh c ht g]
  | n + 1, t, ht, h => by
    have e : tableOf c g t.1 = g t := tableOf_fresh c ht g
    have hstep : stepIn (tableOf c g t.1) [] = (g t).toList := by rw [stepIn_nil, e]
    have hall : allIn (tableOf c g) t.1 (List.replicate (n + 1) []) =
        t.1 :: allIn (tableOf c g) (g t).toList (List.replicate n []) := by
      rw [List.replicate_succ, allIn, hstep]
    rw [hall] at h ⊢
    have hmem : (g t).toList ∉ histOf c := h _ (head_mem_allIn _ _ _)
    have ht' : c ⟨(g t).toList, hS₀ _⟩ = none := by
      by_contra hne
      exact hmem (mem_histOf.mpr ⟨hS₀ _, hne⟩)
    have ih := allIn_tableOf hS₀ c g n ⟨(g t).toList, hS₀ _⟩ ht'
      (fun y hy => h y (List.mem_of_mem_tail hy))
    simp only at ih
    refine ⟨?_, ?_⟩
    · rw [ih.1]
      rfl
    · rw [List.map_cons, ih.2, e]
      rfl

/-- **A round's challenges, its squeezes fresh and distinct, are uniform draws.** -/
theorem prEvent_round (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) (n : ℕ) (Q : List Bytes32 → Prop) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[
      (∀ y ∈ (allIn (tableOf c g) t.1 (List.replicate n [])).tail, y ∉ histOf c) ∧
        (allIn (tableOf c g) t.1 (List.replicate n [])).Nodup ∧
          Q ((allIn (tableOf c g) t.1 (List.replicate n [])).map (tableOf c g))] ≤
      Pr{let l ← draws Bytes32 (n + 1)}[Q l] := by
  refine (prEvent_mono _ _ (fun g => (pathCells g (fun u => ⟨u.toList, hS₀ u⟩) t (n + 1)).Nodup ∧
    Q (pathAns g (fun u => ⟨u.toList, hS₀ u⟩) t (n + 1))) fun g h => ?_).trans
      (prEvent_path _ (n + 1) t Q)
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨e1, e2⟩ := allIn_tableOf hS₀ c g n t ht h1
  rw [e1] at h2
  rw [e2] at h3
  exact ⟨(List.nodup_map_iff Subtype.val_injective).mp h2, h3⟩

end CachePath

/-! ## The protocol's round-by-round soundness -/

/-- **An opened transcript**: each round's opened message (its root's candidate, if it has a
root, and its values) and its challenges. -/
abbrev Opened (M F : Type) := List ((Option M × List F) × List F)

/-- **The protocol's round-by-round knowledge soundness**, a parameter: the state `pre s p m`
before round `p.length`'s challenges (after the opened rounds `p` and its opened message `m`), the
state `post s p m c` after them, the next round's state implying this round's after
(`pre_post`), and each round's error `err j`: over `ns + 1` uniform challenges, the probability
that the round turns its state from lost to won, for every prefix and message. -/
structure Piop {St : Type} [SampleableType F] (K : ChainSpec F St) (M : Type) where
  pre : St → Opened M F → Option M × List F → Prop
  post : St → Opened M F → Option M × List F → List F → Prop
  pre_post : ∀ s p m c m', pre s (p ++ [(m, c)]) m' → post s p m c
  err : ℕ → ℝ≥0∞
  sound : ∀ (j : ℕ) (s : St) (p : Opened M F) (m : Option M × List F), j < K.rounds.length →
    p.length = j → Pr{let c ← draws F ((K.spec j).ns + 1)}[¬ pre s p m ∧ post s p m c] ≤ err j

/-- **A transcript is lost at the start and won at the end**: the first round's state before its
challenges is lost, the last round's after its challenges won. -/
def Piop.LostWon {St M : Type} [SampleableType F] {K : ChainSpec F St} (R : Piop K M) (s : St) :
    Opened M F → Prop
  | [] => False
  | (m, c) :: rest => ¬ R.pre s [] m ∧
      ∃ p m' c', (m, c) :: rest = p ++ [(m', c')] ∧ R.post s p m' c'

/-- **The round-by-round argument**: a transcript lost at the start and won at the end has a
round that turns its state from lost to won. -/
theorem Piop.exists_bad {St M : Type} [SampleableType F] {K : ChainSpec F St} (R : Piop K M)
    (s : St) : ∀ (rest : Opened M F) (p : Opened M F) (m : Option M × List F) (c : List F),
      ¬ R.pre s p m → (∃ q m' c', p ++ (m, c) :: rest = q ++ [(m', c')] ∧ R.post s q m' c') →
        ∃ p' m' c' rest', p ++ (m, c) :: rest = p' ++ (m', c') :: rest' ∧ ¬ R.pre s p' m' ∧
          R.post s p' m' c'
  | [], p, m, c, hpre, ⟨q, m', c', he, hpost⟩ => by
    obtain ⟨rfl, he'⟩ := List.append_inj' he rfl
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at he'
    rcases he' with ⟨rfl, rfl⟩
    exact ⟨_, _, _, [], rfl, hpre, hpost⟩
  | (m₂, c₂) :: rest, p, m, c, hpre, hwin => by
    by_cases hpost : R.post s p m c
    · exact ⟨p, m, c, (m₂, c₂) :: rest, rfl, hpre, hpost⟩
    · have hpre₂ : ¬ R.pre s (p ++ [(m, c)]) m₂ := fun h => hpost (R.pre_post s p m c m₂ h)
      have e : p ++ (m, c) :: (m₂, c₂) :: rest = (p ++ [(m, c)]) ++ (m₂, c₂) :: rest := by simp
      rw [e] at hwin ⊢
      exact Piop.exists_bad R s rest (p ++ [(m, c)]) m₂ c₂ hpre₂ hwin

theorem Piop.exists_bad_of_lostWon {St M : Type} [SampleableType F] {K : ChainSpec F St}
    (R : Piop K M) (s : St) (full : Opened M F) (h : R.LostWon s full) :
    ∃ p m c rest, full = p ++ (m, c) :: rest ∧ ¬ R.pre s p m ∧ R.post s p m c := by
  match full, h with
  | (m, c) :: rest, ⟨hpre, hwin⟩ =>
    exact R.exists_bad s rest [] m c hpre (by simpa using hwin)

/-! ## The candidates -/

/-- A round's candidates: its root's, as `some`, or `none` for a round without a root. -/
def optC {M : Type} (C : ListCommit M) (H : Hist) (T : Table) (m : RMsg F) : List (Option M) :=
  match m.1 with
  | some r => (C.cands H T r).map some
  | none => [none]

/-- The candidate lists of the rounds from round `i` on. -/
def candLists {M : Type} (C : ℕ → ListCommit M) (H : Hist) (T : Table) :
    ℕ → List (RMsg F) → List (List (Option M))
  | _, [] => []
  | i, m :: ms => optC (C i) H T m :: candLists C H T (i + 1) ms

/-- **The union bound's factor**: the product of the list bounds of the rounds' roots, from round
`i` on (`1` for a round without a root). -/
def facL {M : Type} (C : ℕ → ListCommit M) : ℕ → List RoundSpec → ℕ
  | _, [] => 1
  | i, s :: rs => (if s.root then (C i).bound else 1) * facL C (i + 1) rs

/-- The opened transcript of candidates, messages and challenges (a missing round's challenges
read as `[]`). -/
def opened {M : Type} : List (Option M) → List (RMsg F) → List (List F) → Opened M F
  | c :: cs, m :: ms, chs => ((c, m.2), chs.headD []) :: opened cs ms chs.tail
  | _, _, _ => []

section Cands

variable {M : Type}

theorem length_candLists (C : ℕ → ListCommit M) (H : Hist) (T : Table) :
    ∀ (i : ℕ) (ms : List (RMsg F)), (candLists C H T i ms).length = ms.length
  | _, [] => rfl
  | i, _ :: ms => by simp [candLists, length_candLists C H T (i + 1) ms]

theorem length_optC_le (C : ListCommit M) (H : Hist) (T : Table) {s : RoundSpec} {m : RMsg F}
    (h : m.Fits s) : (optC C H T m).length ≤ if s.root then C.bound else 1 := by
  obtain ⟨r, l⟩ := m
  obtain ⟨hr, -⟩ := h
  cases r with
  | none =>
    simp only at hr
    simp [optC, ← hr]
  | some r =>
    simp only [Option.isSome_some] at hr
    simp only [optC, List.length_map, ← hr, ite_true]
    exact C.length_le H T r

theorem prod_candLists_le (C : ℕ → ListCommit M) (H : Hist) (T : Table) :
    ∀ (i : ℕ) (rs : List RoundSpec) (ms : List (RMsg F)), FitsAll rs ms →
      ((candLists C H T i ms).map List.length).prod ≤ facL C i rs
  | _, [], [], _ => by simp [candLists, facL]
  | i, s :: rs, m :: ms, h => by
    simp only [candLists, facL, List.map_cons, List.prod_cons]
    exact Nat.mul_le_mul (length_optC_le (C i) H T h.1) (prod_candLists_le C H T (i + 1) rs ms h.2)
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

theorem facL_append (C : ℕ → ListCommit M) : ∀ (i : ℕ) (rs₁ rs₂ : List RoundSpec),
    facL C i (rs₁ ++ rs₂) = facL C i rs₁ * facL C (i + rs₁.length) rs₂
  | i, [], rs₂ => by simp [facL]
  | i, s :: rs₁, rs₂ => by
    simp only [List.cons_append, facL, facL_append C (i + 1) rs₁ rs₂, List.length_cons]
    rw [mul_assoc, show i + 1 + rs₁.length = i + (rs₁.length + 1) by omega]

theorem candLists_congr (C : ℕ → ListCommit M) {H : Hist} {T T' : Table}
    (h : ∀ d ∈ H, T d = T' d) : ∀ (i : ℕ) (ms : List (RMsg F)),
      candLists C H T i ms = candLists C H T' i ms
  | _, [] => rfl
  | i, m :: ms => by
    simp only [candLists, candLists_congr C h (i + 1) ms, List.cons.injEq, and_true]
    unfold optC
    split <;> simp [(C i).congr H T T' _ h]

theorem optC_congr (C : ListCommit M) {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d)
    (m : RMsg F) : optC C H T m = optC C H T' m := by
  unfold optC
  split <;> simp [C.congr H T T' _ h]

theorem length_opened : ∀ (cs : List (Option M)) (ms : List (RMsg F)) (chs : List (List F)),
    cs.length = ms.length → (opened cs ms chs).length = ms.length
  | [], [], _, _ => rfl
  | _ :: cs, _ :: ms, chs, h1 => by
    simp only [opened, List.length_cons] at h1 ⊢
    rw [length_opened cs ms chs.tail (by omega)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- **The union bound over a product of lists**: if each tuple's event has probability at most
`ε`, some tuple of the lists' members has probability at most the product of the lengths times
`ε`. -/
theorem prEvent_forall₂_le {α β : Type} (mx : ProbComp α) (E : List β → α → Prop) (ε : ℝ≥0∞) :
    ∀ Ls : List (List β), (∀ cs, List.Forall₂ (· ∈ ·) cs Ls → Pr{let a ← mx}[E cs a] ≤ ε) →
      Pr{let a ← mx}[∃ cs, List.Forall₂ (· ∈ ·) cs Ls ∧ E cs a] ≤ ((Ls.map List.length).prod : ℕ) * ε
  | [], h => by
    refine (prEvent_mono _ _ (fun a => E [] a) fun a ha => ?_).trans ?_
    · obtain ⟨cs, hcs, he⟩ := ha
      rw [List.forall₂_nil_right_iff] at hcs
      rwa [hcs] at he
    · simpa using h [] List.Forall₂.nil
  | l :: Ls, h => by
    have hl := fun b (hb : b ∈ l) => prEvent_forall₂_le mx (fun cs a => E (b :: cs) a) ε Ls
      fun cs hcs => h (b :: cs) (List.Forall₂.cons hb hcs)
    refine (prEvent_mono _ _ (fun a => ∃ b ∈ l, ∃ cs, List.Forall₂ (· ∈ ·) cs Ls ∧ E (b :: cs) a)
      fun a ha => ?_).trans ?_
    · obtain ⟨cs, hcs, he⟩ := ha
      cases hcs with
      | cons hb hcs' => exact ⟨_, hb, _, hcs', he⟩
    · refine (prEvent_exists_mem_le mx _ _ l fun b hb => hl b hb).trans (le_of_eq ?_)
      simp only [List.map_cons, List.prod_cons, Nat.cast_mul, mul_assoc]

end Cands

/-! ## The bad events -/

section Bad

variable {St M : Type} [SampleableType F] (K : ChainSpec F St) (C : ℕ → ListCommit M)
  (R : Piop K M)

/-- **`x` is round `j`'s first input**: for a statement `s`, the messages `ms` of the rounds before
and `m` of round `j`, fitting them, the chain before `x` was asked (its inputs in `H`), without
collision. -/
def ParseK (H : Hist) (x : List UInt8) (T : Table) (j : ℕ) (s : St) (ms : List (RMsg F))
    (m : RMsg F) : Prop :=
  j < K.rounds.length ∧ FitsAll (K.rounds.take j) ms ∧ m.Fits (K.spec j) ∧
    x = lastIn T (K.label s) (absorbs K.lim (K.rounds.take j) ms ++ [encM K.lim m]) ∧
    (∀ y ∈ prevIn T (K.label s) (absorbs K.lim (K.rounds.take j) ms ++ [encM K.lim m]), y ∈ H) ∧
    Set.InjOn T ↑H

/-- Round `j`'s inputs from its first input `x`: `x`, then each state, `ns` of them. -/
def ChainSpec.sqIns (T : Table) (x : List UInt8) (j : ℕ) : List (List UInt8) :=
  allIn T x (List.replicate (K.spec j).ns [])

/-- **Round `j` is bad at its first input**: the inputs after it fresh and distinct, and its
challenges turn the state from lost to won for some candidates of the roots of the rounds up to
`j`, read off the history. -/
def RoundBadK (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ j s ms m, ParseK K H x T j s ms m ∧
    (∀ y ∈ (K.sqIns T x j).tail, y ∉ H) ∧ (K.sqIns T x j).Nodup ∧
    ∃ cs c, List.Forall₂ (· ∈ ·) cs (candLists C H T 0 ms) ∧ c ∈ optC (C j) H T m ∧
      ¬ R.pre s (opened cs ms (chalsT K.lim T (K.label s) (K.rounds.take j) ms)) (c, m.2) ∧
      R.post s (opened cs ms (chalsT K.lim T (K.label s) (K.rounds.take j) ms)) (c, m.2)
        (((K.sqIns T x j).map T).map (chalL K.lim))

/-- **A bad fresh query**: a collision, or a bad round. -/
def listBadK (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  Coll H x T ∨ RoundBadK K C R H x T

/-! ### The parse reads the history only, and is unique -/

theorem allIn_congr {T T' : Table} (y : List UInt8) (es : List (List UInt8))
    (h : ∀ z ∈ allIn T y es, T z = T' z) :
    allIn T' y es = allIn T y es ∧ (allIn T' y es).map T' = (allIn T y es).map T := by
  have hp : ∀ z ∈ prevIn T y es, T z = T' z := fun z hz => h z (by
    rw [allIn_eq]
    exact List.mem_append_left _ hz)
  obtain ⟨e1, e2⟩ := chain_congr y es hp
  have ea : allIn T' y es = allIn T y es := by rw [allIn_eq, allIn_eq, e1, e2]
  refine ⟨ea, ?_⟩
  rw [ea]
  exact List.map_congr_left fun z hz => (h z hz).symm

theorem chalsT_congr {T T' : Table} (lim : F ≃ Limbs) (y : List UInt8) (rs : List RoundSpec)
    (ms : List (RMsg F)) (h : ∀ z ∈ allIn T y (absorbs lim rs ms), T z = T' z) :
    chalsT lim T' y rs ms = chalsT lim T y rs ms := by
  obtain ⟨e1, e2⟩ := allIn_congr y _ h
  have e3 : (allIn T' y (absorbs lim rs ms)).tail.map T' =
      (allIn T y (absorbs lim rs ms)).tail.map T := by
    rw [e1]
    exact List.map_congr_left fun z hz => (h z (List.mem_of_mem_tail hz)).symm
  unfold chalsT
  rw [e3]

variable {K}

theorem parseK_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x : List UInt8)
    (j : ℕ) (s : St) (ms : List (RMsg F)) (m : RMsg F) :
    ParseK K H x T j s ms m ↔ ParseK K H x T' j s ms m := by
  unfold ParseK
  constructor
  · rintro ⟨h1, h2, h3, hx, hH, hi⟩
    obtain ⟨e1, e2⟩ := chain_congr (T := T) (T' := T') _ _ fun z hz => h z (hH z hz)
    refine ⟨h1, h2, h3, hx.trans e2.symm, fun y hy => hH y (by rwa [e1] at hy),
      (injOn_congr h).mp hi⟩
  · rintro ⟨h1, h2, h3, hx, hH, hi⟩
    obtain ⟨e1, e2⟩ := chain_congr (T := T') (T' := T) _ _ fun z hz => (h z (hH z hz)).symm
    refine ⟨h1, h2, h3, hx.trans e2.symm, fun y hy => hH y (by rwa [e1] at hy),
      (injOn_congr h).mpr hi⟩

theorem ParseK.length_eq {H : Hist} {x : List UInt8} {T : Table} {j : ℕ} {s : St}
    {ms : List (RMsg F)} {m : RMsg F} (h : ParseK K H x T j s ms m) : ms.length = j := by
  rw [h.2.1.length_eq, List.length_take]
  exact min_eq_left (le_of_lt h.1)

/-- The chain before round `j`'s first input was asked. -/
theorem ParseK.allIn_sub {H : Hist} {x : List UInt8} {T : Table} {j : ℕ} {s : St}
    {ms : List (RMsg F)} {m : RMsg F} (h : ParseK K H x T j s ms m) :
    ∀ z ∈ allIn T (K.label s) (absorbs K.lim (K.rounds.take j) ms), z ∈ H := by
  intro z hz
  refine h.2.2.2.2.1 z ?_
  rw [prevIn_concat]
  exact hz

/-- **The parse is unique.** -/
theorem parseK_unique {H : Hist} {x : List UInt8} {T : Table} {j j' : ℕ} {s s' : St}
    {ms ms' : List (RMsg F)} {m m' : RMsg F} (h : ParseK K H x T j s ms m)
    (h' : ParseK K H x T j' s' ms' m') : j = j' ∧ s = s' ∧ ms = ms' ∧ m = m' := by
  obtain ⟨hj, hf, hm, hx, hH, hi⟩ := h
  obtain ⟨hj', hf', hm', hx', hH', -⟩ := h'
  have hd : ∀ (k : ℕ) (ms₀ : List (RMsg F)) (m₀ : RMsg F),
      ∀ e ∈ absorbs K.lim (K.rounds.take k) ms₀ ++ [encM K.lim m₀], 32 ∣ e.length := by
    intro k ms₀ m₀ e he
    rcases List.mem_append.mp he with he | he
    · exact dvd_of_mem_absorbs K.lim _ _ e he
    · rw [List.mem_singleton.mp he]
      exact dvd_length_encM K.lim m₀
  obtain ⟨hlab, hes⟩ := chain_unique T hi _ _ _ _ (hd j ms m) (hd j' ms' m') (K.label_len s)
    (K.label_len s') hH hH' (hx.symm.trans hx')
  have hs : s = s' := K.label_injective hlab
  have hl := congrArg List.length hes
  simp only [List.length_append, List.length_singleton, length_absorbs] at hl
  have hjj : j = j' := nSteps_take_inj K.rounds j j' (le_of_lt hj) (le_of_lt hj') (by omega)
  subst hjj
  obtain ⟨ha, he⟩ := List.append_inj hes (by simp [length_absorbs])
  simp only [List.cons.injEq, and_true] at he
  exact ⟨rfl, hs, absorbs_inj K.lim hf hf' ha, encM_inj K.lim hm hm' he⟩

variable (K)

/-- Round `j`'s inputs read the table at its first input and at 32-byte inputs only. -/
theorem allIn_replicate_congr {T T' : Table} (hs : ∀ v : Bytes32, T v.toList = T' v.toList) :
    ∀ (n : ℕ) (x : List UInt8), T x = T' x →
      allIn T' x (List.replicate n []) = allIn T x (List.replicate n []) ∧
        (allIn T' x (List.replicate n [])).map T' = (allIn T x (List.replicate n [])).map T
  | 0, x, hx => by simp [allIn, hx]
  | n + 1, x, hx => by
    have ih := allIn_replicate_congr hs n (T x).toList (hs (T x))
    have e : stepIn (T' x) [] = (T x).toList := by rw [stepIn_nil, hx]
    simp only [List.replicate_succ, allIn, List.map_cons]
    rw [e, stepIn_nil]
    refine ⟨by rw [ih.1], ?_⟩
    rw [ih.2, hx]

/-- **`listBadK` reads the table on the inputs asked, at the fresh input, and at the 32-byte
inputs** (the states its rounds' lookahead hashes). -/
theorem listBadK_congr {H : Hist} {x : List UInt8} {T T' : Table} (hH : ∀ d ∈ H, T d = T' d)
    (hx : T x = T' x) (hs : ∀ v : Bytes32, T v.toList = T' v.toList) :
    listBadK K C R H x T ↔ listBadK K C R H x T' := by
  have hcoll : Coll H x T ↔ Coll H x T' := by
    unfold Coll
    rw [hx]
    constructor
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).symm.trans h⟩
      · exact Or.inr h
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).trans h⟩
      · exact Or.inr h
  have hsq : ∀ j, K.sqIns T' x j = K.sqIns T x j ∧
      (K.sqIns T' x j).map T' = (K.sqIns T x j).map T :=
    fun j => allIn_replicate_congr hs _ x hx
  have hround : ∀ T₁ T₂ : Table, (∀ d ∈ H, T₁ d = T₂ d) →
      (∀ j, K.sqIns T₂ x j = K.sqIns T₁ x j ∧ (K.sqIns T₂ x j).map T₂ = (K.sqIns T₁ x j).map T₁) →
      RoundBadK K C R H x T₁ → RoundBadK K C R H x T₂ := by
    intro T₁ T₂ h12 hsq12 hb
    obtain ⟨j, s, ms, m, hp, h1, h2, cs, c, hcs, hc, h3, h4⟩ := hb
    have hch : chalsT K.lim T₂ (K.label s) (K.rounds.take j) ms =
        chalsT K.lim T₁ (K.label s) (K.rounds.take j) ms :=
      chalsT_congr K.lim _ _ _ fun z hz => h12 z (hp.allIn_sub z hz)
    refine ⟨j, s, ms, m, (parseK_congr h12 x j s ms m).mp hp, by rw [(hsq12 j).1]; exact h1,
      by rw [(hsq12 j).1]; exact h2, cs, c, by rwa [← candLists_congr C h12], by
        rwa [← optC_congr (C j) h12], by rw [hch]; exact h3, ?_⟩
    rw [hch, (hsq12 j).2]
    exact h4
  unfold listBadK
  rw [hcoll]
  exact or_congr_right ⟨hround T T' hH hsq, hround T' T (fun d hd => (hH d hd).symm)
    fun j => ⟨(hsq j).1.symm, (hsq j).2.symm⟩⟩

/-! ### Each fresh query is bad with small probability -/

/-- **The largest round error times its union bound's factor**: round `j`'s error times the
product of the list bounds of the roots of the rounds `0..j`. -/
noncomputable def maxErrK : ℝ≥0∞ :=
  (Finset.range K.rounds.length).sup fun j => (facL C 0 (K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j

theorem facL_take_succ (j : ℕ) (hj : j < K.rounds.length) :
    facL C 0 (K.rounds.take (j + 1)) =
      facL C 0 (K.rounds.take j) * (if (K.spec j).root then (C j).bound else 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, facL_append,
    List.length_take, min_eq_left (le_of_lt hj), K.spec_eq j hj]
  simp [facL]

variable [Fintype F] [DecidableEq F]

variable {S : Finset (List UInt8)}

/-- **A round is bad with probability at most its error times its factor**: the parse is read off
the history, so at most one round and one parse are possible, the candidates and the challenges
before are fixed by the history, and the round's challenges are uniform. -/
theorem prob_roundBadK (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[RoundBadK K C R (histOf c) t.1 (tableOf c g)] ≤
      maxErrK K C R := by
  classical
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  have hcg : ∀ g, ∀ d ∈ histOf c, tableOf c g d = tableOf c g₀ d := fun g _ hd =>
    tableOf_eq_of_mem c hd g g₀
  by_cases hp : ∃ j s ms m, ParseK K (histOf c) t.1 (tableOf c g₀) j s ms m
  · obtain ⟨j, s, ms, m, hp⟩ := hp
    have hj : j < K.rounds.length := hp.1
    let T₀ := tableOf c g₀
    let chs := chalsT K.lim T₀ (K.label s) (K.rounds.take j) ms
    let Ls := candLists C (histOf c) T₀ 0 ms
    let oc := optC (C j) (histOf c) T₀ m
    let E : List (Option M) → (↥S → Bytes32) → Prop := fun cs g => ∃ c' ∈ oc,
      (∀ y ∈ (allIn (tableOf c g) t.1 (List.replicate (K.spec j).ns [])).tail, y ∉ histOf c) ∧
      (allIn (tableOf c g) t.1 (List.replicate (K.spec j).ns [])).Nodup ∧
      (¬ R.pre s (opened cs ms chs) (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2)
        (((allIn (tableOf c g) t.1 (List.replicate (K.spec j).ns [])).map (tableOf c g)).map
          (chalL K.lim)))
    refine (prEvent_mono _ _ (fun g => ∃ cs, List.Forall₂ (· ∈ ·) cs Ls ∧ E cs g)
      fun g hg => ?_).trans ?_
    · obtain ⟨j', s', ms', m', hp', h1, h2, cs, c', hcs, hc', h3, h4⟩ := hg
      rw [parseK_congr (hcg g)] at hp'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := parseK_unique hp hp'
      have hch : chalsT K.lim (tableOf c g) (K.label s) (K.rounds.take j) ms = chs :=
        chalsT_congr K.lim _ _ _ fun z hz => (hcg g z (hp.allIn_sub z hz)).symm
      rw [candLists_congr C (hcg g)] at hcs
      rw [optC_congr (C j) (hcg g)] at hc'
      rw [hch] at h3 h4
      exact ⟨cs, hcs, c', hc', h1, h2, h3, h4⟩
    · have hone : ∀ cs, List.Forall₂ (· ∈ ·) cs Ls → ∀ c' ∈ oc,
          Pr{let g ← $ᵗ (↥S → Bytes32)}[
            (∀ y ∈ (allIn (tableOf c g) t.1 (List.replicate (K.spec j).ns [])).tail,
              y ∉ histOf c) ∧
            (allIn (tableOf c g) t.1 (List.replicate (K.spec j).ns [])).Nodup ∧
            (¬ R.pre s (opened cs ms chs) (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2)
              (((allIn (tableOf c g) t.1 (List.replicate (K.spec j).ns [])).map
                (tableOf c g)).map (chalL K.lim)))] ≤ R.err j := by
        intro cs hcs c' _
        have hlen : (opened cs ms chs).length = j := by
          rw [length_opened cs ms chs (hcs.length_eq.trans (length_candLists C _ _ 0 ms)),
            hp.length_eq]
        refine (prEvent_round hS₀ c t ht (K.spec j).ns (fun l => ¬ R.pre s (opened cs ms chs)
          (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2) (l.map (chalL K.lim)))).trans ?_
        rw [prEvent_draws_chalL K.lim ((K.spec j).ns + 1) (fun l => ¬ R.pre s (opened cs ms chs)
          (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2) l)]
        exact R.sound j s _ _ hj hlen
      refine (prEvent_forall₂_le _ E ((oc.length : ℝ≥0∞) * R.err j) Ls fun cs hcs =>
        prEvent_exists_mem_le _ _ _ oc fun c' hc' => hone cs hcs c' hc').trans ?_
      have hf1 := prod_candLists_le C (histOf c) T₀ 0 _ ms hp.2.1
      have hf2 := length_optC_le (C j) (histOf c) T₀ hp.2.2.1
      have hfac : (Ls.map List.length).prod * oc.length ≤ facL C 0 (K.rounds.take (j + 1)) := by
        rw [facL_take_succ K C j hj]
        exact Nat.mul_le_mul hf1 hf2
      calc ((Ls.map List.length).prod : ℝ≥0∞) * ((oc.length : ℝ≥0∞) * R.err j)
          = (((Ls.map List.length).prod * oc.length : ℕ) : ℝ≥0∞) * R.err j := by
            push_cast
            ring
        _ ≤ (facL C 0 (K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j := by
            gcongr
        _ ≤ maxErrK K C R :=
            Finset.le_sup (f := fun j => (facL C 0 (K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j)
              (Finset.mem_range.mpr hj)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun g hg => ?_]
    · exact bot_le
    obtain ⟨j, s, ms, m, hp', -⟩ := hg
    exact hp ⟨j, s, ms, m, (parseK_congr (hcg g) _ _ _ _ _).mp hp'⟩

/-- **A fresh query is bad with probability at most `(4 |H| + 3) / 2^256 + max_j facL_j · err j`.** -/
theorem prob_listBadK (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[listBadK K C R (histOf c) t.1 (tableOf c g)] ≤
      ((4 * (histOf c).card + 3 : ℕ) : ℝ≥0∞) / 2 ^ 256 + maxErrK K C R :=
  (prEvent_or_le _ _ _).trans (add_le_add (prob_coll c t ht) (prob_roundBadK K C R hS₀ c t ht))

end Bad

/-! ## The trace: a winning run asks a bad fresh query -/

section TraceLemmas

variable {M : Type}

theorem allIn_cons_tail (T : Table) (y : List UInt8) (es : List (List UInt8)) :
    allIn T y es = y :: (allIn T y es).tail := by
  cases es <;> rfl

theorem allIn_append' (T : Table) : ∀ (y : List UInt8) (es₁ es₂ : List (List UInt8)),
    allIn T y (es₁ ++ es₂) = allIn T y es₁ ++ (allIn T (lastIn T y es₁) es₂).tail
  | y, [], es₂ => by
    rw [List.nil_append, allIn_cons_tail T y es₂]
    rfl
  | y, e :: es₁, es₂ => by
    simp only [List.cons_append, allIn, lastIn, allIn_append' T _ es₁ es₂]

theorem tail_allIn_append (T : Table) (y : List UInt8) (es₁ es₂ : List (List UInt8)) :
    (allIn T y (es₁ ++ es₂)).tail = (allIn T y es₁).tail ++ (allIn T (lastIn T y es₁) es₂).tail := by
  rw [allIn_append', allIn_cons_tail T y es₁]
  simp only [List.cons_append, List.tail_cons]

theorem length_tail_allIn (T : Table) : ∀ (y : List UInt8) (es : List (List UInt8)),
    (allIn T y es).tail.length = es.length
  | _, [] => rfl
  | y, e :: es => by
    simp only [allIn, List.tail_cons, List.length_cons]
    rw [allIn_cons_tail, List.length_cons, length_tail_allIn T _ es]

theorem length_allIn_replicate (T : Table) (x : List UInt8) (n : ℕ) :
    (allIn T x (List.replicate n [])).length = n + 1 := by
  rw [allIn_cons_tail, List.length_cons, length_tail_allIn, List.length_replicate]

/-- The challenges of rounds one after the other. -/
theorem chalsT_append (lim : F ≃ Limbs) (T : Table) (y : List UInt8) (rs₀ rs₂ : List RoundSpec)
    (ms₀ ms₂ : List (RMsg F)) (h : ms₀.length = rs₀.length) :
    chalsT lim T y (rs₀ ++ rs₂) (ms₀ ++ ms₂) =
      chalsT lim T y rs₀ ms₀ ++ chalsT lim T (lastIn T y (absorbs lim rs₀ ms₀)) rs₂ ms₂ := by
  unfold chalsT
  rw [absorbs_append lim rs₀ rs₂ ms₀ ms₂ h, tail_allIn_append, List.map_append, List.map_append,
    groupK_append]
  rw [List.length_map, List.length_map, length_tail_allIn, length_absorbs]

theorem chalsT_single (lim : F ≃ Limbs) (T : Table) (y : List UInt8) (s : RoundSpec)
    (m : RMsg F) : chalsT lim T y [s] [m] =
      [((allIn T (stepIn (T y) (encM lim m)) (List.replicate s.ns [])).map T).map (chalL lim)] := by
  unfold chalsT
  rw [absorbs_single]
  simp only [allIn, List.tail_cons]
  exact groupK_single s _ (by simp [length_allIn_replicate])

/-- A round's challenges: the states of its squeezes from its first input. -/
theorem chalsT_cons (lim : F ≃ Limbs) (T : Table) (y : List UInt8) (s : RoundSpec)
    (rs : List RoundSpec) (m : RMsg F) (ms : List (RMsg F)) :
    chalsT lim T y (s :: rs) (m :: ms) =
      ((allIn T (stepIn (T y) (encM lim m)) (List.replicate s.ns [])).map T).map (chalL lim) ::
        chalsT lim T (lastIn T y (absorbs lim [s] [m])) rs ms := by
  have h := chalsT_append lim T y [s] rs [m] ms rfl
  simp only [List.singleton_append] at h
  rw [h, chalsT_single]
  rfl

theorem candLists_append (C : ℕ → ListCommit M) (H : Hist) (T : Table) :
    ∀ (i : ℕ) (ms₀ ms₂ : List (RMsg F)),
      candLists C H T i (ms₀ ++ ms₂) = candLists C H T i ms₀ ++ candLists C H T (i + ms₀.length) ms₂
  | i, [], ms₂ => by simp [candLists]
  | i, m :: ms₀, ms₂ => by
    simp only [List.cons_append, candLists, candLists_append C H T (i + 1) ms₀ ms₂,
      List.length_cons, List.cons.injEq, true_and]
    rw [show i + 1 + ms₀.length = i + (ms₀.length + 1) by omega]

theorem forall₂_append_split {α β : Type} {R' : α → β → Prop} :
    ∀ {a₁ a₂ : List α} {b₁ b₂ : List β}, a₁.length = b₁.length →
      List.Forall₂ R' (a₁ ++ a₂) (b₁ ++ b₂) → List.Forall₂ R' a₁ b₁ ∧ List.Forall₂ R' a₂ b₂
  | [], _, [], _, _, h => ⟨List.Forall₂.nil, h⟩
  | _ :: _, _, _ :: _, _, hl, h => by
    cases h with
    | cons h1 h2 =>
      obtain ⟨e1, e2⟩ := forall₂_append_split (by simpa using hl) h2
      exact ⟨List.Forall₂.cons h1 e1, e2⟩
  | [], _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, hl, _ => by simp at hl

/-- **An opened transcript split at a round** splits its candidates, messages and challenges. -/
theorem opened_eq_append_cons : ∀ (p : Opened M F) (cs : List (Option M)) (ms : List (RMsg F))
    (chs : List (List F)) (m' : Option M × List F) (c' : List F) (rest : Opened M F),
    chs.length = ms.length → opened cs ms chs = p ++ (m', c') :: rest →
      ∃ cs₀ c cs₁ ms₀ m ms₁ chs₀ ch chs₁, cs = cs₀ ++ c :: cs₁ ∧ ms = ms₀ ++ m :: ms₁ ∧
        chs = chs₀ ++ ch :: chs₁ ∧ cs₀.length = p.length ∧ ms₀.length = p.length ∧
        chs₀.length = p.length ∧ p = opened cs₀ ms₀ chs₀ ∧ m' = (c, m.2) ∧ c' = ch
  | [], c :: cs, m :: ms, ch :: chs, m', c', rest, _, h => by
    simp only [opened, List.headD_cons, List.tail_cons, List.nil_append, List.cons.injEq,
      Prod.mk.injEq] at h
    exact ⟨[], c, cs, [], m, ms, [], ch, chs, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by rw [← h.1.1], h.1.2.symm⟩
  | q :: p, c₀ :: cs, m₀ :: ms, ch₀ :: chs, m', c', rest, hl, h => by
    simp only [opened, List.headD_cons, List.tail_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨cs₀, c, cs₁, ms₀, m, ms₁, chs₀, ch, chs₁, e1, e2, e3, l1, l2, l3, ep, em, ec⟩ :=
      opened_eq_append_cons p cs ms chs m' c' rest (by simpa using hl) h.2
    exact ⟨c₀ :: cs₀, c, cs₁, m₀ :: ms₀, m, ms₁, ch₀ :: chs₀, ch, chs₁, by rw [e1]; rfl,
      by rw [e2]; rfl, by rw [e3]; rfl, by simp [l1], by simp [l2], by simp [l3],
      by rw [← h.1, ep]; rfl, em, ec⟩
  | [], [], _, _, _, _, _, _, h => by simp [opened] at h
  | [], _ :: _, [], _, _, _, _, _, h => by simp [opened] at h
  | _, _ :: _, _ :: _, [], _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, _, h => by simp [opened] at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by simp [opened] at h

theorem fitsAll_split : ∀ (rs : List RoundSpec) (ms₀ : List (RMsg F)) (m : RMsg F)
    (ms₁ : List (RMsg F)), FitsAll rs (ms₀ ++ m :: ms₁) →
      ∃ rs₀ s rs₁, rs = rs₀ ++ s :: rs₁ ∧ FitsAll rs₀ ms₀ ∧ m.Fits s ∧ FitsAll rs₁ ms₁
  | s :: rs, [], m, ms₁, h => ⟨[], s, rs, rfl, trivial, h.1, h.2⟩
  | s :: rs, m₀ :: ms₀, m, ms₁, h => by
    obtain ⟨rs₀, s', rs₁, e, h1, h2, h3⟩ := fitsAll_split rs ms₀ m ms₁ h.2
    exact ⟨s :: rs₀, s', rs₁, by rw [e]; rfl, ⟨h.1, h1⟩, h2, h3⟩
  | [], [], _, _, h => h.elim
  | [], _ :: _, _, _, h => h.elim

theorem encM_mem_absorbs (lim : F ≃ Limbs) : ∀ (rs : List RoundSpec) (ms : List (RMsg F)),
    ms.length = rs.length → ∀ m ∈ ms, encM lim m ∈ absorbs lim rs ms
  | [], [], _, m, h => by simp at h
  | s :: rs, m₀ :: ms, hl, m, h => by
    simp only [absorbs, List.headD_cons, List.tail_cons, List.mem_cons, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (encM_mem_absorbs lim rs ms (by simpa using hl) m h))
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- Every step's bytes follow a state in one of the chain's inputs. -/
theorem step_mem_allIn (T : Table) : ∀ (y : List UInt8) (es : List (List UInt8)),
    ∀ e ∈ es, ∃ st, stepIn st e ∈ allIn T y es
  | _, [], e, h => by simp at h
  | y, e' :: es, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨T y, by rw [allIn, allIn_cons_tail]; simp⟩
    · obtain ⟨st, hst⟩ := step_mem_allIn T _ es e h
      exact ⟨st, by rw [allIn]; exact List.mem_cons_of_mem _ hst⟩

/-- **The input absorbing a root refers to it.** -/
theorem refers_stepIn_encM (lim : F ≃ Limbs) (st r : Bytes32) (l : List F) :
    Refers (stepIn st (encM lim (some r, l))) r := by
  refine Or.inr (Or.inr ?_)
  simp [stepIn, encM, List.drop_append, List.take_append]

theorem candLists_stable (C : ℕ → ListCommit M) {H H' : Hist} {T : Table} :
    ∀ (i : ℕ) (ms : List (RMsg F)),
      (∀ m ∈ ms, ∀ r, m.1 = some r → ∀ k, (C k).cands H T r = (C k).cands H' T r) →
        candLists C H T i ms = candLists C H' T i ms
  | _, [], _ => rfl
  | i, m :: ms, h => by
    simp only [candLists, List.cons.injEq]
    refine ⟨?_, candLists_stable C (i + 1) ms fun m' hm' => h m' (List.mem_cons_of_mem _ hm')⟩
    unfold optC
    split
    · next r hr => rw [h m List.mem_cons_self r hr i]
    · rfl

theorem optC_stable (C : ListCommit M) {H H' : Hist} {T : Table} (m : RMsg F)
    (h : ∀ r, m.1 = some r → C.cands H T r = C.cands H' T r) : optC C H T m = optC C H' T m := by
  unfold optC
  split
  · next r hr => rw [h r hr]
  · rfl

/-- **No collision orders the chain's inputs**: each input comes before every later one. -/
theorem chain_pairwise {L : List (List UInt8)} {T : Table}
    (hord : ∀ y ∈ L, ∀ z ∈ L, Refers z (T y) → y ∈ before L z) :
    ∀ (y : List UInt8) (es : List (List UInt8)), (∀ z ∈ allIn T y es, z ∈ L) →
      (allIn T y es).Pairwise (fun a b => a ∈ before L b)
  | y, [], _ => List.pairwise_singleton _ _
  | y, e :: es, h => by
    rw [allIn, List.pairwise_cons]
    have hy : y ∈ L := h y (by simp [allIn])
    have hrest : ∀ z ∈ allIn T (stepIn (T y) e) es, z ∈ L := fun z hz =>
      h z (by rw [allIn]; exact List.mem_cons_of_mem _ hz)
    have ih := chain_pairwise hord _ es hrest
    have hy' : y ∈ before L (stepIn (T y) e) :=
      hord y hy _ (hrest _ (head_mem_allIn _ _ _)) (Or.inl (take_stepIn _ _).symm)
    refine ⟨fun z hz => ?_, ih⟩
    rw [allIn_cons_tail] at hz ih
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hy'
    · exact before_subset_of_mem L _ z ((List.pairwise_cons.mp ih).1 z hz) hy'

end TraceLemmas

section Trace

variable {St M : Type} [SampleableType F] (K : ChainSpec F St) (C : ℕ → ListCommit M)
  (R : Piop K M)

open Classical in
/-- **The trace, on a log**: if the log holds the chain's inputs, and some candidates of the
rounds' roots, read off the log, make the transcript lost at the start and won at the end, then
some fresh input of the log is bad. -/
theorem trace_coreK (L : List (List UInt8)) (T : Table) (s : St) (ms : List (RMsg F))
    (cs : List (Option M)) (hfit : FitsAll K.rounds ms)
    (hmem : ∀ y ∈ allIn T (K.label s) (absorbs K.lim K.rounds ms), y ∈ L)
    (hcs : List.Forall₂ (· ∈ ·) cs (candLists C L.toFinset T 0 ms))
    (hwin : R.LostWon s (opened cs ms (chalsT K.lim T (K.label s) K.rounds ms))) :
    FreshBad (listBadK K C R) T ∅ L := by
  by_contra hnb
  have nb : ∀ y ∈ L, ¬ listBadK K C R (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBadK K C R) T ∅ L hnb y hy (Finset.notMem_empty _)
  -- No collision: the answers to distinct inputs differ, and an input's answer is referred to
  -- by another only if it was asked first.
  have hinj : ∀ y ∈ L, ∀ z ∈ L, T y = T z → y = z := by
    intro y hy z hz hyz
    by_contra hne
    rcases before_trichotomy L y z hy hz hne with h | h
    · exact nb z hz (Or.inl (Or.inl ⟨y, h, hyz⟩))
    · exact nb y hy (Or.inl (Or.inl ⟨z, h, hyz.symm⟩))
  have hord : ∀ y ∈ L, ∀ z ∈ L, Refers z (T y) → y ∈ before L z := by
    intro y hy z hz h
    by_contra hb
    by_cases hyz : y = z
    · subst hyz
      exact nb y hy (Or.inl (Or.inr ⟨y, Finset.mem_insert_self _ _, h⟩))
    · rcases before_trichotomy L y z hy hz hyz with h' | h'
      · exact hb h'
      · exact nb y hy (Or.inl (Or.inr ⟨z, Finset.mem_insert_of_mem h', h⟩))
  have injB : ∀ y, Set.InjOn T ↑(before L y) := fun y a ha b hb hab =>
    hinj a (mem_of_mem_before L a y ha) b (mem_of_mem_before L b y hb) hab
  -- After a root is absorbed, its candidates are the ones the history already fixed.
  have stab : ∀ {N : Type} (Cn : ListCommit N) (r : Bytes32) (y z : List UInt8), y ∈ L →
      Refers y r → (y = z ∨ y ∈ before L z) →
        Cn.cands L.toFinset T r = Cn.cands (before L z) T r := by
    intro N Cn r y z hy hry hyz
    have hsub : ∀ w, w ∈ before L y → w ∈ before L z := by
      rcases hyz with rfl | h
      · exact fun w hw => hw
      · exact fun w hw => before_subset_of_mem L y z h hw
    refine Cn.stable (before L z) L.toFinset T r (fun w hw => List.mem_toFinset.mpr
      (mem_of_mem_before L w z hw)) (fun w hw hwr => ?_) (fun y' hy' w hw h => ?_)
    · rw [← hwr] at hry
      exact hsub w (hord w (List.mem_toFinset.mp hw) y hy hry)
    · exact before_subset_of_mem L y' z hy' (hord w (List.mem_toFinset.mp hw) y'
        (mem_of_mem_before L y' z hy') h)
  -- The round that turns the state from lost to won.
  obtain ⟨p, m', c', rest, hfull, hpre, hpost⟩ := R.exists_bad_of_lostWon s _ hwin
  obtain ⟨cs₀, c, cs₁, ms₀, m, ms₁, chs₀, ch, chs₁, ecs, ems, echs, l1, l2, l3, ep, em, ec⟩ :=
    opened_eq_append_cons p cs ms _ m' c' rest (by rw [chalsT, length_groupK, hfit.length_eq])
      hfull
  rw [ems] at hfit
  obtain ⟨rs₀, s₁, rs₁, ers, hf0, hfm, hf1⟩ := fitsAll_split K.rounds ms₀ m ms₁ hfit
  have hl0 : ms₀.length = rs₀.length := hf0.length_eq
  have htake : K.rounds.take rs₀.length = rs₀ := by
    rw [ers]
    exact List.take_left' rfl
  have hspec : K.spec rs₀.length = s₁ := by
    rw [ChainSpec.spec, ers, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
    simp
  have hjlt : rs₀.length < K.rounds.length := by
    rw [ers]
    simp
  -- The round's first input and its squeezes.
  set lab := K.label s
  set y₀ := lastIn T lab (absorbs K.lim rs₀ ms₀)
  set x := stepIn (T y₀) (encM K.lim m) with hx
  have hxl : x = lastIn T lab (absorbs K.lim rs₀ ms₀ ++ [encM K.lim m]) := by
    rw [lastIn_concat]
  -- The challenges split at the round.
  have hchs : chalsT K.lim T lab K.rounds ms =
      chalsT K.lim T lab rs₀ ms₀ ++ (((allIn T x (List.replicate s₁.ns [])).map T).map
        (chalL K.lim) :: chalsT K.lim T (lastIn T y₀ (absorbs K.lim [s₁] [m])) rs₁ ms₁) := by
    rw [ers, ems, chalsT_append K.lim T lab rs₀ (s₁ :: rs₁) ms₀ (m :: ms₁) hl0, chalsT_cons]
  rw [echs] at hchs
  have hl0' : chs₀.length = (chalsT K.lim T lab rs₀ ms₀).length := by
    rw [l3, ← l2, hl0, chalsT, length_groupK]
  obtain ⟨hc0, hc1⟩ := List.append_inj hchs hl0'
  simp only [List.cons.injEq] at hc1
  -- The chain's inputs, up to the round's first input and its squeezes.
  have hchain : allIn T lab (absorbs K.lim K.rounds ms) =
      prevIn T lab (absorbs K.lim rs₀ ms₀ ++ [encM K.lim m]) ++
        (allIn T x (List.replicate s₁.ns []) ++
          (allIn T (lastIn T x (List.replicate s₁.ns [])) (absorbs K.lim rs₁ ms₁)).tail) := by
    rw [ers, ems, absorbs_append K.lim rs₀ (s₁ :: rs₁) ms₀ (m :: ms₁) hl0]
    rw [show absorbs K.lim (s₁ :: rs₁) (m :: ms₁) =
      [encM K.lim m] ++ (List.replicate s₁.ns [] ++ absorbs K.lim rs₁ ms₁) by simp [absorbs]]
    rw [← List.append_assoc, allIn_append, ← hxl, allIn_append']
  have hpw := chain_pairwise hord _ _ hmem
  rw [hchain, List.pairwise_append, List.pairwise_append] at hpw
  obtain ⟨-, ⟨hsq, -, -⟩, hcross⟩ := hpw
  have hxmem : x ∈ L := hmem x (by rw [hchain]; simp [head_mem_allIn])
  -- The chain before `x` was asked before it.
  have hprev : ∀ z ∈ prevIn T lab (absorbs K.lim rs₀ ms₀ ++ [encM K.lim m]), z ∈ before L x :=
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
    have he : encM K.lim m₂ ∈ absorbs K.lim rs₀ ms₀ ++ [encM K.lim m] := by
      rcases List.mem_append.mp hm₂ with h | h
      · exact List.mem_append_left _ (encM_mem_absorbs K.lim rs₀ ms₀ hl0 m₂ h)
      · rw [List.mem_singleton.mp h]
        exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨st, hst⟩ := step_mem_allIn T lab _ _ he
    obtain ⟨o, l'⟩ := m₂
    simp only at hr
    subst hr
    rw [allIn_eq, ← hxl] at hst
    have hy : stepIn st (encM K.lim (some r, l')) ∈ L := by
      rcases List.mem_append.mp hst with h | h
      · exact mem_of_mem_before L _ x (hprev _ h)
      · rw [List.mem_singleton.mp h]
        exact hxmem
    refine stab (C k) r _ x hy (refers_stepIn_encM K.lim st r l') ?_
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
    by rw [hspec]; exact hfm, by rw [htake]; exact hxl, fun z hz => by
      rw [htake] at hz
      exact hprev z hz, injB x⟩, ?_, ?_, cs₀, c, hcs0, ?_, ?_, ?_⟩)
  · rw [ChainSpec.sqIns, hspec]
    exact hfresh
  · rw [ChainSpec.sqIns, hspec]
    exact hnodup
  · rwa [hl0] at hc
  · rw [htake, ← hc0, ← ep, ← em]
    exact hpre
  · rw [htake, ← hc0, ← ep, ← em, ChainSpec.sqIns, hspec, ← hc1.1, ← ec]
    exact hpost

end Trace

end Compose
