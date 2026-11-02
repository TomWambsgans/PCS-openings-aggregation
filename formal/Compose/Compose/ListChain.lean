-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The structure (bad fresh queries parsed from the history, their probability, the trace of a
-- winning run) follows `formal/QuotientRpm/ChainRom.lean` of this repository, whose lemmas it uses;
-- here the roots are the proof's, not hashes of the messages, and every round is union-bounded
-- over the candidate lists of the roots it follows.
import QuotientRpm.ChainRom

/-!
# The reduction with real roots: the list union, query by query

The deployed reduction's proof carries two **roots** and five values, never the polynomials:
the chain (`chainWith`, `crates/quotient/src/transcript.rs`) hashes the label, then each root's two
words after a state, then the values. What a root commits to is read off the hash's answers by an
extraction that returns a **list** of candidates (`ListCommit`: a WHIR root's level-0 Johnson
list, no out-of-domain sample at level 0), so a challenge drawn after a root must be sound for
every candidate of that root: its error is union-bounded over the list, `L₁` candidates for
`(α, β, γ)` and `L₁ L₂` pairs for `t` and `ρ`.

**The extraction**, `ListCommit`, is any function of the inputs asked so far and their answers
(`congr`) returning at most `bound` candidates for a digest, that does not change when inputs
whose answers no earlier input refers to are added (`stable`: a Merkle tree's extraction climbs
from the root through inputs that refer to their children's digests, `Refers`). A fresh answer
that an earlier input refers to is a collision event (`Coll`), so after the root is absorbed the
candidates are the ones the history already fixed.

A fresh query `x` is bad (`listBad`) when its answer collides (`Coll`: an earlier answer, or a
digest an input asked before, or `x` itself, refers to, `4 |H| + 3` values), or when `x` is the
chain's input after the first root, the second root or the values (the chain before it asked,
without collision) and its answer turns, for **some** candidate (pair) of the roots before it, the
reduction's state from lost to won. Each is bad with probability at most
`(4 |H| + 3) / 2^256 + max L₁ (L₁ L₂) · roundError` (`prob_listBad`). An accepted run whose
candidates (read off the final transcript) satisfy the claims, the cells of one failing the
relation, asks a bad fresh query (`trace_listBad`). Hence

**`knowledgeSoundness_list`**: an adversary of at most `Q` queries outputs a statement, two roots
and five values; the chain's challenges make some pair of candidates of the two roots, read off
the transcript, satisfy the verifier's claims while the witness candidate's cells fail the
relation with probability at most `(Q + 6) (max L₁ (L₁ L₂) · roundError + 4 (Q + 6) / 2^256)`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params

/-! ## Inputs that refer to a digest -/

/-- An input **refers** to a digest when the digest is its first or its second 32-byte chunk (a
Merkle node's children, a chain state), or its two words after the first 32 bytes (a root the
chain absorbs). -/
def Refers (y : List UInt8) (d : Bytes32) : Prop :=
  d.toList = y.take 32 ∨ d.toList = (y.drop 32).take 32 ∨ rootWords d = (y.drop 32).take 64

open Classical in
-- The linter runs out of recursion depth on this proof.
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- An input refers to at most three digests. -/
theorem card_refers_le (y : List UInt8) :
    (Finset.univ.filter fun u : Bytes32 => Refers y u).card ≤ 3 := by
  have hu : ∀ z : List UInt8, (Finset.univ.filter fun u : Bytes32 => u.toList = z).card ≤ 1 :=
    fun z => Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact Vector.toList_inj.mp (ha.2.trans hb.2.symm)
  have hr : (Finset.univ.filter fun u : Bytes32 => rootWords u = (y.drop 32).take 64).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact rootWords_injective (ha.2.trans hb.2.symm)
  have hsub : (Finset.univ.filter fun u : Bytes32 => Refers y u) ⊆
      ((Finset.univ.filter fun u : Bytes32 => u.toList = y.take 32) ∪
        (Finset.univ.filter fun u : Bytes32 => u.toList = (y.drop 32).take 32)) ∪
        (Finset.univ.filter fun u : Bytes32 => rootWords u = (y.drop 32).take 64) := by
    intro u hu'
    simp only [Finset.mem_filter] at hu'
    obtain ⟨-, h⟩ := hu'
    unfold Refers at h
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases h with h | h | h
    · exact Or.inl (Or.inl ⟨Finset.mem_univ _, h⟩)
    · exact Or.inl (Or.inr ⟨Finset.mem_univ _, h⟩)
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 := Finset.card_union_le (Finset.univ.filter fun u : Bytes32 => u.toList = y.take 32)
    (Finset.univ.filter fun u : Bytes32 => u.toList = (y.drop 32).take 32)
  have := hu (y.take 32)
  have := hu ((y.drop 32).take 32)
  omega

/-! ## List commitments -/

/-- **A list commitment**: candidates for what a digest commits to, read off the inputs asked so
far and their answers, at most `bound` of them, stable once the inputs below the digest are
asked. -/
structure ListCommit (M : Type) where
  /-- The largest list. -/
  bound : ℕ
  /-- The candidates of a digest, given the inputs asked and the hash's table. -/
  cands : Hist → Table → Bytes32 → List M
  length_le : ∀ H T r, (cands H T r).length ≤ bound
  /-- The candidates read only the answers to the inputs asked. -/
  congr : ∀ H T T' r, (∀ d ∈ H, T d = T' d) → cands H T r = cands H T' r
  /-- Adding inputs below which nothing asked climbs changes nothing: if every input of `H'`
  answering the digest, or a digest an input of `H` refers to, is in `H`, the candidates in
  `H'` are those in `H`. -/
  stable : ∀ (H H' : Hist) (T : Table) (r : Bytes32), H ⊆ H' → (∀ z ∈ H', T z = r → z ∈ H) →
    (∀ y ∈ H, ∀ z ∈ H', Refers y (T z) → z ∈ H) → cands H' T r = cands H T r

/-! ## The proof, the chain, the transcript -/

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]

/-- **A proof of the reduction with real commitments**: the statement's 64 bytes, the roots of the
witness and quotient tables, and the five values (`quotient::protocol::Proof` without the
openings). -/
structure RootProof (F : Type) where
  stmt : Vector UInt8 64
  r₁ : Bytes32
  r₂ : Bytes32
  v : (Fin 4 → F) × F

/-- The chain's five challenges. -/
structure Chals (F : Type) where
  α : F
  β : F
  γ : F
  t : F
  ρ : F

variable {P : Params F} {B : P.Bounds} (W : Wire P B)

/-- **The chain** of `quotient::protocol::reduce` over a hash `H` in any monad: the label, the
first root after the seed, two more states, the second root, the values. -/
def chainWith {m : Type → Type} [Monad m] (H : List UInt8 → m Bytes32) (π : RootProof F) :
    m (Chals F) := do
  let st₀ ← H (W.label π.stmt)
  let st₁ ← H (Wire.afterRoot st₀ π.r₁)
  let st₂ ← H st₁.toList
  let st₃ ← H st₂.toList
  let st₄ ← H (Wire.afterRoot st₃ π.r₂)
  let st₅ ← H (W.afterValues st₄ π.v)
  pure ⟨W.chal st₁, W.chal st₂, W.chal st₃, W.chal st₄, W.chal st₅⟩

/-- A transcript: every input asked, in order, with its answer. -/
abbrev Transcript := List (List UInt8 × Bytes32)

/-- The inputs a transcript asks. -/
def histOfTr (tr : Transcript) : Hist := (tr.map Prod.fst).toFinset

/-- The answers a transcript records (the first answer to an input; zero for inputs it does not
ask). -/
def tableOfTr (tr : Transcript) : Table := fun x =>
  ((tr.find? fun e => decide (e.1 = x)).map Prod.snd).getD (Vector.replicate 32 0)

/-- The hash, logging every query and its answer. -/
def logImpl : QueryImpl HashSpec (StateT Transcript (OracleComp HashSpec)) := fun t => do
  let u ← (hashQuery t : OracleComp HashSpec Bytes32)
  modify fun l => l ++ [(t, u)]
  pure u

/-- A computation with its transcript. -/
def logged {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Transcript) :=
  (simulateQ logImpl oa).run []

/-- **The experiment**: the adversary's proof, the chain's challenges on it, and the transcript of
every query, the adversary's and the chain's. -/
def rootExperiment (A : OracleComp HashSpec (RootProof F)) :
    OracleComp HashSpec ((RootProof F × Chals F) × Transcript) :=
  logged (A >>= fun π => chainWith W hashQuery π >>= fun ch => pure (π, ch))

/-- **What wins**: some candidate of the first root and some candidate of the second, read off the
transcript, satisfy the claims the verifier checks at the chain's challenges, while the first's
cells fail the relation for the statement. -/
def ListWins (C₁ : ListCommit B.Msg₁) (C₂ : ListCommit B.Msg₂)
    (z : (RootProof F × Chals F) × Transcript) : Prop :=
  ∃ g ∈ C₁.cands (histOfTr z.2) (tableOfTr z.2) z.1.1.r₁,
    ∃ R ∈ C₂.cands (histOfTr z.2) (tableOfTr z.2) z.1.1.r₂,
      P.Accepts (W.decode z.1.1.stmt) g.1 R.1 z.1.2.α z.1.2.β z.1.2.γ z.1.2.t z.1.1.v.1 z.1.1.v.2
          z.1.2.ρ ∧ ¬ P.Sat (W.decode z.1.1.stmt) (P.cells g.1)

/-- The union bound's factor: `L₁` candidates for the first challenge, `L₁ L₂` pairs for the
others. -/
def listFactor (L₁ L₂ : ℕ) : ℕ := max L₁ (L₁ * L₂)

/-! ## The bad events -/

variable (C₁ : ListCommit B.Msg₁) (C₂ : ListCommit B.Msg₂)

/-- **A collision**: the fresh answer at `x` repeats an earlier answer, or an input asked before,
or `x`, refers to it. -/
def Coll (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  (∃ y ∈ H, T y = T x) ∨ ∃ y ∈ insert x H, Refers y (T x)

/-- `x` is the input after the first root `r₁`, for the statement `sb`. -/
def ParseFirst (H : Hist) (x : List UInt8) (T : Table) (sb : Vector UInt8 64) (r₁ : Bytes32) :
    Prop :=
  ∃ st₀, Has H T (W.label sb) st₀ ∧ x = Wire.afterRoot st₀ r₁ ∧ Set.InjOn T ↑H

open Classical in
/-- The triple the input after the first root leads to, its states not asked before, makes the
first round's state go from lost to won for some candidate of the first root. -/
def FreshFirst (H : Hist) (x : List UInt8) (T : Table) (sb : Vector UInt8 64) (r₁ : Bytes32) :
    Prop :=
  (T x).toList ∉ H ∧ (T (T x).toList).toList ∉ H ∧ (T (T x).toList).toList ≠ (T x).toList ∧
    ∃ g ∈ C₁.cands H T r₁, ¬ State₁ (W.decode sb) g ∧
      State₂ (W.decode sb) g (W.chal (T x), W.chal (T (T x).toList),
        W.chal (T (T (T x).toList).toList))

/-- `x` is the input after the second root: the chain before it was asked, without collision,
and gave the first challenges `c`. -/
def ParseSecond (H : Hist) (x : List UInt8) (T : Table) (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)
    (c : F × F × F) : Prop :=
  ∃ st₀ st₁ st₂ st₃, Has H T (W.label sb) st₀ ∧ Has H T (Wire.afterRoot st₀ r₁) st₁ ∧
    Has H T st₁.toList st₂ ∧ Has H T st₂.toList st₃ ∧ x = Wire.afterRoot st₃ r₂ ∧
    c = (W.chal st₁, W.chal st₂, W.chal st₃) ∧ Set.InjOn T ↑H

/-- `x` is the input after the five values: the chain before it was asked, without collision,
and gave the challenges `c` and `t`. -/
def ParseThird (H : Hist) (x : List UInt8) (T : Table) (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)
    (c : F × F × F) (t : F) (v : (Fin 4 → F) × F) : Prop :=
  ∃ st₀ st₁ st₂ st₃ st₄, Has H T (W.label sb) st₀ ∧ Has H T (Wire.afterRoot st₀ r₁) st₁ ∧
    Has H T st₁.toList st₂ ∧ Has H T st₂.toList st₃ ∧ Has H T (Wire.afterRoot st₃ r₂) st₄ ∧
    x = W.afterValues st₄ v ∧ c = (W.chal st₁, W.chal st₂, W.chal st₃) ∧ t = W.chal st₄ ∧
    Set.InjOn T ↑H

/-- The first round, for some candidate. -/
def FirstBad (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ sb r₁, ParseFirst W H x T sb r₁ ∧ FreshFirst W C₁ H x T sb r₁

open Classical in
/-- The second round, for some pair of candidates. -/
def SecondBad (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ sb r₁ r₂ c, ParseSecond W H x T sb r₁ r₂ c ∧
    ∃ g ∈ C₁.cands H T r₁, ∃ R ∈ C₂.cands H T r₂,
      ¬ State₃ (W.decode sb) g c R ∧ State₄ (W.decode sb) g c R (W.chal (T x))

open Classical in
/-- The third round, for some pair of candidates. -/
def ThirdBad (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  ∃ sb r₁ r₂ c t v, ParseThird W H x T sb r₁ r₂ c t v ∧
    ∃ g ∈ C₁.cands H T r₁, ∃ R ∈ C₂.cands H T r₂,
      ¬ State₄ (W.decode sb) g c R t ∧ State₆ (W.decode sb) g c R t v (W.chal (T x))

/-- **A bad fresh query.** -/
def listBad (H : Hist) (x : List UInt8) (T : Table) : Prop :=
  Coll H x T ∨ FirstBad W C₁ H x T ∨ SecondBad W C₁ C₂ H x T ∨ ThirdBad W C₁ C₂ H x T

/-! ## The parse is unique, and reads only the history -/

section Parse

variable {W}

theorem parseFirst_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x sb r₁) :
    ParseFirst W H x T sb r₁ ↔ ParseFirst W H x T' sb r₁ := by
  simp only [ParseFirst, has_congr h, injOn_congr h]

theorem parseSecond_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (x sb r₁ r₂ c) :
    ParseSecond W H x T sb r₁ r₂ c ↔ ParseSecond W H x T' sb r₁ r₂ c := by
  simp only [ParseSecond, has_congr h, injOn_congr h]

theorem parseThird_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d)
    (x sb r₁ r₂ c t v) :
    ParseThird W H x T sb r₁ r₂ c t v ↔ ParseThird W H x T' sb r₁ r₂ c t v := by
  simp only [ParseThird, has_congr h, injOn_congr h]

theorem parseFirst_unique {H : Hist} {x : List UInt8} {T : Table} {sb sb' r₁ r₁'}
    (h : ParseFirst W H x T sb r₁) (h' : ParseFirst W H x T sb' r₁') : sb = sb' ∧ r₁ = r₁' := by
  obtain ⟨st₀, h0, hx, hi⟩ := h
  obtain ⟨st₀', h0', hx', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (hx.symm.trans hx')
  exact ⟨W.label_injective (has_inj hi h0 h0'), rfl⟩

theorem parseSecond_unique {H : Hist} {x : List UInt8} {T : Table} {sb sb' r₁ r₁' r₂ r₂' c c'}
    (h : ParseSecond W H x T sb r₁ r₂ c) (h' : ParseSecond W H x T sb' r₁' r₂' c') :
    sb = sb' ∧ r₁ = r₁' ∧ r₂ = r₂' ∧ c = c' := by
  obtain ⟨st₀, st₁, st₂, st₃, h0, h1, h2, h3, hx, hc, hi⟩ := h
  obtain ⟨st₀', st₁', st₂', st₃', h0', h1', h2', h3', hx', hc', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (hx.symm.trans hx')
  have e2 : st₂ = st₂' := Vector.toList_inj.mp (has_inj hi h3 h3')
  subst e2
  have e1 : st₁ = st₁' := Vector.toList_inj.mp (has_inj hi h2 h2')
  subst e1
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (has_inj hi h1 h1')
  exact ⟨W.label_injective (has_inj hi h0 h0'), rfl, rfl, hc.trans hc'.symm⟩

theorem parseThird_unique {H : Hist} {x : List UInt8} {T : Table}
    {sb sb' r₁ r₁' r₂ r₂' c c' t t' v v'}
    (h : ParseThird W H x T sb r₁ r₂ c t v) (h' : ParseThird W H x T sb' r₁' r₂' c' t' v') :
    sb = sb' ∧ r₁ = r₁' ∧ r₂ = r₂' ∧ c = c' ∧ t = t' ∧ v = v' := by
  obtain ⟨st₀, st₁, st₂, st₃, st₄, h0, h1, h2, h3, h4, hx, hc, ht, hi⟩ := h
  obtain ⟨st₀', st₁', st₂', st₃', st₄', h0', h1', h2', h3', h4', hx', hc', ht', -⟩ := h'
  obtain ⟨rfl, rfl⟩ := W.afterValues_injective (hx.symm.trans hx')
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (has_inj hi h4 h4')
  have e2 : st₂ = st₂' := Vector.toList_inj.mp (has_inj hi h3 h3')
  subst e2
  have e1 : st₁ = st₁' := Vector.toList_inj.mp (has_inj hi h2 h2')
  subst e1
  obtain ⟨rfl, rfl⟩ := Wire.afterRoot_injective (has_inj hi h1 h1')
  exact ⟨W.label_injective (has_inj hi h0 h0'), rfl, rfl, hc.trans hc'.symm, ht.trans ht'.symm,
    rfl⟩

/-- An input after a root is not both the first and the second. -/
theorem parseFirst_parseSecond {H : Hist} {x : List UInt8} {T : Table} {sb sb' r₁ r₁' r₂ c}
    (h : ParseFirst W H x T sb r₁) (h' : ParseSecond W H x T sb' r₁' r₂ c) : False := by
  obtain ⟨st₀, h0, hx, hi⟩ := h
  obtain ⟨-, -, st₂, st₃, -, -, -, h3, hx', -, -⟩ := h'
  obtain ⟨rfl, -⟩ := Wire.afterRoot_injective (hx.symm.trans hx')
  have := congrArg List.length (has_inj hi h0 h3)
  simp [length_label] at this

theorem parseFirst_parseThird {H : Hist} {x : List UInt8} {T : Table} {sb sb' r₁ r₁' r₂ c t v}
    (h : ParseFirst W H x T sb r₁) (h' : ParseThird W H x T sb' r₁' r₂ c t v) : False := by
  obtain ⟨_, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

theorem parseSecond_parseThird {H : Hist} {x : List UInt8} {T : Table}
    {sb sb' r₁ r₁' r₂ r₂' c c' t v}
    (h : ParseSecond W H x T sb r₁ r₂ c) (h' : ParseThird W H x T sb' r₁' r₂' c' t v) : False := by
  obtain ⟨_, _, _, _, _, _, _, _, hx, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx', _⟩ := h'
  have := congrArg List.length (hx.symm.trans hx')
  simp at this

end Parse

/-! ## Each fresh query is bad with small probability -/

section Probability

variable {S : Finset (List UInt8)}

/-- **The union bound over a list**: if each of a list's events has probability at most `ε`,
some one of them has probability at most the list's length times `ε`. -/
theorem prEvent_exists_mem_le {α β : Type} (mx : ProbComp α) (E : β → α → Prop) (ε : ℝ≥0∞) :
    ∀ l : List β, (∀ b ∈ l, Pr{let a ← mx}[E b a] ≤ ε) →
      Pr{let a ← mx}[∃ b ∈ l, E b a] ≤ l.length * ε
  | [], _ => by
    rw [prEvent_eq_zero_of_forall_not _ _ fun a h => by simp at h]
    exact bot_le
  | b :: l, h => by
    have hl := prEvent_exists_mem_le mx E ε l fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    refine (prEvent_mono _ _ (fun a => E b a ∨ ∃ b' ∈ l, E b' a) fun a ha => ?_).trans
      ((prEvent_or_le _ _ _).trans ((add_le_add (h b List.mem_cons_self) hl).trans ?_))
    · simpa using ha
    · rw [List.length_cons, Nat.cast_succ, add_mul, one_mul, add_comm]

/-- **A collision has probability at most `(4 |H| + 3) / 2^256`.** -/
theorem prob_coll (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[Coll (histOf c) t.1 (tableOf c g)] ≤
      ((4 * (histOf c).card + 3 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  let Bad : Finset Bytes32 := (histOf c).image (tableOf c g₀) ∪ (insert t.1 (histOf c)).biUnion
    fun y => Finset.univ.filter fun u : Bytes32 => Refers y u
  refine (prEvent_mono _ _ (fun g => g t ∈ Bad) fun g h => ?_).trans ?_
  · rw [← tableOf_fresh c ht g]
    rcases h with ⟨y, hy, hyx⟩ | ⟨y, hy, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨y, hy, by rw [tableOf_eq_of_mem c hy g₀ g, hyx]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, hy, by simpa using h⟩)
  · refine (prEvent_cell t (fun u => u ∈ Bad)).trans ?_
    rw [SampleableType.prEvent_uniformSample, card_bytes32]
    have hc : Bad.card ≤ 4 * (histOf c).card + 3 := by
      refine (Finset.card_union_le _ _).trans ?_
      have h2 := Finset.card_biUnion_le (s := insert t.1 (histOf c)) (t := fun y =>
        Finset.univ.filter fun u : Bytes32 => Refers y u)
      have h3 : ∑ y ∈ insert t.1 (histOf c), (Finset.univ.filter fun u : Bytes32 =>
          Refers y u).card ≤ (insert t.1 (histOf c)).card * 3 := by
        simpa using Finset.sum_le_card_nsmul _ _ 3 fun y _ => card_refers_le y
      have h4 := Finset.card_insert_le t.1 (histOf c)
      have h5 := Finset.card_image_le (s := histOf c) (f := tableOf c g₀)
      nlinarith
    have : ((Finset.univ.filter fun u : Bytes32 => u ∈ Bad).card : ℝ≥0∞) ≤
        ((4 * (histOf c).card + 3 : ℕ) : ℝ≥0∞) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact_mod_cast hc
    rw [Nat.cast_pow, Nat.cast_ofNat]
    gcongr

/-- The candidates read off a cache do not depend on the table's other answers. -/
theorem cands_tableOf {M : Type} (C : ListCommit M) (c : SCache S) (g g' : ↥S → Bytes32)
    (r : Bytes32) : C.cands (histOf c) (tableOf c g) r = C.cands (histOf c) (tableOf c g') r :=
  C.congr _ _ _ r fun _ hd => tableOf_eq_of_mem c hd g g'

/-- The first round's fresh part, for one candidate, has probability at most the round error. -/
theorem prob_freshFirst_one (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) (hlen : t.1.length = 96) (sb : Vector UInt8 64) (gm : B.Msg₁) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[(tableOf c g t.1).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ≠ (tableOf c g t.1).toList ∧
      ¬ State₁ (W.decode sb) gm ∧
      State₂ (W.decode sb) gm (W.chal (tableOf c g t.1),
        W.chal (tableOf c g (tableOf c g t.1).toList),
        W.chal (tableOf c g (tableOf c g (tableOf c g t.1).toList).toList))] ≤
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

theorem le_listFactor_left (L₁ L₂ : ℕ) : L₁ ≤ listFactor L₁ L₂ := le_max_left _ _

theorem le_listFactor_right (L₁ L₂ : ℕ) : L₁ * L₂ ≤ listFactor L₁ L₂ := le_max_right _ _

/-- A pair of candidate lists, union-bounded. -/
theorem prob_pairs (c : SCache S) {r₁ r₂ : Bytes32} (E : B.Msg₁ → B.Msg₂ → (↥S → Bytes32) → Prop)
    (hE : ∀ gm R, Pr{let g ← $ᵗ (↥S → Bytes32)}[E gm R g] ≤ (roundError P B : ℝ≥0∞)) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[∃ gm ∈ C₁.cands (histOf c) (tableOf c g) r₁,
      ∃ R ∈ C₂.cands (histOf c) (tableOf c g) r₂, E gm R g] ≤
      (listFactor C₁.bound C₂.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) := by
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  let l₁ := C₁.cands (histOf c) (tableOf c g₀) r₁
  let l₂ := C₂.cands (histOf c) (tableOf c g₀) r₂
  refine (prEvent_mono _ _ (fun g => ∃ gm ∈ l₁, ∃ R ∈ l₂, E gm R g) fun g h => ?_).trans ?_
  · rwa [cands_tableOf C₁ c g g₀, cands_tableOf C₂ c g g₀] at h
  refine (prEvent_exists_mem_le _ (fun gm g => ∃ R ∈ l₂, E gm R g)
    ((l₂.length : ℝ≥0∞) * (roundError P B : ℝ≥0∞)) l₁ fun gm _ =>
      prEvent_exists_mem_le _ (fun R g => E gm R g) _ l₂ fun R _ => hE gm R).trans ?_
  rw [← mul_assoc]
  gcongr
  have h1 := C₁.length_le (histOf c) (tableOf c g₀) r₁
  have h2 := C₂.length_le (histOf c) (tableOf c g₀) r₂
  exact_mod_cast (Nat.mul_le_mul h1 h2).trans (le_listFactor_right _ _)

/-- **The rounds' bad events have probability at most `max L₁ (L₁ L₂)` times the largest round
error**: the parse is read off the history, so at most one round and one parse are possible,
and the candidates are fixed by the history. -/
theorem prob_round (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[FirstBad W C₁ (histOf c) t.1 (tableOf c g) ∨
      SecondBad W C₁ C₂ (histOf c) t.1 (tableOf c g) ∨
        ThirdBad W C₁ C₂ (histOf c) t.1 (tableOf c g)] ≤
      (listFactor C₁.bound C₂.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) := by
  let g₀ : ↥S → Bytes32 := fun _ => Vector.replicate 32 0
  have hcg : ∀ g, ∀ d ∈ histOf c, tableOf c g d = tableOf c g₀ d := fun g _ hd =>
    tableOf_eq_of_mem c hd g g₀
  by_cases h1 : ∃ sb r₁, ParseFirst W (histOf c) t.1 (tableOf c g₀) sb r₁
  · obtain ⟨sb, r₁, hp⟩ := h1
    have hlen : t.1.length = 96 := by
      obtain ⟨st₀, -, hx, -⟩ := hp
      rw [hx]
      simp
    let l₁ := C₁.cands (histOf c) (tableOf c g₀) r₁
    refine (prEvent_mono _ _ (fun g => ∃ gm ∈ l₁, (tableOf c g t.1).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ∉ histOf c ∧
      (tableOf c g (tableOf c g t.1).toList).toList ≠ (tableOf c g t.1).toList ∧
      ¬ State₁ (W.decode sb) gm ∧
      State₂ (W.decode sb) gm (W.chal (tableOf c g t.1),
        W.chal (tableOf c g (tableOf c g t.1).toList),
        W.chal (tableOf c g (tableOf c g (tableOf c g t.1).toList).toList)))
      fun g h => ?_).trans ?_
    · rcases h with ⟨sb', r₁', hp', hf⟩ | ⟨sb', r₁', r₂', c', hp', -⟩ |
        ⟨sb', r₁', r₂', c', tt, v, hp', -⟩
      · rw [parseFirst_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl⟩ := parseFirst_unique hp' hp
        obtain ⟨f1, f2, f3, gm, hgm, f4, f5⟩ := hf
        rw [cands_tableOf C₁ c g g₀] at hgm
        exact ⟨gm, hgm, f1, f2, f3, f4, f5⟩
      · rw [parseSecond_congr (hcg g)] at hp'
        exact (parseFirst_parseSecond hp hp').elim
      · rw [parseThird_congr (hcg g)] at hp'
        exact (parseFirst_parseThird hp hp').elim
    · refine (prEvent_exists_mem_le _ _ (roundError P B : ℝ≥0∞) l₁ fun gm _ =>
        prob_freshFirst_one W hS₀ c t ht hlen sb gm).trans ?_
      gcongr
      exact_mod_cast (C₁.length_le _ _ _).trans (le_listFactor_left _ _)
  by_cases h2 : ∃ sb r₁ r₂ c', ParseSecond W (histOf c) t.1 (tableOf c g₀) sb r₁ r₂ c'
  · obtain ⟨sb, r₁, r₂, c', hp⟩ := h2
    refine (prEvent_mono _ _ (fun g => ∃ gm ∈ C₁.cands (histOf c) (tableOf c g) r₁,
      ∃ R ∈ C₂.cands (histOf c) (tableOf c g) r₂, ¬ State₃ (W.decode sb) gm c' R ∧
        State₄ (W.decode sb) gm c' R (W.chal (g t))) fun g h => ?_).trans ?_
    · rcases h with ⟨sb', r₁', hp', -⟩ | ⟨sb', r₁', r₂', c'', hp', hf⟩ |
        ⟨sb', r₁', r₂', c'', tt, v, hp', -⟩
      · rw [parseFirst_congr (hcg g)] at hp'
        exact (parseFirst_parseSecond hp' hp).elim
      · rw [parseSecond_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := parseSecond_unique hp' hp
        rwa [tableOf_fresh c ht g] at hf
      · rw [parseThird_congr (hcg g)] at hp'
        exact (parseSecond_parseThird hp hp').elim
    · exact prob_pairs C₁ C₂ c _ fun gm R =>
        (prEvent_cell t (fun u => ¬ State₃ (W.decode sb) gm c' R ∧
          State₄ (W.decode sb) gm c' R (W.chal u))).trans (prob_second_chain W _ gm c' R)
  by_cases h3 : ∃ sb r₁ r₂ c' tt v, ParseThird W (histOf c) t.1 (tableOf c g₀) sb r₁ r₂ c' tt v
  · obtain ⟨sb, r₁, r₂, c', tt, v, hp⟩ := h3
    refine (prEvent_mono _ _ (fun g => ∃ gm ∈ C₁.cands (histOf c) (tableOf c g) r₁,
      ∃ R ∈ C₂.cands (histOf c) (tableOf c g) r₂, ¬ State₄ (W.decode sb) gm c' R tt ∧
        State₆ (W.decode sb) gm c' R tt v (W.chal (g t))) fun g h => ?_).trans ?_
    · rcases h with ⟨sb', r₁', hp', -⟩ | ⟨sb', r₁', r₂', c'', hp', -⟩ |
        ⟨sb', r₁', r₂', c'', tt', v', hp', hf⟩
      · rw [parseFirst_congr (hcg g)] at hp'
        exact (parseFirst_parseThird hp' hp).elim
      · rw [parseSecond_congr (hcg g)] at hp'
        exact (parseSecond_parseThird hp' hp).elim
      · rw [parseThird_congr (hcg g)] at hp'
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := parseThird_unique hp' hp
        rwa [tableOf_fresh c ht g] at hf
    · exact prob_pairs C₁ C₂ c _ fun gm R =>
        (prEvent_cell t (fun u => ¬ State₄ (W.decode sb) gm c' R tt ∧
          State₆ (W.decode sb) gm c' R tt v (W.chal u))).trans
          (prob_third_chain W _ gm c' R tt v)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun g h => ?_]
    · simp
    rcases h with ⟨sb, r₁, hp, -⟩ | ⟨sb, r₁, r₂, c', hp, -⟩ | ⟨sb, r₁, r₂, c', tt, v, hp, -⟩
    · exact h1 ⟨sb, r₁, (parseFirst_congr (hcg g) _ _ _).mp hp⟩
    · exact h2 ⟨sb, r₁, r₂, c', (parseSecond_congr (hcg g) _ _ _ _ _).mp hp⟩
    · exact h3 ⟨sb, r₁, r₂, c', tt, v, (parseThird_congr (hcg g) _ _ _ _ _ _ _).mp hp⟩

/-- **A fresh query is bad with probability at most
`(4 |H| + 3) / 2^256 + max L₁ (L₁ L₂) · roundError`.** -/
theorem prob_listBad (hS₀ : ∀ v : Bytes32, v.toList ∈ S) (c : SCache S) (t : ↥S)
    (ht : c t = none) :
    Pr{let g ← $ᵗ (↥S → Bytes32)}[listBad W C₁ C₂ (histOf c) t.1 (tableOf c g)] ≤
      ((4 * (histOf c).card + 3 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (listFactor C₁.bound C₂.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) :=
  (prEvent_or_le _ _ _).trans (add_le_add (prob_coll c t ht) (prob_round W C₁ C₂ hS₀ c t ht))

end Probability

end Compose
