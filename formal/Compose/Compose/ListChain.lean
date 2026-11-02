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

**`knowledgeSoundness_list`**: an adversary of at most `Q` queries outputs a statement, two roots,
five values and anything else (the openings), and the verifier runs the chain and then any
computation `post` of at most `QV` queries (the openings' verifier); the chain's challenges make
some pair of candidates of the two roots, read off the transcript of every query, satisfy the
verifier's claims while the witness candidate's cells fail the relation with probability at most
`(Q + 6 + QV) (max L₁ (L₁ L₂) · roundError + 4 (Q + 6 + QV) / 2^256)`.

The transcript is in the experiment's output (`logged`: the hash, logging every query and its
answer), so the event, and the extractor, read it.
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

/-- **A run**: the adversary's reduction proof and the rest of what it outputs (the openings), the
chain's challenges, and what the verifier computes after the chain (the openings' verdicts). -/
structure Run (F O β : Type) where
  proof : RootProof F
  rest : O
  chals : Chals F
  out : β

/-- **The run**: the adversary, the chain on its reduction proof, then `post` (the openings, any
computation of the hash). -/
def rootRun {O β : Type} (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) :
    OracleComp HashSpec (Run F O β) :=
  A >>= fun p => chainWith W hashQuery p.1 >>= fun ch => post p ch >>= fun b =>
    pure ⟨p.1, p.2, ch, b⟩

/-- **The experiment**: the run, with the transcript of every query, the adversary's, the
chain's and the openings'. -/
def rootExperiment {O β : Type} (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) :
    OracleComp HashSpec (Run F O β × Transcript) :=
  logged (rootRun W A post)

/-- **What wins**: some candidate of the first root and some candidate of the second, read off the
transcript, satisfy the claims the verifier checks at the chain's challenges, while the first's
cells fail the relation for the statement. -/
def ListWins {O β : Type} (C₁ : ListCommit B.Msg₁) (C₂ : ListCommit B.Msg₂)
    (z : Run F O β × Transcript) : Prop :=
  ∃ g ∈ C₁.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.r₁,
    ∃ R ∈ C₂.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.r₂,
      P.Accepts (W.decode z.1.proof.stmt) g.1 R.1 z.1.chals.α z.1.chals.β z.1.chals.γ z.1.chals.t
          z.1.proof.v.1 z.1.proof.v.2 z.1.chals.ρ ∧ ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)

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

/-! ## The transcript of a run -/

section Log

/-- Every entry of a run's log against a table holds the table's answer. -/
theorem tableQueryLog_snd {α : Type} (T : Table) (oa : OracleComp HashSpec α) :
    ∀ q ∈ tableQueryLog oa T, q.2 = T q.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro q hq
    rw [tableQueryLog_query_bind] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact ih _ q hq

theorem logged_run_pure {α : Type} (a : α) (l : Transcript) :
    (simulateQ logImpl (pure a : OracleComp HashSpec α)).run l = pure (a, l) := by
  simp

theorem logged_run_query_bind {α : Type} (t : List UInt8) (k : Bytes32 → OracleComp HashSpec α)
    (l : Transcript) :
    (simulateQ logImpl (liftM (HashSpec.query t) >>= k)).run l =
      hashQuery t >>= fun u => (simulateQ logImpl (k u)).run (l ++ [(t, u)]) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((fun u => (u, l ++ [(t, u)])) <$> hashQuery t) >>= _ = _
  rw [bind_map_left]

/-- **What the logged run computes**: the run's result, and its log appended. -/
theorem eval_logged_run {α : Type} (T : Table) (oa : OracleComp HashSpec α) :
    ∀ l : Transcript, evalWithAnswerFn (QueryImpl.ofFn T) ((simulateQ logImpl oa).run l) =
      (evalWithAnswerFn (QueryImpl.ofFn T) oa,
        l ++ (tableQueryLog oa T).map fun q => (q.1, q.2)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro l; simp
  | query_bind t k ih =>
    intro l
    rw [logged_run_query_bind, hashQuery, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      ih, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, tableQueryLog_query_bind]
    simp

/-- The logged run asks what the run asks. -/
theorem log_logged_run {α : Type} (T : Table) (oa : OracleComp HashSpec α) :
    ∀ l : Transcript, tableQueryLog ((simulateQ logImpl oa).run l) T = tableQueryLog oa T := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro l; simp
  | query_bind t k ih =>
    intro l
    rw [logged_run_query_bind, hashQuery, tableQueryLog_query_bind, tableQueryLog_query_bind, ih]

theorem isTotalQueryBound_logged_run {α : Type} (oa : OracleComp HashSpec α) :
    ∀ (n : ℕ) (l : Transcript), IsTotalQueryBound oa n →
      IsTotalQueryBound ((simulateQ logImpl oa).run l) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n l _; rw [logged_run_pure]; trivial
  | query_bind t k ih =>
    intro n l hn
    obtain ⟨hn1, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rw [logged_run_query_bind, hashQuery]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun u => ih u (n - 1) _ (hk u)⟩

/-- A transcript's table answers as the table that answered it, on the inputs it asks. -/
theorem tableOfTr_eq (T : Table) : ∀ tr : Transcript, (∀ e ∈ tr, e.2 = T e.1) →
    ∀ x ∈ tr.map Prod.fst, tableOfTr tr x = T x
  | [], _, x, hx => by simp at hx
  | e :: tr, h, x, hx => by
    by_cases hex : e.1 = x
    · have hp : decide (e.1 = x) = true := decide_eq_true hex
      have hf : (e :: tr).find? (fun e' => decide (e'.1 = x)) = some e :=
        List.find?_cons_of_pos (p := fun e' : List UInt8 × Bytes32 => decide (e'.1 = x)) (l := tr) hp
      show (((e :: tr).find? fun e' => decide (e'.1 = x)).map Prod.snd).getD _ = T x
      rw [hf, Option.map_some, Option.getD_some, h e List.mem_cons_self, hex]
    · have hx' : x ∈ tr.map Prod.fst := by
        rcases List.mem_cons.mp hx with h' | h'
        · exact absurd h'.symm hex
        · exact h'
      have hp : ¬ decide (e.1 = x) = true := fun h' => hex (of_decide_eq_true h')
      have hf : (e :: tr).find? (fun e' => decide (e'.1 = x)) =
          tr.find? (fun e' => decide (e'.1 = x)) :=
        List.find?_cons_of_neg (p := fun e' : List UInt8 × Bytes32 => decide (e'.1 = x)) (l := tr) hp
      have := tableOfTr_eq T tr (fun e' he' => h e' (List.mem_cons_of_mem _ he')) x hx'
      show (((e :: tr).find? fun e' => decide (e'.1 = x)).map Prod.snd).getD _ = T x
      rw [hf]
      exact this

end Log

/-! ## An accepted run of a false statement makes a fresh query bad -/

section Trace

theorem chain_queryBound (π : RootProof F) : IsTotalQueryBound (chainWith W hashQuery π) 6 := by
  simp only [chainWith, hashQuery]
  repeat' (first | trivial | refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => ?_⟩)

variable {O β : Type}

theorem rootRun_queryBound (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (rootRun W A post) (Q + 6 + QV) := by
  have h : ∀ p : RootProof F × O, IsTotalQueryBound (chainWith W hashQuery p.1 >>= fun ch =>
      post p ch >>= fun b => (pure ⟨p.1, p.2, ch, b⟩ : OracleComp HashSpec (Run F O β)))
        (6 + (QV + 0)) :=
    fun p => isTotalQueryBound_bind (chain_queryBound W p.1) fun ch =>
      isTotalQueryBound_bind (hV p ch) fun b =>
        (trivial : IsTotalQueryBound (pure ⟨p.1, p.2, ch, b⟩ : OracleComp HashSpec (Run F O β)) 0)
  have := isTotalQueryBound_bind hQ h
  rwa [Nat.add_zero, ← Nat.add_assoc] at this

theorem rootExperiment_queryBound (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (rootExperiment W A post) (Q + 6 + QV) :=
  isTotalQueryBound_logged_run _ _ _ (rootRun_queryBound W A post Q QV hQ hV)

/-- The run against a table: the adversary's output, the chain's challenges, the verdict after,
and the chain's six inputs between the adversary's queries and the openings'. -/
theorem rootRun_run (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) (T : Table) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let x₀ := W.label p.1.stmt
    let x₁ := Wire.afterRoot (T x₀) p.1.r₁
    let x₂ := (T x₁).toList
    let x₃ := (T x₂).toList
    let x₄ := Wire.afterRoot (T x₃) p.1.r₂
    let x₅ := W.afterValues (T x₄) p.1.v
    let ch : Chals F := ⟨W.chal (T x₁), W.chal (T x₂), W.chal (T x₃), W.chal (T x₄), W.chal (T x₅)⟩
    (tableQueryLog (rootRun W A post) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          ([x₀, x₁, x₂, x₃, x₄, x₅] ++ (tableQueryLog (post p ch) T).map Sigma.fst) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (rootRun W A post) =
        ⟨p.1, p.2, ch, evalWithAnswerFn (QueryImpl.ofFn T) (post p ch)⟩ := by
  intro p x₀ x₁ x₂ x₃ x₄ x₅ ch
  constructor
  · simp only [rootRun, chainWith, hashQuery, tableQueryLog_bind, tableQueryLog_pure,
      List.map_append, List.append_nil, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl
  · simp only [rootRun, chainWith, hashQuery, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl

/-- The experiment against a table: the run's result and its transcript. -/
theorem rootExperiment_run (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) (T : Table) :
    tableQueryLog (rootExperiment W A post) T = tableQueryLog (rootRun W A post) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (rootExperiment W A post) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (rootRun W A post),
          (tableQueryLog (rootRun W A post) T).map fun q => (q.1, q.2)) := by
  refine ⟨log_logged_run T _ [], ?_⟩
  have := eval_logged_run T (rootRun W A post) []
  rw [List.nil_append] at this
  exact this

open Classical in
/-- **The trace, on a log**: if the log holds the chain's six inputs, and some candidate pair of the
two roots, read off the log, satisfies the verifier's claims at the chain's challenges while the
witness candidate's cells fail the relation, then some fresh input of the log is bad. -/
theorem trace_core (L : List (List UInt8)) (T : Table) (π : RootProof F) (g : B.Msg₁)
    (R : B.Msg₂) :
    let x₀ := W.label π.stmt
    let x₁ := Wire.afterRoot (T x₀) π.r₁
    let x₂ := (T x₁).toList
    let x₃ := (T x₂).toList
    let x₄ := Wire.afterRoot (T x₃) π.r₂
    let x₅ := W.afterValues (T x₄) π.v
    (∀ y ∈ [x₀, x₁, x₂, x₃, x₄, x₅], y ∈ L) → g ∈ C₁.cands L.toFinset T π.r₁ →
      R ∈ C₂.cands L.toFinset T π.r₂ →
      P.Accepts (W.decode π.stmt) g.1 R.1 (W.chal (T x₁)) (W.chal (T x₂)) (W.chal (T x₃))
        (W.chal (T x₄)) π.v.1 π.v.2 (W.chal (T x₅)) →
      ¬ P.Sat (W.decode π.stmt) (P.cells g.1) → FreshBad (listBad W C₁ C₂) T ∅ L := by
  intro x₀ x₁ x₂ x₃ x₄ x₅ mem hg hR hacc hsat
  by_contra hnb
  have nb : ∀ y ∈ L, ¬ listBad W C₁ C₂ (before L y) y T := fun y hy => by
    simpa using not_bad_before (listBad W C₁ C₂) T ∅ L hnb y hy (Finset.notMem_empty _)
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
  have m0 := mem x₀ (by simp)
  have m1 := mem x₁ (by simp)
  have m2 := mem x₂ (by simp)
  have m3 := mem x₃ (by simp)
  have m4 := mem x₄ (by simp)
  have m5 := mem x₅ (by simp)
  have take32 : ∀ st : Bytes32, st.toList.take 32 = st.toList := fun st =>
    List.take_of_length_le (by simp)
  -- The chain's inputs come in their order.
  have b01 : x₀ ∈ before L x₁ := hord x₀ m0 x₁ m1 (Or.inl (Wire.take_afterRoot _ _).symm)
  have b12 : x₁ ∈ before L x₂ := hord x₁ m1 x₂ m2 (Or.inl (take32 _).symm)
  have b23 : x₂ ∈ before L x₃ := hord x₂ m2 x₃ m3 (Or.inl (take32 _).symm)
  have b34 : x₃ ∈ before L x₄ := hord x₃ m3 x₄ m4 (Or.inl (Wire.take_afterRoot _ _).symm)
  have b45 : x₄ ∈ before L x₅ := hord x₄ m4 x₅ m5 (Or.inl (W.take_afterValues _ _).symm)
  have s12 := before_subset_of_mem L x₁ x₂ b12
  have s23 := before_subset_of_mem L x₂ x₃ b23
  have s34 := before_subset_of_mem L x₃ x₄ b34
  have s45 := before_subset_of_mem L x₄ x₅ b45
  have c04 : x₀ ∈ before L x₄ := s34 (s23 (s12 b01))
  have c14 : x₁ ∈ before L x₄ := s34 (s23 b12)
  have c24 : x₂ ∈ before L x₄ := s34 b23
  -- After a root is absorbed, its candidates are the ones the history already fixed.
  have stab : ∀ {M : Type} (C : ListCommit M) (r : Bytes32) (y z : List UInt8), y ∈ L →
      Refers y r → (y = z ∨ y ∈ before L z) → C.cands L.toFinset T r = C.cands (before L z) T r := by
    intro M C r y z hy hry hyz
    have hsub : ∀ w, w ∈ before L y → w ∈ before L z := by
      rcases hyz with rfl | h
      · exact fun w hw => hw
      · exact fun w hw => before_subset_of_mem L y z h hw
    refine C.stable (before L z) L.toFinset T r (fun w hw => List.mem_toFinset.mpr
      (mem_of_mem_before L w z hw)) (fun w hw hwr => ?_) (fun y' hy' w hw h => ?_)
    · rw [← hwr] at hry
      exact hsub w (hord w (List.mem_toFinset.mp hw) y hy hry)
    · exact before_subset_of_mem L y' z hy' (hord w (List.mem_toFinset.mp hw) y'
        (mem_of_mem_before L y' z hy') h)
  have hr₁ : Refers x₁ π.r₁ := Or.inr (Or.inr (Wire.rootPart_afterRoot _ _).symm)
  have hr₂ : Refers x₄ π.r₂ := Or.inr (Or.inr (Wire.rootPart_afterRoot _ _).symm)
  have g1 : g ∈ C₁.cands (before L x₁) T π.r₁ := by
    rwa [stab C₁ π.r₁ x₁ x₁ m1 hr₁ (Or.inl rfl)] at hg
  have g4 : g ∈ C₁.cands (before L x₄) T π.r₁ := by
    rwa [stab C₁ π.r₁ x₁ x₄ m1 hr₁ (Or.inr c14)] at hg
  have g5 : g ∈ C₁.cands (before L x₅) T π.r₁ := by
    rwa [stab C₁ π.r₁ x₁ x₅ m1 hr₁ (Or.inr (s45 c14))] at hg
  have R4 : R ∈ C₂.cands (before L x₄) T π.r₂ := by
    rwa [stab C₂ π.r₂ x₄ x₄ m4 hr₂ (Or.inl rfl)] at hR
  have R5 : R ∈ C₂.cands (before L x₅) T π.r₂ := by
    rwa [stab C₂ π.r₂ x₄ x₅ m4 hr₂ (Or.inr b45)] at hR
  -- The round that the existing proof's trace names.
  let π' : Proof P B := ⟨W.decode π.stmt, g, R, π.v⟩
  let tbl : ∀ k, Answer P B k := fun k => match k with
    | .first .. => (W.chal (T x₁), W.chal (T x₂), W.chal (T x₃))
    | .second .. => W.chal (T x₄)
    | .third .. => W.chal (T x₅)
  rcases bad_of_accepts π' tbl hacc hsat with hb | hb | hb
  · obtain ⟨h1, h2⟩ := hb
    refine nb x₁ m1 (Or.inr (Or.inl ⟨π.stmt, π.r₁, ⟨T x₀, ⟨b01, rfl⟩, rfl, injB x₁⟩,
      ⟨fun h => not_mem_before_of_mem_before b12 h, fun h => ?_, fun h => ?_, g, g1, h1, h2⟩⟩))
    · exact not_mem_before_of_mem_before (s23 b12) h
    · have e : x₃ = x₂ := h
      rw [e] at b23
      exact not_mem_before_self L x₂ b23
  · obtain ⟨h1, h2⟩ := hb
    exact nb x₄ m4 (Or.inr (Or.inr (Or.inl ⟨π.stmt, π.r₁, π.r₂, _, ⟨T x₀, T x₁, T x₂, T x₃,
      ⟨c04, rfl⟩, ⟨c14, rfl⟩, ⟨c24, rfl⟩, ⟨b34, rfl⟩, rfl, rfl, injB x₄⟩, g, g4, R, R4, h1, h2⟩)))
  · obtain ⟨h1, h2⟩ := hb
    exact nb x₅ m5 (Or.inr (Or.inr (Or.inr ⟨π.stmt, π.r₁, π.r₂, _, _, π.v,
      ⟨T x₀, T x₁, T x₂, T x₃, T x₄, ⟨s45 c04, rfl⟩, ⟨s45 c14, rfl⟩, ⟨s45 c24, rfl⟩,
        ⟨s45 b34, rfl⟩, ⟨b45, rfl⟩, rfl, rfl, rfl, injB x₅⟩, g, g5, R, R5, h1, h2⟩)))

open Classical in
/-- **The trace**: on every table, a winning run asks a bad fresh query. -/
theorem trace_listBad (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) (T : Table)
    (hwin : ListWins W C₁ C₂ (evalWithAnswerFn (QueryImpl.ofFn T) (rootExperiment W A post))) :
    FreshBad (listBad W C₁ C₂) T ∅
      ((tableQueryLog (rootExperiment W A post) T).map Sigma.fst) := by
  obtain ⟨hlogE, hevalE⟩ := rootExperiment_run W A post T
  obtain ⟨hL, heval⟩ := rootRun_run W A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set π := p.1
  set x₀ := W.label π.stmt
  set x₁ := Wire.afterRoot (T x₀) π.r₁
  set x₂ := (T x₁).toList
  set x₃ := (T x₂).toList
  set x₄ := Wire.afterRoot (T x₃) π.r₂
  set x₅ := W.afterValues (T x₄) π.v
  set L := (tableQueryLog (rootRun W A post) T).map Sigma.fst
  rw [hlogE]
  rw [hevalE, heval] at hwin
  -- The transcript's candidates are the table's on the inputs asked.
  set tr : Transcript := (tableQueryLog (rootRun W A post) T).map fun q => (q.1, q.2)
  have htrH : histOfTr tr = L.toFinset := by
    simp only [histOfTr, tr, L, List.map_map]
    rfl
  have htrT : ∀ d ∈ histOfTr tr, tableOfTr tr d = T d := by
    intro d hd
    refine tableOfTr_eq T tr (fun e he => ?_) d (by simpa [histOfTr] using hd)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact tableQueryLog_snd T _ q hq
  obtain ⟨g, hg, R, hR, hacc, hsat⟩ := hwin
  simp only at hg hR hacc hsat
  rw [C₁.congr _ _ _ _ htrT, htrH] at hg
  rw [C₂.congr _ _ _ _ htrT, htrH] at hR
  exact trace_core W C₁ C₂ L T π g R (fun y hy => by
    rw [hL]
    exact List.mem_append_right _ (List.mem_append_left _ hy)) hg hR hacc hsat

end Trace

/-! ## Knowledge soundness with real roots -/

/-- **The reduction's knowledge soundness with real roots, union-bounded over the lists, in the
random-oracle model.** For every adversary making at most `Q` queries of the random oracle
`H : bytes → 32 bytes` that outputs a statement, two roots, five values and anything else (the
openings), and every computation `post` after the chain of at most `QV` queries (the openings'
verifier), the probability that some candidate of the first root and some candidate of the second
(read off the transcript of every query, by any list commitment) satisfy the verifier's claims at
the chain's challenges while the first's cells fail the relation is at most
`(Q + 6 + QV) (max L₁ (L₁ L₂) · roundError + 4 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_list {O β : Type} (A : OracleComp HashSpec (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp HashSpec β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (rootExperiment W A post)).run' ∅}[ListWins W C₁ C₂ z] ≤
      ((Q + 6 + QV : ℕ) : ℝ≥0∞) * ((listFactor C₁.bound C₂.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) + 4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine prEvent_randomOracle_le_of_freshBad (rootExperiment W A post) (Q + 6 + QV)
    (rootExperiment_queryBound W A post Q QV hQ hV) (Set.range fun v : Bytes32 => v.toList)
    (Set.finite_range _) (ListWins W C₁ C₂) (listBad W C₁ C₂) _ (fun S hS c t ht hcard => ?_)
    (fun T h => trace_listBad W C₁ C₂ A post T h)
  have hS' : ∀ v : Bytes32, v.toList ∈ S := fun v => hS _ ⟨v, rfl⟩
  refine (prob_listBad W C₁ C₂ hS' c t ht).trans ?_
  have hcard' : (histOf c).card < Q + 6 + QV := by
    simpa [histOf, Finset.card_map] using hcard
  rw [add_comm]
  gcongr
  have : 4 * (histOf c).card + 3 ≤ 4 * (Q + 6 + QV) := by omega
  calc ((4 * (histOf c).card + 3 : ℕ) : ℝ≥0∞) ≤ ((4 * (Q + 6 + QV) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast this
    _ = 4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) := by push_cast; ring

end Compose
