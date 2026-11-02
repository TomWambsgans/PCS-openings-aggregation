-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The bad-query engine for dependent answer types (`prEvent_randomOracle_le_of_freshBad_dep`)
-- generalises `formal/QuotientRpm/FreshBad.lean`'s `prEvent_randomOracle_le_of_freshBad`, which
-- follows VCVio's `prEvent_randomOracle_le_of_bad_queries` (https://github.com/Verified-zkEVM/VCVio,
-- commit afa6593f, Apache-2.0). The model is leanerVM `mumbai`'s (https://github.com/Verified-zkEVM/leanerVM,
-- commit 6175f1a0, MIT OR Apache-2.0): `KeccakCalls`, `callKeccak256`, `Digest.toRpm`.
import Compose.Openings
import LeanVM.Protocol.WithHash
import Common.Lanes

/-!
# The composition in mumbai's two-oracle model

F2's `family_sound` lives in leanerVM `mumbai`'s random-oracle model `KeccakCalls`: Keccak-256
(`Bytes → Digest`, queries `.inl x`) and Keccak-f[1600] (`KeccakState → KeccakState`, queries
`.inr s`), two independent lazily sampled oracles. This file moves the reduction's list argument
there, so that the chain, the Merkle trees and the openings are answered by **one** oracle model:

* **the engine** (`prEvent_randomOracle_le_of_freshBad_dep`): `QuotientRpm`'s bad-fresh-query
  bound for answer types that depend on the input (`KeccakCalls` is `Sum.elim` of the two);
* **the view** (`viewT`, `viewH`): Keccak-256's answers as 32 bytes (`Digest.toRpm`), on the
  Keccak-256 inputs; a query is bad when it is Keccak-256's and `listBad` of the view
  (`kcBad`); Keccak-f's queries are never bad (`freshBad_kc`);
* **the pushforward** (`prEvent_view`): a uniform table of both oracles on a finite set, read
  through the view, is a uniform table of 32-byte answers on its Keccak-256 inputs; so each
  fresh query is bad with probability at most `listBad`'s bound (`prob_kcBad`);
* **the experiment** (`kcExperiment`): the adversary, the chain over Keccak-256
  (`hash256`), then any computation of both oracles (the openings), with the transcript of the
  Keccak-256 queries (`loggedKC`).

**`knowledgeSoundness_list_kc`** and **`knowledgeSoundness_composed_kc`**: the bounds of
`ListChain.lean` and `Openings.lean`, in mumbai's model.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params

/-! ## The engine, for answers whose type depends on the input -/

/-- The uniform table on a finite set of inputs, for dependent answer types. -/
noncomputable local instance instSampleablePiSubtype {D : Type} {R : D → Type} [∀ d, Fintype (R d)]
    [∀ d, Nonempty (R d)] (S : Finset D) : SampleableType ((d : ↥S) → R d.1) :=
  SampleableType.piOfFintype _

section Engine

variable {D : Type} {R : D → Type} [DecidableEq D]

theorem isTotalQueryBound_restrictQueries_dep [∀ d, Finite (R d)] (S : Finset D) {α : Type}
    (oa : OracleComp (OracleSpec.ofFn R) α) (h : AllQueriesSatisfy oa (· ∈ S)) :
    ∀ n, IsTotalQueryBound oa n → IsTotalQueryBound (restrictQueries S oa h) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; trivial
  | query_bind t k ih =>
    intro n hb
    exact ⟨hb.1, fun u => ih u (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) _ (hb.2 u)⟩

omit [DecidableEq D] in
theorem restrictCache_empty_dep (S : Finset D) :
    restrictCache S (∅ : (OracleSpec.ofFn R).QueryCache) = ∅ := by
  ext d
  rfl

variable [∀ d, Fintype (R d)] [∀ d, Nonempty (R d)] [∀ d, SampleableType (R d)]

/-- **Bad fresh queries bound an event of the lazily sampled oracle, for dependent answer
types**: `QuotientRpm.prEvent_randomOracle_le_of_freshBad` with `R d` in place of one type. -/
theorem prEvent_randomOracle_le_of_freshBad_dep {α : Type}
    (oa : OracleComp (OracleSpec.ofFn R) α) (n : ℕ) (hn : IsTotalQueryBound oa n) (S₀ : Set D)
    (hS₀ : S₀.Finite) (event : α → Prop) (bad : Finset D → D → (∀ d, R d) → Prop) (ε : ℝ≥0∞)
    (hbad : ∀ S : Finset D, (∀ d ∈ S₀, d ∈ S) →
      ∀ (c : (OracleSpec.ofFn fun d : ↥S => R d.1).QueryCache) (t : ↥S),
        c t = none → (cacheDom c).card < n →
        Pr{let g ← $ᵗ ((d : ↥S) → R d.1)}[bad ((cacheDom c).map
          (Function.Embedding.subtype (· ∈ S))) t.1 (extendTable S (completeTable c g))] ≤ ε)
    (htrace : ∀ T : (∀ d, R d), event (evalWithAnswerFn (QueryImpl.ofFn T) oa) →
      FreshBad bad T ∅ ((tableQueryLog oa T).map Sigma.fst)) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤ n * ε := by
  classical
  let S := possibleQueryKeys oa ∪ hS₀.toFinset
  have hS : AllQueriesSatisfy oa (· ∈ S) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun d hd => Finset.mem_union_left _ hd
  let small := restrictQueries S oa hS
  have hrun : (simulateQ randomOracle small).run' ∅ = (simulateQ randomOracle oa).run' ∅ := by
    rw [← randomOracle_restrictQueries S oa hS ∅, restrictCache_empty_dep]
  rw [← hrun]
  let : MeasurableSpace α := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable small ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq event]
  simp only [prEvent_norm]
  let e : ↥S ↪ D := Function.Embedding.subtype (· ∈ S)
  let bad' : Finset ↥S → ↥S → ((d : ↥S) → R d.1) → Prop := fun H' x' g' =>
    bad (H'.map e) x'.1 (extendTable S g')
  have htrace' : ∀ g : (d : ↥S) → R d.1, event (evalWithAnswerFn (QueryImpl.ofFn g) small) →
      FreshBadRun bad' small g ∅ := by
    intro g hev
    have hg : (fun d : ↥S => extendTable S g d.1) = g := funext (extendTable_subtype S g)
    have heval := evalWithAnswerFn_restrictQueries S oa hS (extendTable S g)
    rw [hg] at heval
    have h := htrace (extendTable S g) (heval ▸ hev)
    have hlog := tableQueryLog_restrictQueries S oa hS (extendTable S g)
    rw [hg] at hlog
    rw [← hlog, List.map_map] at h
    have hm : (Sigma.fst ∘ fun q : (Σ d : ↥S, R d.1) => (⟨q.1.1, q.2⟩ : Σ d : D, R d)) =
        e ∘ Sigma.fst := rfl
    rw [hm, ← List.map_map, show (∅ : Finset D) = (∅ : Finset ↥S).map e from rfl] at h
    have h' := (freshBad_map e bad (extendTable S) g ∅ _).mp h
    simp only [FreshBadRun, completeTable_empty, cacheDom_empty]
    exact h'
  refine (prEvent_mono _ _ _ htrace').trans ?_
  exact prEvent_freshBad_le (D := ↥S) (R := fun d => R d.1) bad' ε n
    (fun c t hct hcard => hbad S (fun d hd => Finset.mem_union_right _ (hS₀.mem_toFinset.mpr hd))
      c t hct hcard) small n (isTotalQueryBound_restrictQueries_dep S oa hS n hn) ∅ (by simp)

end Engine

/-! ## Keccak-256's answers as 32 bytes -/

open LeanVM LeanVM.Protocol LeanVM.Semantics

/-- A digest as its 32 bytes (mumbai's `Digest.toRpm`). -/
abbrev toB (d : Digest) : Bytes32 := LeanVM.Rpm.Digest.toRpm d

theorem toB_injective : Function.Injective toB := LeanVM.Rpm.digestEquiv.injective

/-- A table of both oracles. -/
abbrev KTable := (d : List UInt8 ⊕ KeccakState) → KeccakCalls d

/-- Keccak-256's answers, as 32 bytes. -/
def viewT (T : KTable) : Table := fun x => toB (T (.inl x))

/-- The Keccak-256 inputs of a set of queries. -/
noncomputable def viewH (H : Finset (List UInt8 ⊕ KeccakState)) : Hist :=
  H.preimage Sum.inl Sum.inl_injective.injOn

@[simp] theorem mem_viewH {H : Finset (List UInt8 ⊕ KeccakState)} {x : List UInt8} :
    x ∈ viewH H ↔ Sum.inl x ∈ H := Finset.mem_preimage

theorem viewH_insert_inl (H : Finset (List UInt8 ⊕ KeccakState)) (x : List UInt8) :
    viewH (insert (Sum.inl x) H) = insert x (viewH H) := by
  ext y
  simp

theorem viewH_insert_inr (H : Finset (List UInt8 ⊕ KeccakState)) (s : KeccakState) :
    viewH (insert (Sum.inr s) H) = viewH H := by
  ext y
  simp

@[simp] theorem viewH_empty : viewH (∅ : Finset (List UInt8 ⊕ KeccakState)) = ∅ := by
  ext y
  simp

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) (C₁ : ListCommit B.Msg₁)
  (C₂ : ListCommit B.Msg₂)

/-- **A bad query of both oracles**: a Keccak-256 query bad for the view; never a Keccak-f
query. -/
def kcBad (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) :
    Prop :=
  match d with
  | .inl x => listBad W C₁ C₂ (viewH H) x (viewT T)
  | .inr _ => False

/-- A bad fresh Keccak-256 input of the view is a bad fresh query. -/
theorem freshBad_kc (T : KTable) : ∀ (H : Finset (List UInt8 ⊕ KeccakState))
    (L : List (List UInt8 ⊕ KeccakState)),
    FreshBad (listBad W C₁ C₂) (viewT T) (viewH H) (L.filterMap Sum.getLeft?) →
      FreshBad (kcBad W C₁ C₂) T H L
  | _, [], h => by simp [FreshBad] at h
  | H, .inl x :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, FreshBad] at h ⊢
    rcases h with ⟨hx, hb⟩ | h
    · exact Or.inl ⟨fun hm => hx (mem_viewH.mpr hm), hb⟩
    · refine Or.inr (freshBad_kc T _ L ?_)
      rwa [viewH_insert_inl]
  | H, .inr s :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, FreshBad] at h ⊢
    refine Or.inr (freshBad_kc T _ L ?_)
    rwa [viewH_insert_inr]

/-- `listBad` reads the table on the inputs asked, at the fresh input, and at the 32-byte
inputs (the states the first round's lookahead hashes). -/
theorem listBad_congr {H : Hist} {x : List UInt8} {T T' : Table} (hH : ∀ d ∈ H, T d = T' d)
    (hx : T x = T' x) (hs : ∀ v : Bytes32, T v.toList = T' v.toList) :
    listBad W C₁ C₂ H x T ↔ listBad W C₁ C₂ H x T' := by
  have hc₁ : ∀ r, C₁.cands H T r = C₁.cands H T' r := fun r => C₁.congr H T T' r hH
  have hc₂ : ∀ r, C₂.cands H T r = C₂.cands H T' r := fun r => C₂.congr H T T' r hH
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
  unfold listBad FirstBad SecondBad ThirdBad ParseFirst FreshFirst ParseSecond ParseThird
  simp only [hcoll, hx, hs, hc₁, hc₂, has_congr hH, injOn_congr hH]

/-! ## A uniform table of both oracles, read through the view -/

section View

variable (S : Finset (List UInt8 ⊕ KeccakState))

/-- The Keccak-f inputs of a finite set of queries. -/
noncomputable def inrPart : Finset KeccakState := S.preimage Sum.inr Sum.inr_injective.injOn

/-- A table of both oracles on `S`, read on its Keccak-256 inputs as 32 bytes. -/
def viewG (g : (d : ↥S) → KeccakCalls d.1) : ↥(viewH S) → Bytes32 :=
  fun x => toB (g ⟨.inl x.1, mem_viewH.mp x.2⟩)

/-- A cache of both oracles on `S`, read on its Keccak-256 inputs as 32 bytes. -/
def viewC (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) : SCache (viewH S) :=
  .ofFn fun x : ↥(viewH S) => (c ⟨.inl x.1, mem_viewH.mp x.2⟩).map toB

/-- Glue a table of both oracles from its Keccak-256 part `y` (as digests) and its Keccak-f
part `b`. -/
def glue (y : ↥(viewH S) → Bytes32) (b : (s : ↥(inrPart S)) → KeccakState) :
    (d : ↥S) → KeccakCalls d.1 := fun d =>
  Sum.casesOn (motive := fun e => e ∈ S → KeccakCalls e) d.1
    (fun x h => LeanVM.Digest.ofRpm (y ⟨x, mem_viewH.mpr h⟩))
    (fun s h => b ⟨s, Finset.mem_preimage.mpr h⟩) d.2

theorem viewG_glue (y : ↥(viewH S) → Bytes32) (b : (s : ↥(inrPart S)) → KeccakState) :
    viewG S (glue S y b) = y := by
  funext x
  exact LeanVM.Rpm.digestToRpm_ofRpm _

/-- The fibres of the view: a table of both oracles reading as `y` is `y` on Keccak-256's inputs
and anything on Keccak-f's. -/
def viewFiber (y : ↥(viewH S) → Bytes32) :
    {g : (d : ↥S) → KeccakCalls d.1 // viewG S g = y} ≃
      ((s : ↥(inrPart S)) → KeccakState) where
  toFun g := fun s => g.1 ⟨.inr s.1, Finset.mem_preimage.mp s.2⟩
  invFun b := ⟨glue S y b, viewG_glue S y b⟩
  left_inv g := by
    obtain ⟨g, hg⟩ := g
    refine Subtype.ext (funext fun d => ?_)
    obtain ⟨d, h⟩ := d
    cases d with
    | inl x =>
      show LeanVM.Digest.ofRpm (y ⟨x, _⟩) = g ⟨.inl x, h⟩
      rw [← hg]
      exact LeanVM.Rpm.digestOfRpm_toRpm _
    | inr s => rfl
  right_inv b := rfl

/-- **A uniform table of both oracles, read through the view, is a uniform table of 32-byte
answers on the Keccak-256 inputs.** -/
theorem prEvent_view (E : (↥(viewH S) → Bytes32) → Prop) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[E (viewG S g)] =
      Pr{let h ← $ᵗ (↥(viewH S) → Bytes32)}[E h] := by
  classical
  refine prEvent_uniform_balanced (viewG S) (Fintype.card ((s : ↥(inrPart S)) → KeccakState))
    (fun y => ?_) E
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (viewFiber S y)

variable {S}

theorem histOf_viewC (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) :
    histOf (viewC S c) = viewH ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) := by
  ext x
  constructor
  · intro hm
    obtain ⟨h, hc⟩ := mem_histOf.mp hm
    refine mem_viewH.mpr (Finset.mem_map.mpr ⟨⟨.inl x, mem_viewH.mp h⟩,
      mem_cacheDom.mpr fun h' => hc ?_, rfl⟩)
    simp [viewC, h']
  · intro hm
    obtain ⟨⟨d, hd⟩, hmem, hde⟩ := Finset.mem_map.mp (mem_viewH.mp hm)
    simp only [Function.Embedding.subtype_apply] at hde
    subst hde
    refine mem_histOf.mpr ⟨mem_viewH.mpr hd, fun h' => mem_cacheDom.mp hmem ?_⟩
    simpa [viewC] using h'

theorem viewT_extendTable (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache)
    (g : (d : ↥S) → KeccakCalls d.1) {x : List UInt8} (hx : x ∈ viewH S) :
    viewT (extendTable S (completeTable c g)) x = tableOf (viewC S c) (viewG S g) x := by
  have e1 : viewT (extendTable S (completeTable c g)) x =
      toB (completeTable c g ⟨.inl x, mem_viewH.mp hx⟩) :=
    congrArg toB (extendTable_subtype S (completeTable c g) ⟨.inl x, mem_viewH.mp hx⟩)
  refine e1.trans (Eq.trans ?_ (tableOf_subtype (viewC S c) (viewG S g) ⟨x, hx⟩).symm)
  show toB ((c ⟨.inl x, _⟩).getD (g ⟨.inl x, _⟩)) =
    (((c ⟨.inl x, _⟩).map toB)).getD (toB (g ⟨.inl x, _⟩))
  cases c ⟨.inl x, mem_viewH.mp hx⟩ <;> rfl

end View

/-- **Each fresh query of both oracles is bad with probability at most
`(4 |H| + 3) / 2^256 + max L₁ (L₁ L₂) · roundError`.** -/
theorem prob_kcBad (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[kcBad W C₁ C₂
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((4 * (cacheDom c).card + 3 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (listFactor C₁.bound C₂.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) := by
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
    have hx : x ∈ viewH S := mem_viewH.mpr hd
    have hS₁ : ∀ v : Bytes32, v.toList ∈ viewH S := fun v => mem_viewH.mpr (hS₀ v)
    have hc₁ : viewC S c ⟨x, hx⟩ = none := by simp [viewC, ht]
    have hH : histOf (viewC S c) ⊆ viewH S := fun y hy => (mem_histOf.mp hy).1
    -- The event, read through the view.
    have hev : ∀ g, kcBad W C₁ C₂ ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) (.inl x)
        (extendTable S (completeTable c g)) ↔
        listBad W C₁ C₂ (histOf (viewC S c)) x (tableOf (viewC S c) (viewG S g)) := by
      intro g
      show listBad W C₁ C₂ _ x _ ↔ _
      rw [← histOf_viewC]
      exact listBad_congr W C₁ C₂ (fun y hy => viewT_extendTable c g (hH hy))
        (viewT_extendTable c g hx) (fun v => viewT_extendTable c g (hS₁ v))
    refine (prEvent_mono _ _ (fun g => listBad W C₁ C₂ (histOf (viewC S c)) x
      (tableOf (viewC S c) (viewG S g))) fun g h => (hev g).mp h).trans ?_
    rw [prEvent_view S (fun h => listBad W C₁ C₂ (histOf (viewC S c)) x (tableOf (viewC S c) h))]
    refine (prob_listBad W C₁ C₂ hS₁ (viewC S c) ⟨x, hx⟩ hc₁).trans ?_
    gcongr
    have hcard : (histOf (viewC S c)).card ≤ (cacheDom c).card := by
      rw [histOf_viewC]
      refine (Finset.card_le_card_of_injOn
        (t := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))) Sum.inl (fun y hy => ?_)
        Sum.inl_injective.injOn).trans (Finset.card_map (Function.Embedding.subtype (· ∈ S))).le
      exact mem_viewH.mp hy
    omega

/-! ## The experiment in mumbai's model -/

/-- Every entry of a run's log against a table holds the table's answer. -/
theorem tableQueryLog_snd_dep {D : Type} {R : D → Type} {α : Type} (T : ∀ d, R d)
    (oa : OracleComp (OracleSpec.ofFn R) α) : ∀ q ∈ tableQueryLog oa T, q.2 = T q.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro q hq
    rw [tableQueryLog_query_bind] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact ih _ q hq

/-- Keccak-256 as the chain reads it: the digest's 32 bytes. -/
def hash256 (x : List UInt8) : OracleComp KeccakCalls Bytes32 :=
  callKeccak256 x >>= fun u => pure (toB u)

/-- A Keccak-256 query's transcript entry, its answer as 32 bytes; nothing for Keccak-f. -/
def inlEntry (q : (d : List UInt8 ⊕ KeccakState) × KeccakCalls d) :
    Option (List UInt8 × Bytes32) :=
  match q with
  | ⟨.inl x, u⟩ => some (x, toB u)
  | ⟨.inr _, _⟩ => none

/-- Both oracles, logging every Keccak-256 query and its answer. -/
def logImplKC : QueryImpl KeccakCalls (StateT Transcript (OracleComp KeccakCalls)) := fun d l =>
  (fun u => (u, l ++ (inlEntry ⟨d, u⟩).toList)) <$> liftM (KeccakCalls.query d)

/-- A computation of both oracles with the transcript of its Keccak-256 queries. -/
def loggedKC {α : Type} (oa : OracleComp KeccakCalls α) :
    OracleComp KeccakCalls (α × Transcript) :=
  (simulateQ logImplKC oa).run []

theorem loggedKC_run_query_bind {α : Type} (d : List UInt8 ⊕ KeccakState)
    (k : KeccakCalls d → OracleComp KeccakCalls α) (l : Transcript) :
    (simulateQ logImplKC (liftM (KeccakCalls.query d) >>= k)).run l =
      liftM (KeccakCalls.query d) >>= fun u =>
        (simulateQ logImplKC (k u)).run (l ++ (inlEntry ⟨d, u⟩).toList) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((fun u => (u, l ++ (inlEntry ⟨d, u⟩).toList)) <$> liftM (KeccakCalls.query d)) >>= _ = _
  rw [bind_map_left]

theorem eval_loggedKC_run {α : Type} (T : KTable) (oa : OracleComp KeccakCalls α) :
    ∀ l : Transcript, evalWithAnswerFn (QueryImpl.ofFn T) ((simulateQ logImplKC oa).run l) =
      (evalWithAnswerFn (QueryImpl.ofFn T) oa, l ++ (tableQueryLog oa T).filterMap inlEntry) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro l; simp
  | query_bind t k ih =>
    intro l
    rw [loggedKC_run_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, ih,
      evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, tableQueryLog_query_bind]
    simp only [QueryImpl.ofFn_apply, List.filterMap_cons, List.append_assoc]
    cases h : inlEntry ⟨t, T t⟩ <;> simp

theorem log_loggedKC_run {α : Type} (T : KTable) (oa : OracleComp KeccakCalls α) :
    ∀ l : Transcript, tableQueryLog ((simulateQ logImplKC oa).run l) T = tableQueryLog oa T := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro l; simp
  | query_bind t k ih =>
    intro l
    rw [loggedKC_run_query_bind, tableQueryLog_query_bind, tableQueryLog_query_bind, ih]

theorem isTotalQueryBound_loggedKC_run {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ (n : ℕ) (l : Transcript), IsTotalQueryBound oa n →
      IsTotalQueryBound ((simulateQ logImplKC oa).run l) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n l _; simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind t k ih =>
    intro n l hn
    obtain ⟨hn1, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rw [loggedKC_run_query_bind]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun u => ih u (n - 1) _ (hk u)⟩

variable {O β : Type}

/-- **The run in mumbai's model**: the adversary, the chain over Keccak-256 on its reduction
proof, then `post` (the openings, any computation of both oracles). -/
def kcRun (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Run F O β) :=
  A >>= fun p => chainWith W hash256 p.1 >>= fun ch => post p ch >>= fun b =>
    pure ⟨p.1, p.2, ch, b⟩

/-- **The experiment in mumbai's model**: the run, with the transcript of its Keccak-256
queries, the adversary's, the chain's and the openings'. -/
def kcExperiment (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Run F O β × Transcript) :=
  loggedKC (kcRun W A post)

theorem chain_queryBound_kc (π : RootProof F) : IsTotalQueryBound (chainWith W hash256 π) 6 := by
  simp only [chainWith, hash256, callKeccak256, bind_assoc, pure_bind]
  repeat' (first | trivial | refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => ?_⟩)

theorem kcExperiment_queryBound (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (kcExperiment W A post) (Q + 6 + QV) := by
  refine isTotalQueryBound_loggedKC_run _ _ _ ?_
  have h : ∀ p : RootProof F × O, IsTotalQueryBound (chainWith W hash256 p.1 >>= fun ch =>
      post p ch >>= fun b => (pure ⟨p.1, p.2, ch, b⟩ : OracleComp KeccakCalls (Run F O β)))
        (6 + (QV + 0)) :=
    fun p => isTotalQueryBound_bind (chain_queryBound_kc W p.1) fun ch =>
      isTotalQueryBound_bind (hV p ch) fun b =>
        (trivial : IsTotalQueryBound (pure ⟨p.1, p.2, ch, b⟩ : OracleComp KeccakCalls (Run F O β)) 0)
  have := isTotalQueryBound_bind hQ h
  rwa [Nat.add_zero, ← Nat.add_assoc] at this

/-- The run against a table of both oracles. -/
theorem kcRun_run (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (T : KTable) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let x₀ := W.label p.1.stmt
    let x₁ := Wire.afterRoot (viewT T x₀) p.1.r₁
    let x₂ := (viewT T x₁).toList
    let x₃ := (viewT T x₂).toList
    let x₄ := Wire.afterRoot (viewT T x₃) p.1.r₂
    let x₅ := W.afterValues (viewT T x₄) p.1.v
    let ch : Chals F := ⟨W.chal (viewT T x₁), W.chal (viewT T x₂), W.chal (viewT T x₃),
      W.chal (viewT T x₄), W.chal (viewT T x₅)⟩
    (tableQueryLog (kcRun W A post) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          ([.inl x₀, .inl x₁, .inl x₂, .inl x₃, .inl x₄, .inl x₅] ++
            (tableQueryLog (post p ch) T).map Sigma.fst) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (kcRun W A post) =
        ⟨p.1, p.2, ch, evalWithAnswerFn (QueryImpl.ofFn T) (post p ch)⟩ := by
  intro p x₀ x₁ x₂ x₃ x₄ x₅ ch
  constructor
  · simp only [kcRun, chainWith, hash256, callKeccak256, bind_assoc, pure_bind,
      tableQueryLog_bind, tableQueryLog_pure, List.map_append, List.append_nil,
      evalWithAnswerFn_liftM_query]
    rfl
  · simp only [kcRun, chainWith, hash256, callKeccak256, bind_assoc, pure_bind,
      evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl

theorem map_fst_filterMap_inlEntry (l : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d)) :
    (l.filterMap inlEntry).map Prod.fst = (l.map Sigma.fst).filterMap Sum.getLeft? := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨d, u⟩ := q
    cases d with
    | inl x => simp [inlEntry, ih]
    | inr s =>
      rw [List.filterMap_cons_none (rfl : inlEntry ⟨.inr s, u⟩ = none), ih]
      rfl

theorem filterMap_getLeft?_map_inl {α γ : Type} (l : List α) :
    (l.map (Sum.inl : α → α ⊕ γ)).filterMap Sum.getLeft? = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

open Classical in
/-- **The trace in mumbai's model**: on every table of both oracles, a winning run asks a bad
fresh query. -/
theorem trace_kc (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (T : KTable)
    (hwin : ListWins W C₁ C₂ (evalWithAnswerFn (QueryImpl.ofFn T) (kcExperiment W A post))) :
    FreshBad (kcBad W C₁ C₂) T ∅ ((tableQueryLog (kcExperiment W A post) T).map Sigma.fst) := by
  obtain ⟨hL, heval⟩ := kcRun_run W A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set π := p.1
  have hlogE := log_loggedKC_run T (kcRun W A post) []
  have hevalE := eval_loggedKC_run T (kcRun W A post) []
  rw [List.nil_append] at hevalE
  unfold kcExperiment loggedKC
  rw [hlogE]
  unfold kcExperiment loggedKC at hwin
  rw [hevalE, heval] at hwin
  set lg := tableQueryLog (kcRun W A post) T
  set L := (lg.map Sigma.fst).filterMap Sum.getLeft?
  set tr : Transcript := lg.filterMap inlEntry
  have htrH : histOfTr tr = L.toFinset := by
    simp only [histOfTr, tr, L, map_fst_filterMap_inlEntry]
  have htrT : ∀ d ∈ histOfTr tr, tableOfTr tr d = viewT T d := by
    intro d hd
    refine tableOfTr_eq (viewT T) tr (fun e he => ?_) d (by simpa [histOfTr] using hd)
    obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he
    obtain ⟨d', u⟩ := q
    cases d' with
    | inl x =>
      simp only [inlEntry, Option.some.injEq] at hqe
      subst hqe
      have := tableQueryLog_snd_dep T _ _ hq
      simp only at this
      simp [viewT, this]
    | inr s => simp [inlEntry] at hqe
  obtain ⟨g, hg, R, hR, hacc, hsat⟩ := hwin
  simp only at hg hR hacc hsat
  rw [C₁.congr _ _ _ _ htrT, htrH] at hg
  rw [C₂.congr _ _ _ _ htrT, htrH] at hR
  have hcore := trace_core W C₁ C₂ L (viewT T) π g R (fun y hy => by
    simp only [L, hL, List.filterMap_append]
    refine List.mem_append_right _ (List.mem_append_left _ ?_)
    rw [show ∀ (a b c d e f : List UInt8), [(Sum.inl a : List UInt8 ⊕ KeccakState), .inl b, .inl c,
        .inl d, .inl e, .inl f] = [a, b, c, d, e, f].map Sum.inl from fun _ _ _ _ _ _ => rfl,
      filterMap_getLeft?_map_inl]
    exact hy) hg hR hacc hsat
  have := freshBad_kc W C₁ C₂ T ∅ (lg.map Sigma.fst) (by rw [viewH_empty]; exact hcore)
  exact this

/-- **The reduction's knowledge soundness with real roots, union-bounded over the lists, in
mumbai's two-oracle model.** `knowledgeSoundness_list` with Keccak-256 and Keccak-f[1600]
independent random oracles, the chain on Keccak-256, the openings any computation of both. -/
theorem knowledgeSoundness_list_kc (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (kcExperiment W A post)).run' ∅}[ListWins W C₁ C₂ z] ≤
      ((Q + 6 + QV : ℕ) : ℝ≥0∞) * ((listFactor C₁.bound C₂.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) + 4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (kcExperiment W A post)
    (Q + 6 + QV) (kcExperiment_queryBound W A post Q QV hQ hV)
    (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
    (Set.finite_range _) (ListWins W C₁ C₂) (kcBad W C₁ C₂) _ (fun S hS c t ht hcard => ?_)
    (fun T h => trace_kc W C₁ C₂ A post T h)
  have hS' : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
    fun v => hS _ ⟨v, rfl⟩
  refine (prob_kcBad W C₁ C₂ S hS' c t ht).trans ?_
  rw [add_comm]
  gcongr
  have : 4 * (cacheDom c).card + 3 ≤ 4 * (Q + 6 + QV) := by omega
  calc ((4 * (cacheDom c).card + 3 : ℕ) : ℝ≥0∞) ≤ ((4 * (Q + 6 + QV) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast this
    _ = 4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) := by push_cast; ring

end Compose
