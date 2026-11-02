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

end Compose
