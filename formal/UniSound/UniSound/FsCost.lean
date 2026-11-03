-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows
-- `formal/EndToEnd/Soundness/Cost.lean` of this repository (its `allQ_ourVerifier`, and leanerVM
-- `mumbai`'s cost lemmas, https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR
-- Apache-2.0: `Short`, `hashBlocks_le_of_short`, `isWeightBound_of_isTotalQueryBound`).
import UniSound.FsProof
import Soundness.Cost

/-!
# The composed verifier's calls of `π`

`UniNumbers.verifier` from the rounds' sizes: the composed verifier (the chain over the univariate
encoding, then the five openings) makes at most `nQ + Σ QO` queries, each **short** (at most
`2^39 + 9` bytes, so at most `2^32` calls of `π`): the seed's input is `80` bytes, a step's at most
`32 + 24 + 32 + 24 nv` with `nv ≤ 2^30` scalars a round; an opening's one claim of at most `28`
coordinates (`Soundness.allQ_ourVerifier`). So at most `(2^10 + 5 · 10122) · 2^32 ≤ 2^80`
(**`uniNumbers_of`**).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile WhirBridge UniStatement
open OracleSpec OracleComp
open LeanVM.Rpm (Short hashBlocks)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

theorem allQ_hash256 {x : List UInt8} (hx : x.length ≤ 2 ^ 39 + 9) :
    AllQueriesSatisfy (hash256 x) Short :=
  allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryH hx) fun _ => LeanVM.Rpm.allQ_pure _

theorem allQ_runM : ∀ (y : List UInt8) (es : List (List UInt8)), y.length ≤ 2 ^ 39 + 9 →
    (∀ e ∈ es, 32 + e.length ≤ 2 ^ 39 + 9) → AllQueriesSatisfy (runM hash256 y es) Short
  | y, [], hy, _ => allQueriesSatisfy_bind (allQ_hash256 hy) fun _ => LeanVM.Rpm.allQ_pure _
  | y, e :: es, hy, he => allQueriesSatisfy_bind (allQ_hash256 hy) fun st =>
      allQueriesSatisfy_bind (allQ_runM (stepIn st e) es (by
        rw [length_stepIn]
        exact he e List.mem_cons_self) fun e' he' => he e' (List.mem_cons_of_mem _ he'))
        fun _ => LeanVM.Rpm.allQ_pure _

theorem isTotalQueryBound_opsRun {Pf F M St : Type} (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)),
      IsTotalQueryBound (opsRun view ops π ch) (ops.map fun o => o.S.QO).sum
  | [], _, _ => trivial
  | o :: os, π, ch => by
    simp only [opsRun, List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind (o.S.queries _) fun _ =>
      (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_opsRun view os π ch)

theorem allQ_opsRun {Pf F M St : Type} (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)),
      (∀ o ∈ ops, (o.cl π ch).claims.length ≤ 2 ∧ o.S.L.vars ≤ 2 ^ 30) →
        AllQueriesSatisfy (opsRun view ops π ch) Short
  | [], _, _, _ => trivial
  | o :: os, π, ch, h => by
    simp only [opsRun]
    refine allQueriesSatisfy_bind (Soundness.allQ_ourVerifier _ _ _ (h o List.mem_cons_self).1
      (h o List.mem_cons_self).2) fun _ => ?_
    rw [map_eq_bind_pure_comp]
    exact allQueriesSatisfy_bind (allQ_opsRun view os π ch fun o' ho' =>
      h o' (List.mem_cons_of_mem _ ho')) fun _ => LeanVM.Rpm.allQ_pure _

theorem mkStmt_length_le (L : WhirBridge.Layout) (hL : L.extra = []) (cs : List WhirBridge.Claim) :
    (mkStmt L hL cs).claims.length ≤ 1 := by
  unfold mkStmt
  split_ifs with h
  · exact h.1
  · simp

theorem length_uniEnc (m : RMsg E) : (uniEnc m).length ≤ 32 + 24 * m.2.length := by
  unfold uniEnc
  split <;> simp

/-- The bytes a step absorbs: at most `24 + 32 + 24 B` for messages of at most `B` scalars. -/
theorem length_mem_absorbsI (s : FSt) (B : ℕ) : ∀ (i : ℕ) (rs : List RoundSpec)
    (ms : List (RMsg E)), (∀ m ∈ ms, m.2.length ≤ B) →
      ∀ e ∈ absorbsI ((uniSpec rs).encAt s) i rs ms, e.length ≤ 24 + 32 + 24 * B
  | _, [], _, _, e, he => by simp [absorbsI] at he
  | i, r :: rs, ms, hm, e, he => by
    simp only [absorbsI, List.mem_cons, List.mem_append, List.mem_replicate] at he
    rcases he with rfl | ⟨-, rfl⟩ | he
    · have hB : (ms.headD (none, [])).2.length ≤ B := by
        rcases ms with _ | ⟨m, ms⟩
        · simp
        · exact hm m List.mem_cons_self
      have h1 := length_uniEnc (ms.headD (none, []))
      have h2 : 24 * (ms.headD (none, [])).2.length ≤ 24 * B := Nat.mul_le_mul_left 24 hB
      unfold ChainSpecU.encAt
      have he : ((uniSpec (r :: rs)).enc (ms.headD (none, []))).length =
          (uniEnc (ms.headD (none, []))).length := rfl
      split_ifs
      · rw [List.length_append]
        have hp : ((uniSpec (r :: rs)).pre s).length = 24 := by
          show s.2.2.toList.length = 24
          simp
        omega
      · omega
    · simp
    · exact length_mem_absorbsI s B (i + 1) rs ms.tail
        (fun m hm' => hm m (List.mem_of_mem_tail hm')) e he

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)
  (hs : UniShapes D)

/-- **The composed verifier's calls of `π`**: at most `2^80`, when the chain asks at most `2^10`
queries and every round sends at most `2^30` scalars. -/
theorem uniNumbers_of (hnQ : (uSpec Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds Fl nV V, r.nv ≤ 2 ^ 30) : UniNumbers D Fl nV V C hs := by
  refine ⟨hnQ, fun π => ?_⟩
  have htot : IsTotalQueryBound (verU (uSpec Fl nV V) (uView (uRounds Fl nV V))
      (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)) π)
      ((uSpec Fl nV V).K.nQ + ((uOps D Fl nV V C hs).map fun o => o.S.QO).sum) := by
    unfold verU
    exact isTotalQueryBound_bind (isTotalQueryBound_chainU _ _ _) fun ch =>
      isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_opsRun _ _ _ _) fun _ => trivial
  have hmsg : ∀ m ∈ (uView (uRounds Fl nV V) π).2, m.2.length ≤ 2 ^ 30 := by
    intro m hm
    have hfit := fitsAll_uView (uRounds Fl nV V) π
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    have hl := hfit.length_eq
    have := fitsAll_getD hfit i (by omega)
    have hi' : i < (uRounds Fl nV V).length := by omega
    rw [List.getD_eq_getElem _ _ hi] at this
    rw [this.2, List.getD_eq_getElem _ _ hi']
    exact hnv _ (List.getElem_mem hi')
  have hops : ∀ ch, ∀ o ∈ uOps D Fl nV V C hs,
      (o.cl π ch).claims.length ≤ 2 ∧ o.S.L.vars ≤ 2 ^ 30 := by
    intro ch o ho
    simp only [uOps, uniOps, List.mem_cons, List.mem_nil_iff, or_false] at ho
    have hk : ∀ k < 5, wv D k ≤ 2 ^ 30 := fun k hk => (hs.hi k hk).trans (by norm_num)
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 0 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 1 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 2 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 3 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 4 (by decide)⟩
  have hall : AllQueriesSatisfy (verU (uSpec Fl nV V) (uView (uRounds Fl nV V))
      (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)) π) Short := by
    unfold verU ChainSpecU.chain
    rw [map_eq_bind_pure_comp, bind_assoc]
    refine allQueriesSatisfy_bind (allQ_runM _ _ ?_ ?_) fun sts => ?_
    · show (uniLabel _).length ≤ _
      simp [uniLabel, name_length]
    · intro e he
      have := length_mem_absorbsI _ (2 ^ 30) 0 _ _ hmsg e he
      omega
    · simp only [Function.comp_apply, pure_bind]
      exact allQueriesSatisfy_bind (allQ_opsRun _ _ _ _ (hops _)) fun _ => LeanVM.Rpm.allQ_pure _
  have hq := sumQO_le D Fl nV V C hs
  refine (LeanVM.Rpm.isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) htot
    (hall.mono fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)).mono ?_
  have h80 : (2 ^ 10 + 5 * 10122) * 2 ^ 32 ≤ (2 : ℕ) ^ 80 := by norm_num
  exact (Nat.mul_le_mul_right _ (by omega)).trans h80

/-- **The Fiat–Shamir layer from the game bridge**, the numbers being the chain's `< 2^10` queries and
every round's `≤ 2^30` scalars. -/
theorem fsLayer_of_game' (hnQ : (uSpec Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds Fl nV V, r.nv ≤ 2 ^ 30) (hG : UniGameLe D Fl nV V C hs) :
    FsLayer D Fl nV V C :=
  fsLayer_of_game D Fl nV V C hs (uniNumbers_of D Fl nV V C hs hnQ hnv) hG

end UniSound

/-- info: 'UniSound.uniNumbers_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniNumbers_of

/-- info: 'UniSound.fsLayer_of_game'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer_of_game'

