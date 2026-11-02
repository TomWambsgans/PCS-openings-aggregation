-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.F1Step
import Soundness.MerkleWord
import Soundness.Replay

/-!
# The Statement's extractor finds a secret when Compose's list holds a witness

Compose's extractor in the random-permutation model (`rpmExtractor`: `adversaryExtractor` on the
setup's log and the adversary's Keccak-256 evaluations, the deployed witness decoder
`witnessDecoder`: mumbai's `decodeStacks` on the Merkle word, each stack's table read as F1's first
message, `readW`) returns a list; the Statement's (`PcsQuotient.extractor`) a secret. Here:
**if some message of Compose's list satisfies F1's relation for the statement, the Statement's
extractor returns a secret of the statement**, on the same evaluations (the setup tree's, then the
transcript's):

* the Statement's word, read through its hash maps, is mumbai's `committedLeaves` on the setup's and
  the transcript's evaluations (`Replay.lean`, `witnessWord_eq_committed`);
* the two Merkle words agree on every column (`MerkleWord.lean`), so the two `decodeStacks` lists
  have the same members (`mem_decodeStacks_congr`: both are mumbai's Johnson candidates of the
  word, `mem_decodeColumns`, and the candidates read the code's columns only, `candidates_congr`);
* a stack whose read message satisfies the relation proves membership (`provesMembership_of_sat`)
  and so spells a secret of the statement (`ReadsSecret`, the bridge's);
* the Statement's extractor returns the first candidate's secret that satisfies the relation, the
  fast path's first (`fastStacks`), then the unique decoder's (`uniqueStacks`), then the list
  decoder's: whichever it returns satisfies the relation, and it returns one since the list
  decoder's list, last, holds such a stack (`orElse_spec`, `findSome_spec`). Nothing is needed of the
  first two stages: they only return earlier.
-/

set_option linter.unusedSectionVars false

-- The membership circuit is a closed term of `2^22` rows, and its cells an additive transform of
-- `2^24` entries: never evaluate them (no simprocs here, which would try to decide the relation).
attribute [local irreducible] PcsQuotient.membershipBuilder PcsQuotient.secretOfStack
set_option simprocs false

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge
open LeanVM.Protocol.EndToEnd

/-! ## Lists -/

/-- A list's find, when every find satisfies `p`, satisfies `p`. -/
theorem findSome_sat {α β : Type} (l : List α) (f : α → Option β) (p : β → Prop)
    (hf : ∀ a b, f a = some b → p b) : ∀ b, l.findSome? f = some b → p b := fun b h ↦ by
  obtain ⟨a, -, hfa⟩ := List.exists_of_findSome?_eq_some h
  exact hf a b hfa

/-- A list with a find has a find satisfying `p`, when every find satisfies `p`. -/
theorem findSome_spec {α β : Type} (l : List α) (f : α → Option β) (p : β → Prop)
    (hf : ∀ a b, f a = some b → p b) (h : ∃ a ∈ l, (f a).isSome) :
    ∃ b, l.findSome? f = some b ∧ p b := by
  obtain ⟨a, ha, hfa⟩ := h
  rcases h₂ : l.findSome? f with _ | b
  · exact absurd hfa (by rw [List.findSome?_eq_none_iff.mp h₂ a ha]; simp)
  · exact ⟨b, rfl, findSome_sat l f p hf b h₂⟩

/-- The first of two options, the second if the first is none: when the first satisfies `p` if it
is some, and the second is some satisfying `p`, some satisfying `p`. -/
theorem orElse_spec {β : Type} (o₁ o₂ : Option β) (p : β → Prop)
    (h₁ : ∀ b, o₁ = some b → p b) (h₂ : ∃ b, o₂ = some b ∧ p b) :
    ∃ b, (o₁ <|> o₂) = some b ∧ p b := by
  rcases o₁ with _ | b
  · simpa using h₂
  · exact ⟨b, rfl, h₁ b rfl⟩

/-! ## The decoder's members -/

/-- mumbai's `decodeStacks` lists the same stacks for two words that agree on the code's columns. -/
theorem mem_decodeStacks_congr {μ R : ℕ} (hw : Whir.Admissible μ R) {W W' : Word}
    (h : ∀ v < 2 ^ (μ - laneBits + R), W v = W' v) (st : Vector K (2 ^ μ))
    (hst : st ∈ LeanVM.Extraction.decodeStacks μ R W) :
    st ∈ LeanVM.Extraction.decodeStacks μ R W' := by
  have h1 : (Column.mk st : Column μ) ∈ decodeColumns μ R W := List.mem_map.mpr ⟨st, hst, rfl⟩
  rw [mem_decodeColumns hw, candidates_congr h] at h1
  rw [← mem_decodeColumns hw] at h1
  obtain ⟨st', hst', he⟩ := List.mem_map.mp h1
  rwa [← column_mk_injective μ he]

/-- **What the deployed witness decoder lists**: the tables of the stacks `decodeStacks` lists for
the Merkle word, read as F1's first message. -/
theorem mem_witnessDecoder_dec (I : Instance E) (c : Consts)
    (w : Fin (2 ^ (witnessDecoder I c).height) → Option (List UInt8)) (g : I.bounds.Msg₁)
    (hg : g ∈ (witnessDecoder I c).dec w) :
    ∃ st ∈ LeanVM.Extraction.decodeStacks (witnessLayout 22).logN logInvRate
        (wordOfMerkle (rootHeight (witnessLayout 22).logN logInvRate) (2 ^ WhirBridge.laneFold) w),
      readW I (tabOf (witnessLayout 22) ⟨st⟩) = g := by
  have h1 : (witnessDecoder I c).dec w =
      (merkleTables (deployD c 22).Lw (deployD c 22).R w).map (readW I) :=
    tableCode_dec _ _ _ _ w
  rw [h1] at hg
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hg
  unfold merkleTables decodeTables decodeColumns at hX
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hX
  obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hq
  exact ⟨st, hst, rfl⟩

/-! ## The Statement's extractor -/

theorem logRows_finish (lr : ℕ) (pw : List (List PcsQuotient.Src)) (b : PcsQuotient.Builder) :
    (PcsQuotient.finish lr pw b).logRows = lr := rfl

/-- The membership circuit has `2^22` rows (its builder is not run). -/
theorem membership_logRows : (PcsQuotient.membership PcsQuotient.logRows).logRows = 22 := by
  unfold PcsQuotient.membership
  exact logRows_finish _ _ _

/-- **The Statement's extractor returns a secret** when its word is `W` and the list decoder lists a
stack spelling a secret of the statement: any circuit of `2^n` rows, `n` a variable, so that nothing
of the circuit, the word or the stacks' sizes is computed. The fast path's and the unique decoder's
candidates are tried first; whatever they return satisfies the relation. -/
theorem extractFrom_spec (n : ℕ) (circuit : PcsQuotient.Circuit) (hlog : circuit.logRows = n)
    (stmt : PcsQuotient.Statement) (pre : Digest → ℕ → Option (List UInt8))
    (proof : PcsQuotient.Proof) (W : ℕ → List K)
    (hw : PcsQuotient.witnessWord n pre proof = some W)
    (st : Vector K (2 ^ (PcsQuotient.cellVars n + 1)))
    (hst : st ∈ LeanVM.Extraction.decodeStacks (PcsQuotient.cellVars n + 1)
      PcsQuotient.logInvRate W)
    (hrel : PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit st)) :
    ∃ w, PcsQuotient.extractFrom circuit stmt pre proof = some w ∧
      PcsQuotient.Relation stmt w := by
  unfold PcsQuotient.extractFrom
  rw [hlog, hw, Option.bind_eq_bind, Option.bind_some]
  have hf : ∀ (a : Vector K (2 ^ (PcsQuotient.cellVars n + 1))) b,
      (let w := PcsQuotient.secretOfStack circuit a
        if PcsQuotient.Relation stmt w then some w else none) = some b →
        PcsQuotient.Relation stmt b := fun a b hab => by
    by_cases hr : PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit a)
    · simp only [ite_eq_left hr] at hab
      cases hab
      exact hr
    · simp only [ite_eq_right hr] at hab
      cases hab
  refine orElse_spec _ _ _ (findSome_sat _ _ _ hf) (orElse_spec _ _ _ (findSome_sat _ _ _ hf)
    (findSome_spec _ _ _ hf ⟨st, hst, ?_⟩))
  show (if PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit st) then
    some (PcsQuotient.secretOfStack circuit st) else none).isSome = true
  rw [ite_eq_left hrel]
  rfl

/-- **If Compose's list holds a witness, the Statement's extractor finds a secret.** For a proof
whose witness root's scalars are the digest `d`: a message of Compose's extractor's list, on the
evaluations `setupEvals` then those of the transcript `T`, whose cells satisfy F1's relation for
the statement, makes the Statement's extractor, on the same setup evaluations and transcript,
return a secret of the statement. -/
theorem extractor_of_mem (c : Consts) (h : IsCantor c.beta) (hX : ReadsSecret c h)
    (stmt : PcsQuotient.Statement) (proof : PcsQuotient.Proof) (d : Digest)
    (hd : digestOfScalars proof.reduction.witnessRoot = some d)
    (setupEvals : List (List UInt8 × Digest)) (T : Common.OracleQueryLog)
    (g : (inst c h).bounds.Msg₁)
    (hg : g ∈ adversaryExtractor (witnessDecoder (inst c h) c)
      (trOf (setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)))
      (rootProofOf stmt proof))
    (hs : (inst c h).params.Sat ((deployedWire (inst c h)).decode (rootProofOf stmt proof).stmt)
      ((inst c h).params.cells g.1)) :
    ∃ w, PcsQuotient.extractor stmt setupEvals T proof = some w ∧ PcsQuotient.Relation stmt w := by
  set paths := setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T) with hpaths
  have hr₁ : (rootProofOf stmt proof).r₁ = toB d := by simp [rootProofOf, hd]
  unfold adversaryExtractor at hg
  rw [hr₁] at hg
  obtain ⟨st, hst, rfl⟩ := mem_witnessDecoder_dec (inst c h) c _ g hg
  have hadm : Whir.Admissible (witnessLayout 22).logN logInvRate :=
    (layouts_ok 22 rows_ok.1 rows_ok.2).1
  have hlogN : (witnessLayout 22).logN = 25 := rfl
  have hst' : st ∈ LeanVM.Extraction.decodeStacks 25 1
      (LeanVM.Extraction.leafAt (LeanVM.Extraction.committedLeaves
        (LeanVM.lookupEvaluation paths) (paths.map (·.1)) d 20 (2 ^ WhirBridge.laneFold)) 20
          (2 ^ WhirBridge.laneFold)) := by
    refine mem_decodeStacks_congr hadm (fun v hv => ?_) st hst
    have hv' : v < 2 ^ 20 := by
      have : (witnessLayout 22).logN - laneBits + logInvRate = 20 := by
        rw [hlogN]; rfl
      rwa [this] at hv
    exact wordOfMerkle_merkleWord_eq paths d 20 (2 ^ WhirBridge.laneFold) hv'
  have hrel : PcsQuotient.Relation stmt
      (PcsQuotient.secretOfStack (PcsQuotient.membership PcsQuotient.logRows) st) :=
    hX stmt ⟨st⟩ (provesMembership_of_sat c h stmt _ hs)
  unfold PcsQuotient.extractor PcsQuotient.transcriptExtractorFor
  exact extractFrom_spec 22 _ membership_logRows stmt _ proof _
    (Replay.witnessWord_eq_committed setupEvals T proof d hd) st hst' hrel

end Soundness
