-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.F1Step
import Soundness.MerkleWord

/-!
# The Statement's extractor finds a secret when Compose's list holds a witness

Compose's extractor in the random-permutation model (`rpmExtractor`: `adversaryExtractor` on the
setup's log and the adversary's Keccak-256 evaluations, the deployed witness decoder
`witnessDecoder`: mumbai's `decodeStacks` on the Merkle word, each stack's table read as F1's first
message, `readW`) returns a list; the Statement's (`PcsQuotient.extractor`) a secret. Here:
**if some message of Compose's list satisfies F1's relation for the statement, the Statement's
extractor returns a secret of the statement**, on the same evaluations (the setup tree's, then the
transcript's):

* the two Merkle words agree on every column (`MerkleWord.lean`), so the two `decodeStacks` lists
  have the same members (`mem_decodeStacks_congr`: both are mumbai's Johnson candidates of the
  word, `mem_decodeColumns`, and the candidates read the code's columns only, `candidates_congr`);
* a stack whose read message satisfies the relation proves membership (`provesMembership_of_sat`)
  and so spells a secret of the statement (`ReadsSecret`, the bridge's);
* the Statement's extractor returns the first candidate's secret that satisfies the relation, the
  fast path's first (`fastStacks`), then the list decoder's: whichever it returns satisfies the
  relation, and it returns one since the list decoder's list holds such a stack
  (`findSome_orElse`).
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

/-- The first of two lists' finds, the second's if the first finds nothing: when every find
satisfies `p` and the second list has a find, a find satisfying `p`. -/
theorem findSome_orElse {α β : Type} (l₁ l₂ : List α) (f : α → Option β) (p : β → Prop)
    (hf : ∀ a b, f a = some b → p b) (h : ∃ a ∈ l₂, (f a).isSome) :
    ∃ b, (l₁.findSome? f <|> l₂.findSome? f) = some b ∧ p b := by
  rcases h₁ : l₁.findSome? f with _ | b
  · obtain ⟨a, ha, hfa⟩ := h
    rcases h₂ : l₂.findSome? f with _ | b
    · exact absurd hfa (by rw [List.findSome?_eq_none_iff.mp h₂ a ha]; simp)
    · obtain ⟨a', -, hfa'⟩ := List.exists_of_findSome?_eq_some h₂
      exact ⟨b, by simp, hf a' b hfa'⟩
  · obtain ⟨a', -, hfa'⟩ := List.exists_of_findSome?_eq_some h₁
    exact ⟨b, by simp, hf a' b hfa'⟩

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

/-- The Statement's witness word, at a proof naming the witness root `d`. -/
theorem witnessWord_eq (answers : List UInt8 → Option Digest) (keys : List (List UInt8))
    (proof : PcsQuotient.Proof) (d : Digest)
    (hd : digestOfScalars proof.reduction.witnessRoot = some d) :
    PcsQuotient.witnessWord 22 answers keys proof =
      some (LeanVM.Extraction.leafAt (LeanVM.Extraction.committedLeaves answers keys d 20
        (2 ^ WhirBridge.laneFold)) 20 (2 ^ WhirBridge.laneFold)) := by
  unfold PcsQuotient.witnessWord PcsQuotient.witnessRootOf
  rw [hd]
  rfl

/-- **The Statement's extractor returns a secret** when its word is `W` and the list decoder lists a
stack spelling a secret of the statement: any circuit of `2^n` rows, `n` a variable, so that nothing
of the circuit, the word or the stacks' sizes is computed. -/
theorem extractFrom_spec (n : ℕ) (circuit : PcsQuotient.Circuit) (hlog : circuit.logRows = n)
    (stmt : PcsQuotient.Statement) (answers : List UInt8 → Option Digest)
    (keys : List (List UInt8)) (proof : PcsQuotient.Proof) (W : ℕ → List K)
    (hw : PcsQuotient.witnessWord n answers keys proof = some W)
    (st : Vector K (2 ^ (PcsQuotient.cellVars n + 1)))
    (hst : st ∈ LeanVM.Extraction.decodeStacks (PcsQuotient.cellVars n + 1)
      PcsQuotient.logInvRate W)
    (hrel : PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit st)) :
    ∃ w, PcsQuotient.extractFrom circuit stmt answers keys proof = some w ∧
      PcsQuotient.Relation stmt w := by
  unfold PcsQuotient.extractFrom
  rw [hlog, hw, Option.bind_eq_bind, Option.bind_some]
  refine findSome_orElse _ _ _ (PcsQuotient.Relation stmt) (fun a b hab => ?_) ⟨st, hst, ?_⟩
  · by_cases hr : PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit a)
    · rw [ite_eq_left hr] at hab
      cases hab
      exact hr
    · rw [ite_eq_right hr] at hab
      cases hab
  · show (if PcsQuotient.Relation stmt (PcsQuotient.secretOfStack circuit st) then
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
  exact extractFrom_spec 22 _ membership_logRows stmt _ _ proof _
    (witnessWord_eq _ _ proof d hd) st hst' hrel

end Soundness
