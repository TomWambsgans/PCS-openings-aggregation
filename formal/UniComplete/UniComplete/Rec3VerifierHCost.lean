-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`; and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean`'s cost of the opening (`cost_openingWithH`, `vOpen`).
import UniComplete.Rec3VerifierHDuplex
import UniComplete.VerifierHCost

/-!
# The block count of π1-rec3's verifier

**`cost_verifierRec3WithH`**: π1-rec3's deployed verifier over the two calls, on any proof whose stream has at most
`S` bytes, makes at most `verifierCost3 D S` block calls (`hashBlocks`: a Keccak-256 of `n` bytes costs
`⌊n / 136⌋ + 1`, a Keccak-f[1600] one), whatever its opening proofs: **`VerifierCost3 D S (verifierCost3 D S)`**
(`Rec3Hyp.lean`). At `S = 2^40` and a program IV of at most `2^40` bytes it is below `2^42` (`verifierCost3_le`).

`verifierCost3 D S = ivCost3 D + 1 + 30 + 3 S + 3 openCost`, `VerifierHCost.lean`'s count with π1-rec3's changes:

* **The walk** (`cc_reduceWithFsH_walked`), counted by `VerifierHCost.lean`'s potential (`pot`: three per unread
  byte, one per byte read but not yet hashed; a read of `n` bytes releases `2 n`, a challenge costs at most `2` plus
  the bytes it hashes). Every sumcheck round reads before its challenge, so the rounds are paid by their reads, the
  batch's paired rounds too (`cc_sumcheckPairsDrawnH`: a pair's round polynomial reads at least three scalars before
  its one narrow challenge, `cc_pairRoundPoly`; the last plain round, `cc_sumcheckDrawnH`): the bound does not
  depend on the batch's `14` narrow challenges at `27` variables. The other challenges cost `2` each (`walkCost3`):
  **the squares draw one challenge** for the bus's `α ∈ E^4` and one for Flock's zerocheck coordinates after its
  seven fixed ones (`drawCost`, `cc_drawRunH`; the main line draws them one by one), then `β`, `γ`, Flock's `z`, its
  `α`, the ring map's six, `t`, `ρ`, `λ`: `2 + 2 + 26 = 30`, whatever the shape (the main line's `walkCost` grows
  with BLAKE2s's height). From the start, the potential is `3 S`.
* **The seed** (`80` bytes, one block), **the IV** (`ivCost3`: the main line's `280` bytes and the program's IV,
  and π1-rec3's `variantBytes (.flock flockMain) .rec3 true`, `9` more: `fs-rec3`, the skip, the slices' code).
* **The openings**: at most three point claims (the walk's result has at most three openings, the commitments'),
  each `openCost = 46 + vOpen` blocks (`VerifierHCost.lean`'s `qc_pcsOpenWithH`); with the walk, no `A0`, `B0`.

Decisions: the calculus (`CostP`, `CC`, `pot`, `Inv`) and the main line's steps (`cc_sampleH`, `cc_nextScalar`, …,
`cc_tablePart`, `cc_ringEndH`, `qc_pcsOpenWithH`) are `VerifierHCost.lean`'s, reused unchanged; the new steps are
stated for every Fiat–Shamir shape `fs` (`drawCost fs`), the walk for the walked configuration (Flock walked, point
claims: what `verifierRec3WithH` runs, at every `fs` and Flock variant); the batch per shape (`cc_batchFsH_rec3`,
…: one declaration for the eight cases exceeds the heartbeat budget). `verifierCost3_le` takes no shape hypothesis:
π1-rec3's walk costs `30` at every shape. The variant's nine bytes are counted by `decide +kernel` on the nine-byte
list (`variantBytes_rec3_length`), as `VerifierHCost.lean` counts its tags (`name_length`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement

namespace UniComplete.Rec3.Cost3

open UniComplete.Cost

/-! ## The new steps -/

section Steps

/-- **A narrow challenge** costs at most `2` blocks beyond the bytes it hashes, as a challenge. -/
theorem cc_sampleNarrowH : CC (sampleNarrowH callKeccak256) 2 0 fun _ ↦ True := by
  intro c hc e
  refine ⟨?_, fun u a _ ↦ ⟨trivial, ?_, ?_⟩⟩
  · show (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1 ≤ 2 + pot c + e
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega
  · exact ⟨le_rfl, hc.2⟩
  · show 3 * (c.data.size - c.cursor) + (c.cursor - c.cursor) + 0 + e ≤
      2 + pot c + e - ((digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList).length / 136 + 1)
    simp only [List.length_append, len_digestBytes, Array.length_toList, Array.size_extract, pot]
    have := hc.1; have := hc.2
    omega

theorem cc_sampleDrawnH (narrow : Bool) : CC (sampleDrawnH callKeccak256 narrow) 2 0 fun _ ↦ True := by
  cases narrow
  · exact cc_sampleH
  · exact cc_sampleNarrowH

/-- The blocks of a run of `count` challenges beyond the potential: two each drawn one by one (`main`), two for the
first and its squares (the others). -/
def drawCost : FsShape → ℕ → ℕ
  | .main, count => 2 * count
  | .rec1, _ | .rec2, _ | .rec3, _ => 2

theorem cc_drawRunH (fs : FsShape) (count : ℕ) :
    CC (drawRunH callKeccak256 fs count) (drawCost fs count) 0 fun _ ↦ True := by
  cases fs
  · exact cc_samplesH count
  all_goals
    dsimp only [drawRunH, drawCost]
    exact cc_ite _ (cc_pure trivial _) (cc_seq cc_sampleH (fun _ _ ↦ cc_pure trivial _) le_rfl)

/-- **A sumcheck, narrow or not, is paid by its reads.** -/
theorem cc_sumcheckDrawnH (claim : E) (count : ℕ) (h : 2 ≤ count) (equalities : List (Option E)) (narrow : Bool) :
    CC (sumcheckDrawnH callKeccak256 claim count equalities narrow) 0 0 fun _ ↦ True := by
  unfold sumcheckDrawnH
  refine cc_mono (cc_bind (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ ?_) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h
  exact cc_mono (cc_bind (cc_roundPoly count h _ _) fun _ _ ↦ cc_bind (cc_sampleDrawnH narrow) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h

/-- **A pair's round polynomial** releases `2`: it reads at least three scalars. -/
theorem cc_pairRoundPoly (degree : ℕ) (claim : E) :
    CC (pairRoundPoly (m := OracleComp KeccakCalls) degree claim) 0 2 fun _ ↦ True := by
  unfold pairRoundPoly
  exact cc_mono (cc_bind (cc_nextScalars_pos 3 (by norm_num)) fun _ _ ↦ cc_bind (cc_nextScalars _) fun _ _ ↦
    cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ _ ↦ trivial

/-- **The paired sumcheck is paid by its reads**: each pair reads its polynomial before its challenge, and the last
plain round (`degree + 1 ≥ 2` coefficients) too. -/
theorem cc_sumcheckPairsDrawnH (claim : E) (degree vars : ℕ) (h : 1 ≤ degree) (narrow : Bool) :
    CC (sumcheckPairsDrawnH callKeccak256 claim degree vars narrow) 0 0 fun _ ↦ True := by
  unfold sumcheckPairsDrawnH
  refine cc_free (cc_mono (cc_forIn_range (k := 0) _ _ _ fun _ _ ↦ ?_) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦ ?_
  · exact cc_mono (cc_bind (cc_pairRoundPoly _ _) fun _ _ ↦ cc_bind (cc_sampleDrawnH narrow) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by omega) (by omega) fun _ h ↦ h
  · repeat (first
      | exact cc_pure (P := fun _ ↦ True) trivial _
      | refine cc_free (cc_sumcheckDrawnH _ _ (by omega) _ _) fun _ _ ↦ ?_
      | refine cc_ite _ ?_ ?_
      | dsimp only
      | split)

end Steps

/-! ## Flock walked, the batch, the walk -/

section Parts

/-- One step of π1-rec3's walk: `VerifierHCost.lean`'s `cc_step` with the new sumchecks. -/
macro "cc_step3" : tactic => `(tactic| first
  | with_reducible_and_instances refine cc_free (cc_sumcheckPairsDrawnH _ _ _ (by norm_num) _) fun _ _ ↦ ?_
  | with_reducible_and_instances refine cc_free (cc_sumcheckDrawnH _ 3 (by norm_num) _ _) fun _ _ ↦ ?_
  | cc_step)

theorem cc_zerocheckFsH (logN k : ℕ) (fs : FsShape) :
    CC (zerocheckFsH callKeccak256 logN k fs) (drawCost fs (logN - k - Flock.nFixed) + 2) 0 fun _ ↦ True := by
  unfold zerocheckFsH
  refine cc_seq (cc_drawRunH _ _) (fun _ _ ↦ ?_) (by omega)
  split
  · refine cc_free (cc_nextScalars _) fun _ _ ↦ ?_
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun p _ ↦ ?_
    obtain ⟨zSkip, claim⟩ := p
    refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun q _ ↦ ?_
    obtain ⟨chi, running⟩ := q
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    exact cc_pure trivial _
  · dsimp only
    refine cc_free (cc_pure (P := fun _ ↦ True) trivial 0) fun p _ ↦ ?_
    obtain ⟨zSkip, claim⟩ := p
    refine cc_free (cc_sumcheckH _ 3 (by norm_num) _) fun q _ ↦ ?_
    obtain ⟨chi, running⟩ := q
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    exact cc_pure trivial _

theorem cc_frontFsH (logN : ℕ) (variant : Flock.Variant) (fs : FsShape) :
    CC (frontFsH callKeccak256 logN variant fs) (drawCost fs (logN - variant.skip - Flock.nFixed) + 4) 0
      fun _ ↦ True := by
  unfold frontFsH
  refine cc_seq (cc_zerocheckFsH _ _ _) (fun _ _ ↦ ?_) (by omega)
  repeat cc_step

/-- **Flock walked**: the front, the walked terminal (a zero collected), the ring switch's map. -/
theorem cc_verifyWalkedFsH (logN : ℕ) (variant : Flock.Variant) (fs : FsShape) :
    CC (verifyWalkedFsH callKeccak256 logN variant fs) (drawCost fs (logN - variant.skip - Flock.nFixed) + 16) 0
      fun _ ↦ True := by
  unfold verifyWalkedFsH
  refine cc_seq (cc_frontFsH _ _ _) (fun _ _ ↦ ?_) (by omega)
  dsimp only
  refine cc_free (cc_requireZero _) fun _ _ ↦ ?_
  refine cc_seq (cc_ringEndH _ _) (fun _ _ ↦ ?_) (by omega)
  exact cc_pure trivial _

/-- The batching sumcheck's tactic: its steps, then the openings' count. -/
macro "cc_batch " pending:ident : tactic => `(tactic| (
  unfold batchFsH
  rcases $pending:ident with _ | ⟨p, flockPoint⟩ <;> dsimp only <;> repeat cc_step3
  all_goals
    refine cc_pure ?_ _
    simp only [Array.length_toList, Array.size_map]
    refine fold_openings_size _ _ _ _ fun acc x ↦ ?_
    obtain ⟨s1, s2, os, bs⟩ := acc
    obtain ⟨⟨c, claim⟩, v⟩ := x
    simp))

/-- The batch, paired rounds (π1-rec3). -/
theorem cc_batchFsH_rec3 (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    CC (batchFsH callKeccak256 .rec3 combined layouts bitSlice ringMap pending) 2 0
      fun z ↦ z.1.length ≤ combined.length := by
  cc_batch pending

/-- The batch, plain rounds (the main line). -/
theorem cc_batchFsH_main (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    CC (batchFsH callKeccak256 .main combined layouts bitSlice ringMap pending) 2 0
      fun z ↦ z.1.length ≤ combined.length := by
  cc_batch pending

/-- The batch, plain rounds (π1-rec). -/
theorem cc_batchFsH_rec1 (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    CC (batchFsH callKeccak256 .rec1 combined layouts bitSlice ringMap pending) 2 0
      fun z ↦ z.1.length ≤ combined.length := by
  cc_batch pending

/-- The batch, plain narrow rounds (π1-rec2). -/
theorem cc_batchFsH_rec2 (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    CC (batchFsH callKeccak256 .rec2 combined layouts bitSlice ringMap pending) 2 0
      fun z ↦ z.1.length ≤ combined.length := by
  cc_batch pending

/-- **The batching sumcheck at any Fiat–Shamir shape**: `λ`, then rounds (paired or not) paid by their reads; at most
one opening per combined claim. -/
theorem cc_batchFsH (fs : FsShape) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (bitSlice : Option Combined) (ringMap : Option (List E))
    (pending : Option (Flock.Pending × List E)) :
    CC (batchFsH callKeccak256 fs combined layouts bitSlice ringMap pending) 2 0
      fun z ↦ z.1.length ≤ combined.length := by
  cases fs
  · exact cc_batchFsH_main combined layouts bitSlice ringMap pending
  · exact cc_batchFsH_rec1 combined layouts bitSlice ringMap pending
  · exact cc_batchFsH_rec2 combined layouts bitSlice ringMap pending
  · exact cc_batchFsH_rec3 combined layouts bitSlice ringMap pending

/-- π1-rec3's walk's challenges, but the sumchecks' rounds: the two runs (`α ∈ E^4`, Flock's sampled coordinates),
then `β`, `γ`, Flock's `z`, its `α`, the ring map's six, `t`, `ρ`, `λ`, two blocks each. -/
def walkCost3 (shape : Shape) (variant : Flock.Variant) (fs : FsShape) : ℕ :=
  drawCost fs 4 + drawCost fs (blake2sR1csLogSize + shape.heights.getD opBlake2s 0 - variant.skip - Flock.nFixed) +
    26

/-- **The walk, Flock walked, point claims** (π1-rec2's and π1-rec3's): at most `walkCost3` blocks beyond the
potential, and at most three openings. -/
theorem cc_reduceWithFsH_walked (shape : Shape) (publicWords : List E) (variant : Flock.Variant) (fs : FsShape) :
    CC (reduceWithFsH callKeccak256 shape publicWords (.flock variant) .point fs true) (walkCost3 shape variant fs) 0
      fun r ↦ r.openings.length ≤ 3 := by
  unfold reduceWithFsH walkCost3
  dsimp only
  split
  · exact cc_throw_bind _ _ _ _ _
  · refine cc_free (cc_countBits _) fun _ _ ↦ ?_
    refine cc_free cc_nextRoot fun _ _ ↦ ?_
    refine cc_seq (cc_drawRunH _ _) (fun _ _ ↦ ?_) (by omega)
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_seq (cc_verifyWalkedFsH _ _ _) (fun x _ ↦ ?_) (by omega)
    obtain ⟨point, end_⟩ := x
    dsimp only
    refine cc_free (cc_pure (P := fun a ↦ a = (some (point, some end_, none), none)) rfl 0) fun a ha ↦ ?_
    subst ha
    refine cc_free cc_nextRoot fun _ _ ↦ ?_
    refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
    refine cc_free (cc_mono (cc_forIn_list (k := 0) _ _ _ fun _ _ ↦ cc_free (cc_tablePart _ _ _ _ _) fun _ _ ↦
      cc_pure (P := fun _ ↦ True) trivial 0) (by simp) le_rfl fun _ h ↦ h) fun _ _ ↦ ?_
    iterate 7 refine cc_free (cc_mono cc_nextScalar le_rfl (Nat.zero_le _) fun _ h ↦ h) fun _ _ ↦ ?_
    rcases end_ with ⟨map, target⟩ | ⟨ws, value⟩ <;> dsimp only
    all_goals try split
    all_goals
      try dsimp only
      refine cc_seq cc_sampleH (fun _ _ ↦ ?_) (by omega)
      refine cc_seq (cc_batchFsH _ _ _ _ _ _) (fun z hz ↦ ?_) (by omega)
      obtain ⟨batched, deferred⟩ := z
      dsimp only at hz ⊢
      split <;> exact cc_pure (P := fun r : Reduced ↦ r.openings.length ≤ 3)
        (hz.trans (List.length_filterMap_le _ _)) _

end Parts

/-! ## The run, the openings, the deployed verifier -/

section Top

open E2ECompleteness.Cost (QC qc_pure)

/-- **The walk** from the start of a stream: the potential is three per byte. -/
theorem costP_walk3 (shape : Shape) (publicWords : List E) (variant : Flock.Variant) (fs : FsShape) (seed : Digest)
    (stream : Array UInt8) (m : ℕ) :
    CostP ((do
        let r ← reduceWithFsH callKeccak256 shape publicWords (.flock variant) .point fs true
        finish (m := OracleComp KeccakCalls)
        return r : CM Reduced).run.run (Chan.start seed stream))
      (walkCost3 shape variant fs + 3 * stream.size + m) fun z rem ↦
        ∀ a, z.1 = .ok a → a.openings.length ≤ 3 ∧ m ≤ rem := by
  have h := cc_mono (k' := walkCost3 shape variant fs) (g' := 0)
    (cc_bind (k₂ := 0) (g₂ := 0) (cc_reduceWithFsH_walked shape publicWords variant fs) fun r hr ↦
      cc_free cc_finish fun _ _ ↦ cc_pure (P := fun r : Reduced ↦ r.openings.length ≤ 3) hr 0) (by omega) le_rfl
    fun _ h ↦ h
  have h2 := h (Chan.start seed stream) ⟨le_rfl, Nat.zero_le _⟩ m
  rw [show walkCost3 shape variant fs + pot (Chan.start seed stream) + m =
    walkCost3 shape variant fs + 3 * stream.size + m by simp [pot, Chan.start]] at h2
  exact h2.mono fun z rem hz a ha ↦ ⟨(hz a ha).1, by have := (hz a ha).2.2; omega⟩

/-- **The run on calldata**, walked: the seed, then the walk; at most three openings, `m` blocks left. -/
theorem costP_runWithFsH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (variant : Flock.Variant) (fs : FsShape) (m : ℕ) :
    CostP (runWithFsH callKeccak256 shape iv publicInput stream (.flock variant) .point fs true)
      ((16 + iv.length + publicInput.length) / 136 + 1 + (walkCost3 shape variant fs + 3 * stream.size + m))
      fun o rem ↦ ∀ r, o.result = .ok r → r.openings.length ≤ 3 ∧ m ≤ rem := by
  unfold runWithFsH seedWithH callKeccak256
  rw [costP_query_bind]
  refine ⟨?_, fun seed ↦ ?_⟩
  · show (name ++ iv ++ publicInput).length / 136 + 1 ≤ _
    simp only [List.length_append, name_length]
    omega
  · rw [show (16 + iv.length + publicInput.length) / 136 + 1 + (walkCost3 shape variant fs + 3 * stream.size + m) -
        hashBlocks (Sum.inl (name ++ iv ++ publicInput)) = walkCost3 shape variant fs + 3 * stream.size + m by
      show _ - ((name ++ iv ++ publicInput).length / 136 + 1) = _
      simp only [List.length_append, name_length]
      omega]
    exact (costP_walk3 shape _ variant fs seed stream m).bind fun z rem hz r hr ↦ hz r hr

/-- **The verifier, walked**: the run, then at most three openings (no `A0`, `B0`). -/
theorem costP_verifyWithFsH (shape : Shape) (iv : List UInt8) (roots : SetupRoots) (publicInput : Vector UInt8 32)
    (proof : UniProof) (fs : FsShape) :
    CostP (verifyWithFsH callKeccak256 callKeccakF1600 shape iv roots publicInput proof fs true)
      ((16 + iv.length + 32) / 136 + 1 + (walkCost3 shape flockMain fs + 3 * proof.stream.size + 3 * openCost))
      fun _ _ ↦ True := by
  unfold verifyWithFsH
  rw [show 16 + iv.length + 32 = 16 + iv.length + publicInput.toList.length by simp]
  refine CostP.bind (costP_runWithFsH shape iv publicInput.toList proof.stream flockMain fs (3 * openCost))
    fun o rem ho ↦ ?_
  split
  · trivial
  · split
    · trivial
    · rename_i r hr
      obtain ⟨hl, hrem⟩ := ho r hr
      refine CostP.weaken (n := 3 * openCost + 0) ((costP_of_qc ?_ 0).mono fun _ _ _ ↦ trivial) (by omega)
      refine (qc_forIn_list (c := openCost) _ _ _ fun x s ↦ ?_).bind_le (b := 0) (fun s ↦ ?_) ?_
      · split
        split
        · exact (qc_pcsOpenWithH _ (layoutWordVars_le _) _ _ _ _).bind_le (fun _ ↦ qc_pure _ 0) (by omega)
        · exact qc_pure _ _
      · split
        · contradiction
        · exact qc_pure _ _
        · exact qc_pure _ _
      · have : r.openings.length * openCost ≤ 3 * openCost := Nat.mul_le_mul_right _ hl
        omega

/-- π1-rec3's variant bytes: `fs-rec3`, the skip, the slices' code (`TowerWalk`). -/
theorem variantBytes_rec3_length : (variantBytes (.flock flockMain) .rec3 true).length = 9 := by
  decide +kernel

theorem variantBytes_rec3_isEmpty : (variantBytes (.flock flockMain) .rec3 true).isEmpty = false := by
  decide +kernel

/-- π1-rec3's IV: the main line's preimage (the tag, the program's IV, three roots, the shape and the five layout
words) and the variant's nine bytes. -/
def ivCost3 (D : Deployment) : ℕ := (289 + D.programIv.length) / 136 + 1

/-- **π1-rec3's deployed verifier's block count** on a proof of a stream of at most `S` bytes: the IV, the seed (one
block), the walk (`30` challenges' blocks, whatever the shape), three per stream byte, the three openings. -/
def verifierCost3 (D : Deployment) (S : ℕ) : ℕ := ivCost3 D + 1 + 30 + 3 * S + 3 * openCost

theorem walkCost3_rec3 (shape : Shape) (variant : Flock.Variant) : walkCost3 shape variant .rec3 = 30 := rfl

theorem ivRec3Input_length (D : Deployment) (roots : SetupRoots) :
    (ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++ digestBytes roots.b0 ++
      shapeBytes D.shape ++ (layoutWords D.shape).flatten ++ variantBytes (.flock flockMain) .rec3 true).length =
      289 + D.programIv.length := by
  simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, layoutWords_length,
    variantBytes_rec3_length]
  omega

/-- **π1-rec3's deployed verifier over the two calls makes at most `verifierCost3 D S` block calls** on any proof
whose stream has at most `S` bytes, whatever its opening proofs. -/
theorem cost_verifierRec3WithH (D : Deployment) (S : ℕ) : VerifierCost3 D S (verifierCost3 D S) := by
  intro roots input proof hS
  refine CostP.toQC (Q := fun _ _ ↦ True) ?_
  unfold Deployment.verifierRec3WithH Deployment.ivRec3WithH contractIvForWithH
  simp only [variantBytes_rec3_isEmpty, Bool.false_eq_true, ↓reduceIte]
  unfold callKeccak256
  rw [bind_assoc, costP_query_bind]
  refine ⟨?_, fun d ↦ ?_⟩
  · show (ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++ digestBytes roots.b0 ++
      shapeBytes D.shape ++ (layoutWords D.shape).flatten ++ variantBytes (.flock flockMain) .rec3 true).length /
        136 + 1 ≤ _
    rw [ivRec3Input_length]
    unfold verifierCost3 ivCost3
    omega
  · rw [pure_bind]
    refine (costP_verifyWithFsH D.shape (digestBytes d) roots input proof .rec3).weaken ?_
    show _ ≤ verifierCost3 D S - ((ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
      digestBytes roots.b0 ++ shapeBytes D.shape ++ (layoutWords D.shape).flatten ++
      variantBytes (.flock flockMain) .rec3 true).length / 136 + 1)
    rw [ivRec3Input_length, len_digestBytes, walkCost3_rec3]
    unfold verifierCost3 ivCost3
    omega

theorem openCost_le : openCost ≤ 121492 := by
  unfold openCost E2ECompleteness.Cost.vOpen LeanVM.Protocol.Verifier.whirBound
  norm_num

/-- **At most `2^42` blocks** on streams of at most `2^40` bytes, for a program IV of at most `2^40` bytes (`3 · 2^40`
for the stream, the rest below `2^34`), at any shape. -/
theorem verifierCost3_le (D : Deployment) (hiv : D.programIv.length ≤ 2 ^ 40) : verifierCost3 D (2 ^ 40) ≤ 2 ^ 42 := by
  have ho := openCost_le
  unfold verifierCost3 ivCost3
  omega

end Top

end UniComplete.Rec3.Cost3

/-- info: 'UniComplete.Rec3.Cost3.cost_verifierRec3WithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.Cost3.cost_verifierRec3WithH

/-- info: 'UniComplete.Rec3.Cost3.verifierCost3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.Cost3.verifierCost3_le
