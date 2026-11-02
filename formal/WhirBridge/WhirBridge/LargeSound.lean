/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

Fiat-Shamir soundness of `opening::verify` (`crates/quotient/src/opening.rs`) on public layouts of
`2^24 ..= 2^28` words. `family_sound_q` and `opening_sound_q` are this package's `family_sound`
(`Family.lean`, adapted from leanerVM `mumbai`'s `romSound`, https://github.com/Verified-zkEVM/leanerVM,
commit 6175f1a0, MIT OR Apache-2.0) and `opening_sound` (`Verifier.lean`) with the verifier's query
count a parameter, their proofs unchanged otherwise.
-/
import WhirBridge.LargeParams
import WhirBridge.LargeLayout

/-!
# Public openings at `2^24 ..= 2^28`

**`ours_sound_public`**: for every public layout `Layout.new vars log_chunk log_n chunks` of
`(table, height)` chunks that `Layout::new` accepts (`NewOK`, decided on the chunks' numbers) with
`24 ≤ log_n ≤ 28`, an adversary of at most `QA` queries to Keccak-256 and Keccak-f[1600] that
outputs a root, claims on the layout and a proof makes `opening::verify` (rate `1/2`) accept while
every candidate table of the word extracted for that root violates one of the claims with
probability at most

```
openingBound QA = (QA + 10122) · (2^-128 + 5 (QA + 10122) / 2^256)  ≤ 2^-63 for QA ≤ 2^64.
```

It is `opening_sound` at those layouts, which are valid by one generic lemma (`Layout.new_valid`)
and admissible (`admissible_large`). `ours_sound_public_layout` is the same for any public layout
whose blocks are a valid public stacking.

**`ours_sound_public_at`**: the same with the shape's own query count `QO = largeQueries log_n`
(`7183 ..= 9018`, `isTotalQueryBound_large`) in place of the uniform `10122`:
`(QA + QO) · (2^-128 + 5 (QA + QO) / 2^256)` (`openingBoundAt`).

**`joint_public_large`**: what the composition reads off an opening that is not doomed: one
candidate among the root's at most `L₀ = largeList log_n` (`9952 ..= 3564`) whose table satisfies
all of its claims.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound (boundary_append_of extractedFrom_eq commitStack_after_ret)
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The query count as a parameter -/

/-- The bound of `opening_sound` with the verifier's query count `QV`:
`(QA + QV) · (2^-128 + 5 (QA + QV) / 2^256)`. -/
noncomputable def openingBoundAt (QV QA : ℕ) : ℝ≥0∞ :=
  ((QA + QV : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((5 * (QA + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256)

theorem openingBoundAt_variant (QA : ℕ) : openingBoundAt variantQueries QA = openingBound QA := by
  rw [openingBoundAt, openingBound, variantQueries_eq]

/-- Fewer verifier queries, a smaller bound. -/
theorem openingBoundAt_le {QV : ℕ} (h : QV ≤ variantQueries) (QA : ℕ) :
    openingBoundAt QV QA ≤ openingBound QA := by
  rw [← openingBoundAt_variant]
  unfold openingBoundAt
  have h' : QA + QV ≤ QA + variantQueries := by omega
  gcongr

/-- `family_sound` with the verifier's query count `QV` a hypothesis (the proof is
`family_sound`'s). -/
theorem family_sound_q {L : Stacking} {R : ℕ} (hw : Whir.Admissible L.logN R) (pre : Bytes)
    (A : OracleComp KeccakCalls (Stmt L × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam (famSeeds L pre) (famProgram L R) z) QV) :
    Pr{let z ← romExperiment A (verifierFam (famSeeds L pre) (famProgram L R))}[
        z.1.2 = true ∧ FamDoomed L R z.1.1 z.2] ≤
      (QA + QV : ℕ) * (εWhir + failBound (famSeeds L pre) (QA + QV)) := by
  refine romSound_of_imp (famProgram L R) (famCert L R hw) (famSeeds L pre)
    (fun x ↦ rootOk_famHistory x) εWhir (famCert_bound L R hw) A QA hA QV hV
    (FamDoomed L R) fun z c hv hbad ↦ ?_
  have hseed : (famSeeds L pre).seed z.1 = famSeed pre z.1 := rfl
  have hroot : (famSeeds L pre).root z.1 = famHistory z.1 := rfl
  rw [hseed, hroot, nodeAt_famHistory] at hv
  obtain ⟨e, rest, hhist, hce⟩ := extracted_root (L := L) (R := R) (claims := z.1.claims) hv
  obtain ⟨r, rest', hr, hhist'⟩ := extracted_root_word hw hv
  have he : e = Ev.commit (rootHeight L.logN R) (2 ^ laneFold)
      (extract (fun x ↦ c (.inl x)) r (rootHeight L.logN R) (2 ^ laneFold)) :=
    (List.cons.inj (hhist.symm.trans hhist')).1
  have hws := (Sound.after_extractedHistory _ _ hv).2
  rw [hhist] at hws
  unfold Doomed
  rw [hseed, hroot, nodeAt_famHistory]
  refine ⟨famHistory z.1 ++ [e], ?_, by rw [List.length_append]; omega, ?_, ?_⟩
  · rw [extractedFrom_eq _ _ _ _ _ _ hv, hhist]
    exact (List.prefix_append_right_inj _).mpr ⟨rest, rfl⟩
  · obtain ⟨level, rest', W, -, he⟩ := commitStack_after_ret hce
    rw [List.singleton_inj.1 he]
    exact boundary_append_of (h := []) trivial
  · refine (famD_iff L R hw z.1 [e]).2 (variantCert_D_root L R hw z.1.claims z.1.short hce
      ⟨shapeOK_root L R hw hce fun ht w W he ↦ hws ht w W (he ▸ List.mem_cons_self ..),
        fun q hq ↦ ?_⟩)
    have hq' : q ∈ Candidates L.logN R (code₀ L.logN R).thr
        (extract (fun x ↦ c (.inl x)) r (rootHeight L.logN R) (2 ^ laneFold)) := by
      rw [he] at hq
      simpa [LeanVM.Protocol.Whir.Sound.wordOf, commits] using hq
    obtain ⟨cl, hcl, hn⟩ := hbad r hr q hq'
    exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨cl, hcl, rfl⟩), hn⟩

/-- `opening_sound` with the verifier's query count `QV` a hypothesis (the proof is
`opening_sound`'s). -/
theorem opening_sound_q (L : Layout) (hL : L.Valid) {R : ℕ} (hw : Whir.Admissible L.logN R)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound
      (verifierFam (famSeeds L.stacking (openingPrefix L R)) (famProgram L.stacking R) z) QV)
    (A : OracleComp KeccakCalls ((Digest × Stmt L.stacking) × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier L R)}[z.1.2 = true ∧ OpeningDoomed L R z.1.1 z.2] ≤
      openingBoundAt QV QA := by
  set pre := openingPrefix L R
  set f : (Digest × Stmt L.stacking) × Proof → Stmt L.stacking × Proof := fun w ↦ (w.1.2, w.2)
  have hA' : IsTotalQueryBound (f <$> A) QA := (isQueryBound_map_iff A f QA _ _).mpr hA
  have hfam := family_sound_q (L := L.stacking) hw pre (f <$> A) QA hA' QV hV
  rw [romExperiment_map, prEvent_map] at hfam
  have hbound : (QA + QV : ℕ) * (εWhir + failBound (famSeeds L.stacking pre) (QA + QV)) =
      openingBoundAt QV QA := by
    rw [openingBoundAt, failBound]
    simp [famSeeds, εWhir]
  rw [hbound] at hfam
  refine le_trans ?_ hfam
  have hV' : (fun w ↦ verifierFam (famSeeds L.stacking pre) (famProgram L.stacking R) (f w)) =
      fun w ↦ seedComp pre w.1.2.claims >>= fun seed ↦
        runProofWithHash callKeccak256 callKeccakF1600 (variantProg L.stacking R w.1.2.claims)
          seed w.2 := funext fun w ↦ verifierFam_eq L R w
  have hO : ourVerifier L R = fun w ↦ if w.1.2.claims.isEmpty = false then
      (seedComp pre w.1.2.claims >>= fun seed ↦
        if rootOf w.2 = some w.1.1 then
          runProofWithHash callKeccak256 callKeccakF1600 (variantProg L.stacking R w.1.2.claims)
            seed w.2
        else pure false) else pure false := funext fun w ↦ ourVerifier_eq L R w
  rw [hV', hO]
  refine romExperiment_le_of_reject A (fun w ↦ seedComp pre w.1.2.claims)
    (fun w seed ↦ runProofWithHash callKeccak256 callKeccakF1600
      (variantProg L.stacking R w.1.2.claims) seed w.2)
    (fun w ↦ w.1.2.claims.isEmpty = false) (fun w ↦ rootOf w.2 = some w.1.1)
    (fun w cache ↦ OpeningDoomed L R w cache)
    (fun w cache ↦ FamDoomed L.stacking R (f w) cache) fun w cache _ hr hbad ↦ ?_
  intro r hr' q hq
  rw [hr'] at hr
  obtain rfl := (Option.some.inj hr).symm
  obtain ⟨cl, hcl, hne⟩ := hbad q hq
  exact ⟨cl, hcl, fun h ↦ hne ((L.holds_iff hL cl (w.1.2.wide cl hcl) q).1 h)⟩

/-! ## The shapes `2^24 ..= 2^28` -/

/-- The proven program's query count at these shapes: `QO = largeQueries log_n`. -/
theorem isTotalQueryBound_fam_large (L : Stacking) (h1 : largeMin ≤ L.logN)
    (h2 : L.logN ≤ largeMax) (pre : Bytes) (z : Stmt L × Proof) :
    IsTotalQueryBound (verifierFam (famSeeds L pre) (famProgram L logInvRate) z)
      (largeQueries L.logN) := by
  rw [verifierFam_fam pre]
  exact isTotalQueryBound_verifierComp (costLE_large L h1 h2 z.1.claims) (famSeed pre z.1) z.2

/-- **Fiat-Shamir soundness of `opening::verify` on any valid public layout of `2^24 ..= 2^28`
words**, at rate `1/2`. -/
theorem ours_sound_public_layout (L : Layout) (hP : L.IsPublic) (hV : L.toBlocks.Valid)
    (h1 : largeMin ≤ L.logN) (h2 : L.logN ≤ largeMax)
    (A : OracleComp KeccakCalls ((Digest × Stmt L.stacking) × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier L logInvRate)}[
        z.1.2 = true ∧ OpeningDoomed L logInvRate z.1.1 z.2] ≤ openingBound QA :=
  opening_sound L (Or.inl ⟨hP, hV⟩) (admissible_large h1 h2) A QA hA

/-- **Fiat-Shamir soundness of `opening::verify` on every public layout of `(table, height)`
chunks of `2^24 ..= 2^28` words** that `Layout::new` accepts (`NewOK`), at rate `1/2`: accepting
while every candidate table of the root's word violates a claim has probability at most
`openingBound QA`, at most `2^-63` for `QA ≤ 2^64` (`ours_sound_public_le`). -/
theorem ours_sound_public (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax)
    (A : OracleComp KeccakCalls
      ((Digest × Stmt (Layout.new vars logChunk logN chunks).stacking) × Proof))
    (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier (Layout.new vars logChunk logN chunks) logInvRate)}[
        z.1.2 = true ∧
          OpeningDoomed (Layout.new vars logChunk logN chunks) logInvRate z.1.1 z.2] ≤
      openingBound QA :=
  opening_sound _ (Layout.new_valid hS) (admissible_large h1 h2) A QA hA

/-- The same bound, evaluated: at most `2^-63` against `2^64` queries. -/
theorem ours_sound_public_le (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax)
    (A : OracleComp KeccakCalls
      ((Digest × Stmt (Layout.new vars logChunk logN chunks).stacking) × Proof))
    (QA : ℕ) (hQ : QA ≤ 2 ^ 64) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier (Layout.new vars logChunk logN chunks) logInvRate)}[
        z.1.2 = true ∧
          OpeningDoomed (Layout.new vars logChunk logN chunks) logInvRate z.1.1 z.2] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 63 :=
  (ours_sound_public vars logChunk logN chunks hS h1 h2 A QA hA).trans (opening_bound_le hQ)

/-- **With the shape's own query count**: `openingBoundAt QO QA`, `QO = largeQueries log_n`
(`7183, 7546, 7928, 8318, 9018` at `log_n = 24 ..= 28`). -/
theorem ours_sound_public_at (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax)
    (A : OracleComp KeccakCalls
      ((Digest × Stmt (Layout.new vars logChunk logN chunks).stacking) × Proof))
    (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier (Layout.new vars logChunk logN chunks) logInvRate)}[
        z.1.2 = true ∧
          OpeningDoomed (Layout.new vars logChunk logN chunks) logInvRate z.1.1 z.2] ≤
      openingBoundAt (largeQueries logN) QA :=
  opening_sound_q _ (Layout.new_valid hS) (admissible_large h1 h2) _
    (isTotalQueryBound_fam_large _ h1 h2 _) A QA hA

/-- **Joint extraction at these shapes**: a root's commitment of the stack's shape that is not
doomed for an opening on a public layout of chunks has one candidate, among at most
`L₀ = largeList log_n`, whose table satisfies every claim of that opening. -/
theorem joint_public_large {vars logChunk logN : ℕ} {chunks : List (ℕ × ℕ)}
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax)
    (claims : List Claim) (hc : ∀ c ∈ claims, c.point.length = vars)
    (cs : List (ℕ × ℕ × Word))
    (hshape : LeanVM.Protocol.Whir.Sound.ShapeOK 0 (code₀ logN logInvRate) laneBits cs)
    (hnot : ¬ OpeningDoom (Layout.new vars logChunk logN chunks).stacking logInvRate claims cs) :
    (Candidates logN logInvRate (code₀ logN logInvRate).thr
        (LeanVM.Protocol.Whir.Sound.wordOf cs 0)).ncard ≤ largeList logN ∧
      ∃ q ∈ Candidates logN logInvRate (code₀ logN logInvRate).thr
          (LeanVM.Protocol.Whir.Sound.wordOf cs 0),
        ∀ c ∈ claims, (Layout.new vars logChunk logN chunks).tableEval q c.point = c.value := by
  refine ⟨(candidates_large h1 h2 _).2, ?_⟩
  obtain ⟨q, hq, hall, -⟩ :=
    (Layout.new vars logChunk logN chunks).joint_of_not_doom (Layout.new_valid hS) logInvRate
      claims hc cs hshape hnot
  exact ⟨q, hq, hall⟩

/-! ## A shape, by `decide`

How a fixed shape is covered: its `NewOK` is decided on the chunks' numbers (no stack is ever
built), and `ours_sound_public` applies. Here a stack of `2^28` words (lanes of `2^22`) holding
`40` columns of `2^22` rows, one of `3 · 2^20` rows (one lane, partly used) and a column of `2^23`
rows over two chunks: `43` lanes, a table of `28` variables. -/

/-- The example's chunks `(table, height)`. -/
def exampleChunks : List (ℕ × ℕ) :=
  (List.range 40).map (fun i ↦ (i, 2 ^ 22)) ++ [(40, 3 * 2 ^ 20), (41, 2 ^ 22), (42, 2 ^ 22)]

theorem exampleChunks_ok : NewOK 28 22 28 exampleChunks ∧ (exampleChunks.map Prod.fst).Nodup ∧
    (Layout.new 28 22 28 exampleChunks).lanes.length = 43 := by
  decide +kernel

theorem example_sound
    (A : OracleComp KeccakCalls
      ((Digest × Stmt (Layout.new 28 22 28 exampleChunks).stacking) × Proof))
    (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier (Layout.new 28 22 28 exampleChunks) logInvRate)}[
        z.1.2 = true ∧ OpeningDoomed (Layout.new 28 22 28 exampleChunks) logInvRate z.1.1 z.2] ≤
      openingBoundAt 9018 QA :=
  largeQueries_eq.2.2.2.2 ▸ ours_sound_public_at 28 22 28 exampleChunks exampleChunks_ok.1
    (by decide) (by decide) A QA hA

end WhirBridge
