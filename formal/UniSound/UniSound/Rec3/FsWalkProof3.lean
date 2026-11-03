-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsWalkProof.lean` (`uniWalk`,
-- `uniWalkReject`) for π1-rec3's walk (`UniStatement.runWithFs … .rec3 true`); its generic lemmas (`progRun`,
-- `readCounts_ok`, `consumes_run`, …) are used as they are.
import UniSound.Rec3.FsWalk3
import UniSound.FsWalkProof

/-!
# π1-rec3's walk is the chain (`UniWalk3`, `UniWalkReject3`)

The two halves of π1-rec3's verifier bridge's walk (`FsWalk3.lean`), proved for **every** deployment, Flock phase,
`nV`, `np` and code-level link `C` (no hypothesis):

* **`uniWalk3 : UniWalk3 D F3 nV np C`**: on a stream of `uLen3` bytes the walk's verdict and result are `uAccB3`
  and `uOut3` at the chain's challenges;
* **`uniWalkReject3 : UniWalkReject3 D F3 nV np`**: on a stream of another length every outcome rejects.

The route is `FsWalkProof.lean`'s: the walk's wrapper (`runWithFs_pair3`: `runWithFs` is the seed, `reduceWithFs`,
then `finish`; its verdict and result are `walkOf3` of `obsOf3`), the code-level link `C.link` (stated up to
`obsOf3`) replaces `reduceWithFs` by `readCounts` then `C.prog`, and the main line's generic lemmas do the rest:
`readCounts_ok`, **`progRun`** (any chain program on a stream holding its bytes is the chain's steps), the bytes the
chain absorbs (`absorbsI_wAbs`), `Consumes` for the rejection.

**The narrow challenges** (`sampleNarrow`, which records `narrowE x` in `Chan.challenges`) need no change of a walk
lemma: the chain program's rounds draw through `samples` (the raw challenges, `progRun`), the code-level link relates
`reduceWithFs` to it up to `obsOf3` (no `challenges`), and the walk's verdict and result (`walkOf3`) read only the
result, the stream, the cursor and the zeros' verdict.
-/

namespace UniSound

open Compose QuotientRpm LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics UniStatement
open OracleSpec OracleComp

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## The walk: the seed, π1-rec3's run, `finish` -/

/-- **The verdict and result of a walk** from what `obsOf3` keeps of the run (`walkOf` without the challenges). -/
def walkOf3 (o : Except UniError Reduced × Option (Array UInt8 × ℕ × ℕ × Digest × Bool)) :
    Bool × Except UniError Reduced :=
  match o with
  | (.error e, _) => (false, .error e)
  | (.ok r, some (d, cur, _, _, z)) =>
    if cur = d.size then (z, .ok r) else (false, .error .streamNotConsumed)
  | (.ok _, none) => (false, .error .streamNotConsumed)

theorem walkOf3_ok (x : Except UniError Reduced × Chan) (r : Reduced) (h1 : x.1 = .ok r)
    (h2 : x.2.cursor = x.2.data.size) : walkOf3 (obsOf3 x) = (x.2.zeros.all (· == 0), .ok r) := by
  rcases x with ⟨res, c⟩
  simp only at h1 h2
  subst h1
  simp [obsOf3, walkOf3, h2]

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **The walk's verdict and result** at a Fiat–Shamir shape are `walkOf3` of what `obsOf3` keeps of
`reduceWithFs`'s run from the seed's channel. -/
theorem runWithFs_pair3 (F : KeccakState → m KeccakState) (shape : UniStatement.Shape) (iv input : List UInt8)
    (stream : Array UInt8) (bl : Blake2s) (mode : ClaimsMode) (fs : FsShape) (walk : Bool) :
    (fun o : Outcome => (o.accepts, o.result)) <$> runWithFs F shape iv input stream bl mode fs walk =
      seedWith F iv input >>= fun seed => (fun x => walkOf3 (obsOf3 x)) <$>
        (reduceWithFs F shape (publicWordsOf input) bl mode fs walk).run.run (Chan.start seed stream) := by
  simp only [runWithFs, map_bind]
  congr 1
  funext seed
  simp only [ExceptT.run_bind, StateT.run_bind, bind_assoc]
  rw [map_eq_bind_pure_comp]
  congr 1
  funext x
  rcases x with ⟨r, c⟩
  cases r with
  | error e => simp [walkOf3, obsOf3, Outcome.accepts]
  | ok a =>
    simp only [StateT.run_bind, finish_run]
    split_ifs with h <;> simp [walkOf3, obsOf3, Outcome.accepts, h]

end Monad

/-! ## WALK -/

/-- **WALK** (π1-rec3): on a stream of π1-rec3's length, the walk is the chain: its verdict `uAccB3`, its result
`uOut3`, at the chain's challenges over Keccak-256 `= keccak256With F`. -/
theorem uniWalk3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np) :
    UniWalk3 D F3 nV np C := by
  intro m _ _ F π hlen
  have hsz : π.proof.stream.size = 24 + roundsBytes (uRounds3 F3 nV np) + 24 * 3 := hlen
  have hsz' : π.proof.stream.size = 24 + roundsBytes (rec3Rounds F3.prog.rounds nV np) + 24 * 3 := hlen
  have h6 : D.shape.heights.length = 6 := D.valid.1
  have hrows : countsAt π.proof.stream 0 6 = (uSt3 F3 nV np π).2 := countsAt_rows _ (by omega)
  rw [runWithFs_pair3]
  have hlink : ∀ c, (fun x => walkOf3 (obsOf3 x)) <$>
      (reduceWithFs F D.shape (publicWordsOf π.input.toList) (.flock flockMain) .point .rec3 true).run.run c =
      (fun x => walkOf3 (obsOf3 x)) <$>
        (readCounts D.shape.heights >>= fun rows => (C.prog π.input rows).run F).run.run c := by
    intro c
    have h := congrArg (fun z => walkOf3 <$> z) (C.link π.input F c)
    simpa only [Functor.map_map] using h
  simp only [hlink]
  have hrc : ∀ seed : Digest,
      (readCounts D.shape.heights >>= fun rows => (C.prog π.input rows).run F).run.run
          (Chan.start seed π.proof.stream) =
        ((C.prog (uSt3 F3 nV np π).1 (uSt3 F3 nV np π).2).run F).run.run
          (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
            (countZeros D.shape.heights (uSt3 F3 nV np π).2)) := by
    intro seed
    rw [run_bind_ok (readCounts_ok D.shape.heights _ (by simp only [Chan.start, h6]; omega))]
    simp only [Chan.start, h6, hrows]
    rfl
  simp only [hrc]
  have hpr : ∀ seed : Digest,
      ((C.prog (uSt3 F3 nV np π).1 (uSt3 F3 nV np π).2).run F).run.run
          (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
            (countZeros D.shape.heights (uSt3 F3 nV np π).2)) =
        progOut (C.prog (uSt3 F3 nV np π).1 (uSt3 F3 nV np π).2)
            (collectZ { Chan.start seed π.proof.stream with cursor := 24 }
              (countZeros D.shape.heights (uSt3 F3 nV np π).2)) <$>
          steps (kB F) (toB seed)
            (wAbs π.proof.stream 24 (bytesAt π.proof.stream 0 24) (uRounds3 F3 nV np)) := by
    intro seed
    rw [progRun _ F _ (by simp [collectZ, Chan.start])
      (by simp only [collectZ, Chan.start, C.rounds_eq, C.tail_eq]; omega)]
    simp only [preOf, collectZ, Chan.start, toList_extract_eq, C.rounds_eq, Nat.sub_zero]
  simp only [hpr]
  rw [seedWith, keccak_eq, bind_map_left]
  change _ = _ <$> (uSpec3 F3 nV np).chain (kB F) _ _
  rw [chainU_eq, map_bind, uView_eq]
  simp only [uniSpec_label, uniSpec_absorbsS, uniSpec_rounds, uniSpec_lim,
    rowBytes_toList _ (by omega : 24 ≤ π.proof.stream.size)]
  rw [absorbsI_wAbs π.proof.stream _ 0 24 _ (by omega)]
  simp only [↓reduceIte]
  refine congrArg (fun f => kB F (name ++ π.iv.toList ++ π.input.toList) >>= f) (funext fun st0 => ?_)
  rw [toB_ofB, Functor.map_map, Functor.map_map]
  refine congrArg (fun f => f <$> steps (kB F) st0
    (wAbs π.proof.stream 24 (bytesAt π.proof.stream 0 24) (uRounds3 F3 nV np))) (funext fun sts => ?_)
  set P := C.prog (uSt3 F3 nV np π).1 (uSt3 F3 nV np π).2 with hP
  set c1 := collectZ { Chan.start (ofB st0) π.proof.stream with cursor := 24 }
    (countZeros D.shape.heights (uSt3 F3 nV np π).2) with hc1
  have hd : c1.data = π.proof.stream := rfl
  have hcu : c1.cursor = 24 := rfl
  have hz0 : c1.zeros.toList = countZeros D.shape.heights (uSt3 F3 nV np π).2 := by
    simp only [hc1, collectZ, Chan.start, foldl_push_toList, List.nil_append]
  set ch := groupK (uRounds3 F3 nV np) (List.map (chalL uLimbs) sts) with hch
  have hN : (runOut P P.rounds [] c1 sts).1 = uDone (uRounds3 F3 nV np) π ch := by
    rw [runOut_done, C.rounds_eq, List.nil_append, hd, hcu]
    rfl
  have htl : scalarsAt (runOut P P.rounds [] c1 sts).2.data (runOut P P.rounds [] c1 sts).2.cursor
      P.tail = uTail3 (uRounds3 F3 nV np) π := by
    rw [runOut_data, runOut_cursor, C.rounds_eq, C.tail_eq, hd, hcu]
    rfl
  have hcur : (progOut P c1 sts).2.cursor = (progOut P c1 sts).2.data.size := by
    rw [progOut_cursor, progOut_data, C.rounds_eq, C.tail_eq, hd, hcu]
    omega
  rw [walkOf3_ok _ _ (progOut_fst P c1 sts) hcur, hN, htl]
  refine Prod.ext ?_ rfl
  show _ = uAccB3 D F3 nV np C π ch
  rw [Bool.eq_iff_iff, all_zero_iff, uAccB3, @decide_eq_true_iff _ (Classical.propDecidable _),
    progOut_zeros, hN, htl, hz0]
  unfold UAcc3 ChainProg.ZerosVanish
  have hzf := zerosFrom_iff P [] (uDone (uRounds3 F3 nV np) π ch)
  simp only [List.nil_append] at hzf
  rw [← hzf]
  simp only [List.mem_append]
  constructor
  · intro h
    exact ⟨fun z hz => h z (Or.inl (Or.inl hz)), fun z hz => h z (Or.inl (Or.inr hz)),
      fun z hz => h z (Or.inr hz)⟩
  · rintro ⟨h1, h2, h3⟩ z ((hz | hz) | hz)
    exacts [h1 z hz, h2 z hz, h3 z hz]

/-! ## WALK REJECTS -/

/-- **π1-rec3's code consumes π1-rec3's length**, `uLen3`. -/
theorem consumes_main3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ)
    (C : UniCode3 D F3 nV np) (input : Vector UInt8 32) (F : KeccakState → OC KeccakState) :
    Consumes (uLen3 F3 nV np) (readCounts D.shape.heights >>= fun rows => (C.prog input rows).run F) := by
  refine ((consumes_readCounts _).bind (k := roundsBytes (uRounds3 F3 nV np) + (3 * 24 + (0 + 0)))
    fun rows => ?_).mono_eq ?_
  · have h := consumes_run (C.prog input rows) F
    rw [C.rounds_eq, C.tail_eq] at h
    exact h
  · rw [D.valid.1, uLen3]
    ring

/-- **WALK REJECTS** (π1-rec3): on a stream of another length, every outcome of the walk over `π` rejects: a
successful run of π1-rec3's code reads exactly `uLen3` bytes (`consumes_main3`, through the code-level link, which
keeps the result, the stream and the cursor), so the stream ran out (`StreamExhausted`) or is left unread
(`StreamNotConsumed`). -/
theorem uniWalkReject3 (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ)
    (C : UniCode3 D F3 nV np) : UniWalkReject3 D F3 nV np := by
  intro π hne o ho
  have key := runWithFs_pair3 (m := OC) Common.queryPermutation D.shape π.iv.toList π.input.toList
    π.proof.stream (.flock flockMain) .point .rec3 true
  have h1 : (o.accepts, o.result) ∈ support ((fun o : Outcome => (o.accepts, o.result)) <$>
      runWithFs Common.queryPermutation D.shape π.iv.toList π.input.toList π.proof.stream
        (.flock flockMain) .point .rec3 true) := by
    rw [support_map]
    exact ⟨o, ho, rfl⟩
  rw [key, mem_support_bind_iff] at h1
  obtain ⟨seed, -, h2⟩ := h1
  have hl := congrArg (fun z => walkOf3 <$> z)
    (C.link π.input Common.queryPermutation (Chan.start seed π.proof.stream))
  simp only [Functor.map_map] at hl
  rw [hl, support_map] at h2
  obtain ⟨y, hy, hyo⟩ := h2
  have hc := consumes_main3 D F3 nV np C π.input Common.queryPermutation
    (Chan.start seed π.proof.stream) y (by simp [Chan.start]) hy
  have hacc : (walkOf3 (obsOf3 y)).1 = false := by
    rcases y with ⟨r, c'⟩
    cases r with
    | error e => rfl
    | ok a =>
      obtain ⟨h3, h4, -⟩ := hc a rfl
      simp only [Chan.start] at h3 h4
      simp only [obsOf3, walkOf3]
      split_ifs with h
      · exact absurd (by rw [← h3, ← h, h4, Nat.zero_add]) hne
      · rfl
  have := congrArg Prod.fst hyo
  simp only at this
  rw [← this]
  exact hacc

end UniSound

/-- info: 'UniSound.uniWalk3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniWalk3

/-- info: 'UniSound.uniWalkReject3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniWalkReject3
