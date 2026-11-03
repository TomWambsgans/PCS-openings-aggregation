-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `formal/UniSound/UniSound/FsWalkProof.lean`
-- (`uniWalk`, `uniWalkReject`) to π2's run (`formal/RecStatement/RecStatement/Verifier.lean`: `reduceWith`, `runWith`),
-- with that file's channel lemmas (`nextRoot_ok`, `nextScalars_ok`, `sample_bind`, `steps`, `wAbs`, `absorbsI_wAbs`,
-- `chainU_eq`) and `formal/RecCompose/RecCompose/Pi2Run.lean`'s (`runWith_post`).
import RecCompose.FsDefs
import UniSound.FsWalkProof

/-!
# π2's walk is the chain (`Pi2Walk`, `Pi2WalkReject`)

The verifier bridge's walk (`FsDefs.lean`) for π2's run at the real circuit `cc`, proved with no hypothesis:

* **`pi2Walk : Pi2Walk`**: on a stream of `944` bytes, in every lawful monad and over every permutation, `runWith`'s
  verdict and result are the chain's challenges (`pi2Spec.chain` over `keccak256With F`) read by `p2Reduced`: the seed
  is the label's hash (`name ‖ iv ‖ input`); the public data's reads (`2` roots, `17` elements, `472` bytes) hash
  nothing and collect `pi2Pubs` (`forIn_bind_run`); then `W`'s root and `α, β, γ` (the first sample absorbs the public
  data and the root, `pre s ++ enc m`), `Q`'s root and `t`, the `16` fold values, `ξ` and `ρ` (`reduceWith_bind_run`);
  `finish` finds the stream read to its end.
* **`pi2WalkReject : Pi2WalkReject`**: on a stream of another length the run fails (`runWith_post`: a success reads
  `pi2Bytes = 944` bytes), so it rejects.
* **`pi2Scalars_real`**: the contract's public scalars (`pi2Scalars`, the run over Keccak-f[1600] at any IV) are
  `pi2Pubs` on a stream of `944` bytes; **`pi2Pubs_pubBytes`**: they read the public data's `472` bytes only.

Decisions: the walk is computed in continuation form, one read or sample at a time, against the chain's steps peeled
one at a time (`steps_cons_bind`); the reads loop by an equation-form `ROk` (`rok_forIn`; `Pi2Run.lean`'s `Reads` gives
postconditions only). `Spec.of cc` is read through `reads` and `logRow` only (`spec_reads`, `spec_logRow`, by `rfl`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics
open UniStatement (Chan ChanM publicWordsOf)
open OracleSpec OracleComp

attribute [local instance high] Completeness.instSampleableTypeE_completeness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack RecStatement.layoutWords

/-! ## The circuit's reads -/

theorem spec_reads : (Spec.of cc).reads = Data.reads := rfl

theorem spec_logRow : (Spec.of cc).logRow = 4 := rfl

theorem reads_bytes : (Data.reads.map Read.bytes).sum = pLen := by decide

theorem pi2Bytes_cc : pi2Bytes (Spec.of cc) = sLen := by
  unfold pi2Bytes
  rw [spec_reads, spec_logRow, reads_bytes]
  rfl

/-! ## Reads that hash nothing, as equations -/

section ROk

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **`X` reads `n` bytes and hashes nothing**: from a channel with `n` bytes left it returns `v` of the data and the
cursor, the cursor advanced by `n`. -/
def ROk {α : Type} (X : ChanM m α) (n : ℕ) (v : Array UInt8 → ℕ → α) : Prop :=
  ∀ c : Chan, c.cursor + n ≤ c.data.size →
    X.run.run c = pure (.ok (v c.data c.cursor), { c with cursor := c.cursor + n })

theorem rok_forIn {γ β : Type} (k : γ → ℕ) (g : Array UInt8 → ℕ → γ → β → β)
    (f : γ → β → ChanM m (ForInStep β)) (hf : ∀ x b, ROk (f x b) (k x) fun d cur => .yield (g d cur x b)) :
    ∀ (l : List γ) (b : β), ROk (forIn l b f) ((l.map k).sum) fun d cur => foldReads k g d cur l b
  | [], b => by
    intro c _
    simp only [List.forIn_nil, List.map_nil, List.sum_nil, foldReads, Nat.add_zero]
    rfl
  | x :: l, b => by
    intro c hc
    simp only [List.map_cons, List.sum_cons] at hc
    rw [List.forIn_cons, UniSound.run_bind_ok (hf x b c (by omega))]
    simp only
    rw [rok_forIn k g f hf l _ _ (by simp only; omega)]
    simp only [foldReads, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **A `for` loop that hashes nothing, then a continuation**. -/
theorem forIn_bind_run {γ β δ : Type} (k : γ → ℕ) (g : Array UInt8 → ℕ → γ → β → β)
    {f : γ → β → ChanM m (ForInStep β)} (hf : ∀ x b, ROk (f x b) (k x) fun d cur => .yield (g d cur x b))
    (l : List γ) (b : β) (K : β → ChanM m δ) (c : Chan) (hc : c.cursor + (l.map k).sum ≤ c.data.size) :
    (forIn l b f >>= K).run.run c =
      (K (foldReads k g c.data c.cursor l b)).run.run { c with cursor := c.cursor + (l.map k).sum } :=
  UniSound.run_bind_ok (rok_forIn k g f hf l b c hc)

theorem nextInteger_okN (n : ℕ) (c : Chan) (h : c.cursor + n ≤ c.data.size) :
    (UniStatement.nextInteger (m := m) n).run.run c =
      pure (.ok (integerAt c.data c.cursor n), { c with cursor := c.cursor + n }) := by
  simp only [UniStatement.nextInteger, ExceptT.run_bind, StateT.run_bind, UniSound.takeBytes_ok n c h, pure_bind,
    ExceptT.run_pure, StateT.run_pure]
  rfl

end ROk

theorem halfAt_eq (d : Array UInt8) (cur : ℕ) (h : cur + 16 ≤ d.size) :
    halfAt d cur = UniStatement.eNew (UniStatement.beWordAt d (cur + 8)) (UniStatement.beWordAt d cur) 0 := by
  unfold halfAt
  dsimp only
  rw [UniSound.beWordAt_extract d cur 16 8 h (by norm_num), UniSound.beWordAt_extract d cur 16 0 h (by norm_num)]
  rfl

theorem scalarAt_eq (d : Array UInt8) (cur : ℕ) (h : cur + 24 ≤ d.size) :
    RecCompose.scalarAt d cur = UniSound.scalarAt d cur := by
  unfold RecCompose.scalarAt UniSound.scalarAt
  dsimp only
  rw [UniSound.beWordAt_extract d cur 24 16 h (by norm_num), UniSound.beWordAt_extract d cur 24 8 h (by norm_num),
    UniSound.beWordAt_extract d cur 24 0 h (by norm_num)]
  rfl

/-! ## The public data -/

theorem extract_congr (d d' : Array UInt8) (a c : ℕ) (hd : c ≤ d.size) (hd' : c ≤ d'.size)
    (h : ∀ i, a ≤ i → i < c → d.getD i 0 = d'.getD i 0) : d.extract a c = d'.extract a c := by
  apply Array.ext
  · simp only [Array.size_extract]
    omega
  · intro i h1 h2
    simp only [Array.size_extract] at h1
    simp only [Array.getElem_extract]
    have := h (a + i) (by omega) (by omega)
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : a + i < d.size),
      Array.getElem?_eq_getElem (by omega : a + i < d'.size), Option.getD_some] at this
    exact this

theorem readValue_congr (d d' : Array UInt8) (cur : ℕ) (rd : Read) (N : ℕ) (hN : cur + rd.bytes ≤ N)
    (hd : N ≤ d.size) (hd' : N ≤ d'.size) (h : ∀ i, i < N → d.getD i 0 = d'.getD i 0) :
    readValue d cur rd = readValue d' cur rd := by
  have hc : ∀ a n, a + n ≤ N → d.extract a (a + n) = d'.extract a (a + n) := fun a n hn ↦
    extract_congr d d' a (a + n) (by omega) (by omega) fun i _ hi ↦ h i (by omega)
  cases rd with
  | integer b =>
    simp only [Read.bytes] at hN
    simp only [readValue, integerAt, hc cur b hN]
  | root =>
    simp only [Read.bytes] at hN
    simp only [readValue, halfAt, hc cur 16 (by omega), hc (cur + 16) 16 (by omega)]
  | scalar =>
    simp only [Read.bytes] at hN
    simp only [readValue, RecCompose.scalarAt, hc cur 24 hN]

theorem foldReads_congr (d d' : Array UInt8) (N : ℕ) (hd : N ≤ d.size) (hd' : N ≤ d'.size)
    (h : ∀ i, i < N → d.getD i 0 = d'.getD i 0) :
    ∀ (l : List Read) (cur : ℕ) (pubs : List E), cur + (l.map Read.bytes).sum ≤ N →
      foldReads Read.bytes pubsStep d cur l pubs = foldReads Read.bytes pubsStep d' cur l pubs
  | [], _, _, _ => rfl
  | rd :: l, cur, pubs, hl => by
    simp only [List.map_cons, List.sum_cons] at hl
    simp only [foldReads, pubsStep]
    rw [readValue_congr d d' cur rd N (by omega) hd hd' h]
    exact foldReads_congr d d' N hd hd' h l _ _ (by omega)

theorem pubBytes_getD (b : Array UInt8) (i : ℕ) (hi : i < pLen) : (pubBytes b).toArray.getD i 0 = b.getD i 0 := by
  simp [pubBytes, hi]

/-- **The public scalars read the public data's `472` bytes only.** -/
theorem pi2Pubs_pubBytes (input : List UInt8) (b : Array UInt8) (h : pLen ≤ b.size) :
    pi2Pubs (Spec.of cc) input (pubBytes b).toArray = pi2Pubs (Spec.of cc) input b := by
  unfold pi2Pubs
  rw [spec_reads]
  exact foldReads_congr _ _ pLen (by simp) h (fun i hi ↦ pubBytes_getD b i hi) Data.reads 0 _
    (by rw [reads_bytes]; omega)

/-! ## The contract's public scalars -/

/-- **The contract's public scalars are `pi2Pubs`** on a stream of `944` bytes (the run over Keccak-f[1600] at any
IV, at the real circuit). -/
theorem pi2Scalars_real (D : RecDeployment) (hD : ∀ iv, (D.pi2 iv).circuit = cc) (roots : RecSetupRoots)
    (input : Vector UInt8 32) (stream : Array UInt8) (h : stream.size = sLen) :
    pi2Scalars D roots input stream = pi2Pubs (Spec.of cc) input.toList stream := by
  have hc : (D.circuitAt roots.pi1).circuit = cc := hD _
  unfold pi2Scalars
  rw [hc]
  have hh := holds_id (runWith_post (m := Id) (fun x ↦ pure (keccakF1600 x)) (Spec.of cc) [] input.toList stream)
  obtain ⟨r, hr⟩ := hh.2 (by rw [pi2Bytes_cc]; exact h)
  obtain ⟨-, hsc, -⟩ := hh.1 r hr
  have hrun : RecStatement.run (Spec.of cc) [] input.toList stream =
      Id.run (runWith (m := Id) (fun x ↦ pure (keccakF1600 x)) (Spec.of cc) [] input.toList stream) := rfl
  rw [hrun, hr]
  exact hsc

/-! ## WALK REJECTS -/

theorem holds_support_oc {ι : Type} {spec : OracleSpec ι} {α : Type} {X : OracleComp spec α} {P : α → Prop}
    (hX : Holds X P) : ∀ x ∈ support X, P x := by
  intro x hx
  have h : (x, P x) ∈ support ((fun x ↦ (x, P x)) <$> X) := by
    rw [support_map]; exact ⟨x, hx, rfl⟩
  unfold Holds at hX
  rw [hX, support_map] at h
  obtain ⟨y, -, hy⟩ := h
  have := congrArg Prod.snd hy
  simp only at this
  exact this ▸ trivial

/-- **WALK REJECTS**: on a stream of another length than `944`, the run fails, so it rejects. -/
theorem pi2WalkReject : Pi2WalkReject := by
  intro π hlen o ho
  have hh := holds_support_oc (runWith_post Common.queryPermutation (Spec.of cc) π.iv.toList π.input.toList
    π.proof.stream) o ho
  unfold RecStatement.Outcome.accepts
  rcases hres : o.result with e | r
  · rfl
  · exact absurd ((hh.1 r hres).1.trans pi2Bytes_cc) hlen

/-! ## The walk -/

/-- The bytes each of the chain's steps absorbs, on a stream of `944` bytes: the public data and `W`'s root, nothing
twice, `Q`'s root, the `17` values. -/
def p2Es (b : Array UInt8) : List (List UInt8) :=
  [UniSound.bytesAt b 0 504, [], [], UniSound.bytesAt b 504 32, UniSound.bytesAt b 536 408]

/-- **The run's result** from the stream and the chain's answers. -/
def red0 (stmt : List E) (b : Array UInt8) (sts : List Bytes32) : RecStatement.Reduced :=
  let pubs := foldReads Read.bytes pubsStep b 0 Data.reads stmt
  let x := sts.map (chalL UniSound.uLimbs)
  let inp : Inputs E := ⟨pubs, x.getD 0 0, x.getD 1 0, x.getD 2 0, x.getD 3 0, UniSound.scalarsAt b 536 16,
    UniSound.scalarAt b 920, x.getD 4 0⟩
  ⟨pubs, pubs.map pairPoint, (UniSound.halvesAt b 472, UniSound.halvesAt b 504), inp, (Spec.of cc).core.run inp⟩

/-- **The channel at the run's end** from the stream and the chain's answers. -/
def cw (b : Array UInt8) (sts : List Bytes32) : Chan :=
  ⟨b, sLen, sLen, ofB (sts.getD 4 default), (sts.map (chalL UniSound.uLimbs)).toArray, #[]⟩

section Walk

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem bind_eq_of {α β : Type} {x x' : m α} {f f' : α → m β} (hx : x = x') (hf : ∀ a, f a = f' a) :
    x >>= f = x' >>= f' := by
  subst hx
  exact bind_congr hf

theorem steps_cons_bind {β : Type} (H : List UInt8 → m Bytes32) (st : Bytes32) (e : List UInt8)
    (es : List (List UInt8)) (f : List Bytes32 → m β) :
    UniSound.steps H st (e :: es) >>= f =
      H (stepIn st e) >>= fun st' => UniSound.steps H st' es >>= fun l => f (st' :: l) := by
  simp only [UniSound.steps, bind_assoc, bind_map_left]

theorem nextRoot_bind {β : Type} (K : E × E → ChanM m β) (c : Chan) (h : c.cursor + 32 ≤ c.data.size) :
    (UniStatement.nextRoot >>= K).run.run c =
      (K (UniSound.halvesAt c.data c.cursor)).run.run { c with cursor := c.cursor + 32 } :=
  UniSound.run_bind_ok (UniSound.nextRoot_ok c h)

theorem nextScalar_bind {β : Type} (K : E → ChanM m β) (c : Chan) (h : c.cursor + 24 ≤ c.data.size) :
    (UniStatement.nextScalar >>= K).run.run c =
      (K (UniSound.scalarAt c.data c.cursor)).run.run { c with cursor := c.cursor + 24 } :=
  UniSound.run_bind_ok (UniSound.nextScalar_ok c h)

theorem nextScalars_bind {β : Type} (n : ℕ) (K : List E → ChanM m β) (c : Chan)
    (h : c.cursor + 24 * n ≤ c.data.size) :
    (UniStatement.nextScalars n >>= K).run.run c =
      (K (UniSound.scalarsAt c.data c.cursor n)).run.run { c with cursor := c.cursor + 24 * n } :=
  UniSound.run_bind_ok (UniSound.nextScalars_ok n c h)

/-- **π2's reduction on a stream of `944` bytes**, in continuation form: the chain's steps on `p2Es` from the seed,
the result `red0` and the channel `cw`. -/
theorem reduceWith_bind_run {δ : Type} (F : KeccakState → m KeccakState) (b : Array UInt8) (hb : b.size = sLen)
    (stmt : List E) (seed : Digest) (K : RecStatement.Reduced → ChanM m δ) :
    (RecStatement.reduceWith F (Spec.of cc) stmt >>= K).run.run (Chan.start seed b) =
      UniSound.steps (UniSound.kB F) (toB seed) (p2Es b) >>= fun sts =>
        (K (red0 stmt b sts)).run.run (cw b sts) := by
  have hb' : b.size = 944 := hb
  unfold RecStatement.reduceWith
  rw [spec_logRow, spec_reads]
  simp only [bind_assoc, pure_bind]
  rw [forIn_bind_run Read.bytes pubsStep ?hf _ _ _ _ (by simp only [Chan.start, reads_bytes, pLen]; omega)]
  case hf =>
    intro x pubs c hc
    cases x with
    | integer n =>
      simp only [Read.bytes] at hc
      simp only
      rw [UniSound.run_bind_ok (nextInteger_okN n c hc)]
      rfl
    | root =>
      simp only [Read.bytes] at hc
      simp only
      rw [UniSound.run_bind_ok (UniSound.nextRoot_ok c hc)]
      simp only [pubsStep, readValue, halfAt_eq c.data c.cursor (by omega),
        halfAt_eq c.data (c.cursor + 16) (by omega)]
      rfl
    | scalar =>
      simp only [Read.bytes] at hc
      simp only
      rw [UniSound.run_bind_ok (UniSound.nextScalar_ok c hc)]
      simp only [pubsStep, readValue, scalarAt_eq c.data c.cursor hc]
      rfl
  -- `W`'s root
  rw [nextRoot_bind _ _ ?_]
  swap
  · simp only [Chan.start, reads_bytes, pLen]
    omega
  -- `α`: the public data and `W`'s root absorbed
  rw [UniSound.sample_bind, p2Es, steps_cons_bind]
  refine bind_eq_of ?_ fun s1 => ?_
  · simp only [UniSound.preOf, Chan.start, UniSound.toList_extract_eq, reads_bytes, pLen]
  -- `β`, `γ`
  rw [UniSound.sample_bind, steps_cons_bind]
  refine bind_eq_of (by rw [UniSound.toB_sampOne, UniSound.preOf_self _ rfl]) fun s2 => ?_
  rw [UniSound.sample_bind, steps_cons_bind]
  refine bind_eq_of (by rw [UniSound.toB_sampOne, UniSound.preOf_self _ rfl]) fun s3 => ?_
  -- `Q`'s root
  rw [nextRoot_bind _ _ ?_]
  swap
  · simp only [UniSound.sampOne, Chan.start, reads_bytes, pLen]
    omega
  -- `t`
  rw [UniSound.sample_bind, steps_cons_bind]
  refine bind_eq_of ?_ fun s4 => ?_
  · simp only [UniSound.preOf, UniSound.sampOne, Chan.start, UniSound.toList_extract_eq, reads_bytes, pLen,
      UniSound.toB_ofB]
  -- the fold values, `ξ`
  rw [nextScalars_bind _ _ _ ?_]
  swap
  · simp only [UniSound.sampOne, Chan.start, reads_bytes, pLen]
    omega
  rw [nextScalar_bind _ _ ?_]
  swap
  · simp only [UniSound.sampOne, Chan.start, reads_bytes, pLen]
    omega
  -- `ρ`
  rw [UniSound.sample_bind, steps_cons_bind]
  refine bind_eq_of ?_ fun s5 => ?_
  · simp only [UniSound.preOf, UniSound.sampOne, Chan.start, UniSound.toList_extract_eq, reads_bytes, pLen,
      UniSound.toB_ofB]
    rfl
  rw [UniSound.steps, pure_bind]
  rfl

theorem finish_cw (b : Array UInt8) (hb : b.size = sLen) (sts : List Bytes32) {β : Type}
    (g : PUnit → ChanM m β) :
    (UniStatement.finish >>= g).run.run (cw b sts) = (g ()).run.run (cw b sts) := by
  refine UniSound.run_bind_ok ?_
  rw [RecCompose.finish_run, ite_eq_left (show (cw b sts).cursor = (cw b sts).data.size from hb.symm)]

end Walk

/-! ## The chain's statement and messages, read off -/

theorem roundsBytes_pi2 : UniSound.roundsBytes (RecPiop.pi2Rounds 4) = 472 := by
  simp [UniSound.roundsBytes, UniSound.roundBytes, RecPiop.pi2Rounds]

/-- **The rounds' messages** the stream carries: `W`'s root at byte `472`, `Q`'s at `504`, the `17` values from
`536`. -/
theorem p2Msgs_eq (π : P2Pf) :
    p2Msgs π = [(some (UniSound.halvesAt π.proof.stream 472), []), (some (UniSound.halvesAt π.proof.stream 504), []),
      (none, (List.range 17).map fun k => UniSound.scalarAt π.proof.stream (536 + 24 * k))] := by
  unfold p2Msgs
  simp only [RecPiop.pi2Rounds, UniSound.msgsAt, UniSound.roundBytes, ↓reduceIte, Bool.false_eq_true,
    Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, List.range_zero, List.map_nil]

theorem pubBytes_toList (b : Array UInt8) (h : pLen ≤ b.size) : (pubBytes b).toList = UniSound.bytesAt b 0 pLen := by
  rw [UniSound.bytesAt_eq_map b 0 pLen (by omega)]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [pubBytes]

/-- **The bytes the chain absorbs** are `p2Es`: the public data and `W`'s root, then `Q`'s root, then the values. -/
theorem absorbsS_p2 (π : P2Pf) (h : π.proof.stream.size = sLen) :
    pi2Spec.absorbsS (p2View π).1 pi2Spec.K.rounds (p2View π).2 = p2Es π.proof.stream := by
  have hb : π.proof.stream.size = 944 := h
  have h1 : pi2Spec.pre = fun s => s.2.2.toList := rfl
  have h2 : pi2Spec.enc = UniSound.uniEnc := rfl
  have hf : pi2Spec.encAt (p2View π).1 = fun j m => if j = 0 then (pubBytes π.proof.stream).toList ++
      UniSound.uniEnc m else UniSound.uniEnc m := by
    funext j m
    have h3 : (p2View π).1 = (π.iv, π.input, pubBytes π.proof.stream) := rfl
    rw [ChainSpecU.encAt, h1, h2, h3]
  have hv : (p2View π).2 = (UniSound.msgsAt π.proof.stream pLen (RecPiop.pi2Rounds 4)).map UniSound.toRMsg := rfl
  have hr : UniSound.roundsBytes (RecPiop.pi2Rounds 4) = 472 := roundsBytes_pi2
  rw [ChainSpecU.absorbsS, hf, hv, pi2Spec_rounds,
    UniSound.absorbsI_wAbs _ _ 0 pLen _ (hr ▸ hb ▸ (by decide : pLen + 472 ≤ 944)),
    pubBytes_toList _ (hb ▸ (by decide : pLen ≤ 944))]
  simp only [↓reduceIte, p2Es, RecPiop.pi2Rounds, UniSound.wAbs, UniSound.roundBytes]
  simp only [↓reduceIte, Bool.false_eq_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, List.replicate,
    List.nil_append, List.cons_append, List.cons.injEq, and_true]
  rw [← UniSound.bytesAt_add_of _ (show 0 + pLen = pLen from rfl)]

theorem getD_take_map {α : Type} (l : List α) (n i : ℕ) (d : α) (h : i < n) : (l.take n).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ite_true]

theorem getD_drop {α : Type} (l : List α) (n i : ℕ) (d : α) : (l.drop n).getD i d = l.getD (n + i) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The transcript's inputs** at the chain's challenges. -/
theorem p2Inputs_eq (π : P2Pf) (h : π.proof.stream.size = sLen) (sts : List Bytes32) :
    p2Inputs π (groupK (RecPiop.pi2Rounds 4) (sts.map (chalL UniSound.uLimbs))) =
      ⟨foldReads Read.bytes pubsStep π.proof.stream 0 Data.reads (publicWordsOf π.input.toList),
        (sts.map (chalL UniSound.uLimbs)).getD 0 0, (sts.map (chalL UniSound.uLimbs)).getD 1 0,
        (sts.map (chalL UniSound.uLimbs)).getD 2 0, (sts.map (chalL UniSound.uLimbs)).getD 3 0,
        UniSound.scalarsAt π.proof.stream 536 16, UniSound.scalarAt π.proof.stream 920,
        (sts.map (chalL UniSound.uLimbs)).getD 4 0⟩ := by
  have hb : π.proof.stream.size = 944 := h
  have hs : (stOf (p2View π).1).2 =
      foldReads Read.bytes pubsStep π.proof.stream 0 Data.reads (publicWordsOf π.input.toList) := by
    show pi2Pubs (Spec.of cc) π.input.toList (pubBytes π.proof.stream).toArray = _
    rw [pi2Pubs_pubBytes _ _ (by rw [hb]; decide)]
    unfold pi2Pubs
    rw [spec_reads]
  unfold p2Inputs
  rw [hs, p2Msgs_eq]
  simp only [groupK, RecPiop.pi2Rounds, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd]
  simp only [getD_take_map _ _ _ _ (by norm_num : (0 : ℕ) < 3), getD_take_map _ _ _ _ (by norm_num : (1 : ℕ) < 3),
    getD_take_map _ _ _ _ (by norm_num : (2 : ℕ) < 3), getD_take_map _ _ _ _ (by norm_num : (0 : ℕ) < 1),
    getD_drop, Nat.reduceAdd]
  have ha : List.take 16 (List.map (fun k => UniSound.scalarAt π.proof.stream (536 + 24 * k)) (List.range 17)) =
      UniSound.scalarsAt π.proof.stream 536 16 := by
    rw [← List.map_take, List.take_range]
    rfl
  have hξ : (List.map (fun k => UniSound.scalarAt π.proof.stream (536 + 24 * k)) (List.range 17)).getD 16 0 =
      UniSound.scalarAt π.proof.stream 920 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num)]
    rfl
  rw [ha, hξ]

/-- **The run's result is `p2Reduced`** at the chain's challenges. -/
theorem red0_eq (π : P2Pf) (h : π.proof.stream.size = sLen) (sts : List Bytes32) :
    red0 (publicWordsOf π.input.toList) π.proof.stream sts =
      p2Reduced π (groupK (RecPiop.pi2Rounds 4) (sts.map (chalL UniSound.uLimbs))) := by
  unfold red0 p2Reduced p2Out
  rw [p2Inputs_eq π h sts, p2Msgs_eq]
  rfl

/-! ## WALK -/

/-- **WALK**: on a stream of `944` bytes, π2's run is the chain over `keccak256With F`, its verdict and result read
off `p2Reduced` at the chain's challenges. -/
theorem pi2Walk : Pi2Walk := by
  intro m _ _ F π hlen
  unfold RecStatement.runWith
  dsimp only
  rw [UniSound.keccak_eq, bind_map_left]
  change _ = _ <$> pi2Spec.chain (UniSound.kB F) _ _
  rw [UniSound.chainU_eq, absorbsS_p2 π hlen, map_bind, map_bind]
  refine bind_eq_of rfl fun st0 => ?_
  rw [reduceWith_bind_run F π.proof.stream hlen _ (ofB st0), UniSound.toB_ofB]
  simp only [finish_cw π.proof.stream hlen, ExceptT.run_pure, StateT.run_pure, bind_assoc, pure_bind, map_bind,
    map_pure, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun sts => ?_
  simp only [Function.comp_apply, red0_eq π hlen sts]
  rfl

end RecCompose

/-- info: 'RecCompose.pi2Walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Walk

/-- info: 'RecCompose.pi2WalkReject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2WalkReject

/-- info: 'RecCompose.pi2Scalars_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Scalars_real
