-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The walk is `UniStatement.runWith`
-- (`formal/UniStatement/UniStatement/Run.lean`), the chain `Compose.ChainSpecU.chain`
-- (`formal/Compose/Compose/ListChainU.lean`); the byte facts follow `formal/EndToEnd/Bridge/Chain.lean`.
import UniSound.FsWalk
import Bridge.Chain

/-!
# The walk is the chain (`UniWalk`, `UniWalkReject`)
-/

set_option linter.unusedSectionVars false

namespace UniSound

open Compose QuotientRpm LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics UniStatement
open OracleSpec OracleComp

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## The stream's bytes -/

/-- The stream's `n` bytes from byte `s`. -/
def bytesAt (b : Array UInt8) (s n : ℕ) : List UInt8 := (b.toList.drop s).take n

theorem bytesAt_add (b : Array UInt8) (s n k : ℕ) :
    bytesAt b s (n + k) = bytesAt b s n ++ bytesAt b (s + n) k := by
  simp only [bytesAt, List.take_add, List.drop_drop]

theorem bytesAt_add_of (b : Array UInt8) {s n k t : ℕ} (h : s + n = t) :
    bytesAt b s (n + k) = bytesAt b s n ++ bytesAt b t k := by
  subst h
  exact bytesAt_add b s n k

theorem toList_extract_eq (b : Array UInt8) (a c : ℕ) :
    (b.extract a c).toList = bytesAt b a (c - a) := by
  simp only [Array.toList_extract, List.extract_eq_take_drop, bytesAt]

theorem getD_toList (b : Array UInt8) (i : ℕ) : b.toList.getD i 0 = b.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

theorem bytesAt_eq_map (b : Array UInt8) (s n : ℕ) (h : s + n ≤ b.size) :
    bytesAt b s n = (List.range n).map fun j => b.getD (s + j) 0 := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_take, List.length_drop, Array.length_toList, List.length_map,
      List.length_range]
    omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      Array.getElem_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : s + i < b.size),
      Option.getD_some]

theorem beWordAt_eq_beWord (b : Array UInt8) (s : ℕ) :
    beWordAt b s = PcsQuotient.Transcript.beWord b.toList s := by
  simp only [beWordAt, PcsQuotient.Transcript.beWord, getD_toList]

theorem be64_beWordAt (b : Array UInt8) (s : ℕ) (h : s + 8 ≤ b.size) :
    QuotientRpm.be64 (beWordAt b s) = bytesAt b s 8 := by
  rw [beWordAt_eq_beWord, Bridge.beWord_eq _ _ (by simpa using h),
    be64_ofBe64 _ (by simp only [List.length_drop, Array.length_toList]; omega)]
  rfl

theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ {l : List α} (init : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: l, init, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self init]
    exact foldl_congr_mem _ fun y hy acc => h y (List.mem_cons_of_mem _ hy) acc

theorem getD_extract (b : Array UInt8) (o n i : ℕ) (h : o + n ≤ b.size) (hi : i < n) :
    (b.extract o (o + n)).getD i 0 = b.getD (o + i) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  rw [ite_eq_left (by omega)]

theorem beWordAt_extract (b : Array UInt8) (o n k : ℕ) (h : o + n ≤ b.size) (hk : k + 8 ≤ n) :
    beWordAt (b.extract o (o + n)) k = beWordAt b (o + k) := by
  unfold beWordAt
  apply foldl_congr_mem
  intro j hj acc
  rw [getD_extract b o n (k + j) h (by simp only [List.mem_range] at hj; omega), Nat.add_assoc]

theorem uLimbs_eNew (a b c : UInt64) : uLimbs (eNew a b c) = (a, b, c) :=
  uLimbs.apply_symm_apply (a, b, c)

theorem bytesAt_24 (b : Array UInt8) (o : ℕ) :
    bytesAt b o 24 = bytesAt b o 8 ++ bytesAt b (o + 8) 8 ++ bytesAt b (o + 16) 8 := by
  rw [← bytesAt_add_of b (rfl : o + 8 = o + 8), ← bytesAt_add_of b (by omega : o + (8 + 8) = o + 16)]

theorem bytesAt_32 (b : Array UInt8) (o : ℕ) :
    bytesAt b o 32 =
      bytesAt b o 8 ++ bytesAt b (o + 8) 8 ++ (bytesAt b (o + 16) 8 ++ bytesAt b (o + 24) 8) := by
  rw [← bytesAt_add_of b (rfl : o + 8 = o + 8), ← bytesAt_add_of b (rfl : o + 16 + 8 = o + 16 + 8),
    ← bytesAt_add_of b (by omega : o + (8 + 8) = o + 16)]

/-- **A scalar as the stream carries it** is the stream's 24 bytes it is read from. -/
theorem scalar24_scalarAt (b : Array UInt8) (o : ℕ) (h : o + 24 ≤ b.size) :
    scalar24 (scalarAt b o) = bytesAt b o 24 := by
  rw [scalar24, scalarAt, uLimbs_eNew, be64_beWordAt b o (by omega),
    be64_beWordAt b (o + 8) (by omega), be64_beWordAt b (o + 16) (by omega), bytesAt_24]

theorem revRoot_vec (w0 w1 w2 w3 : UInt64) :
    revRoot (toB #v[w0, w1, w2, w3]) =
      QuotientRpm.be64 w1 ++ QuotientRpm.be64 w0 ++ (QuotientRpm.be64 w3 ++ QuotientRpm.be64 w2) := by
  have hl : (toB #v[w0, w1, w2, w3]).toList =
      (wordBytes w0 ++ wordBytes w1) ++ (wordBytes w2 ++ wordBytes w3) := by
    rw [Bridge.toB_toList]
    simp [digestBytes]
  have h16 : (wordBytes w0 ++ wordBytes w1).length = 16 := by
    simp [wordBytes_length]
  rw [revRoot, hl, List.take_left' h16, List.drop_left' h16, List.reverse_append,
    List.reverse_append]
  rfl

theorem rootOf_halvesAt (b : Array UInt8) (o : ℕ) :
    UniStatement.rootOf (halvesAt b o) =
      #v[beWordAt b (o + 8), beWordAt b o, beWordAt b (o + 24), beWordAt b (o + 16)] := by
  have e : ∀ x y : UInt64, IsCanonical128 (eNew x y 0) := fun _ _ => rfl
  unfold UniStatement.rootOf digestOfScalars halvesAt
  rw [ite_eq_left ⟨e _ _, e _ _⟩]
  rfl

/-- **A root as the stream carries it** is the stream's 32 bytes it is read from. -/
theorem revRoot_halvesAt (b : Array UInt8) (o : ℕ) (h : o + 32 ≤ b.size) :
    revRoot (toB (UniStatement.rootOf (halvesAt b o))) = bytesAt b o 32 := by
  rw [rootOf_halvesAt, revRoot_vec, be64_beWordAt b o (by omega), be64_beWordAt b (o + 8) (by omega),
    be64_beWordAt b (o + 16) (by omega), be64_beWordAt b (o + 24) (by omega), bytesAt_32]

/-- The stream's `n` scalars from byte `o`. -/
def scalarsAt (b : Array UInt8) (o n : ℕ) : List E := (List.range n).map fun k => scalarAt b (o + 24 * k)

theorem scalarsAt_zero (b : Array UInt8) (o : ℕ) : scalarsAt b o 0 = [] := rfl

theorem scalarsAt_succ (b : Array UInt8) (o n : ℕ) :
    scalarsAt b o (n + 1) = scalarAt b o :: scalarsAt b (o + 24) n := by
  simp only [scalarsAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    Nat.add_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem scalars24_scalarsAt (b : Array UInt8) :
    ∀ (n o : ℕ), o + 24 * n ≤ b.size → scalars24 (scalarsAt b o n) = bytesAt b o (24 * n)
  | 0, o, _ => by simp [scalarsAt_zero, scalars24, bytesAt]
  | n + 1, o, h => by
    rw [scalarsAt_succ, show 24 * (n + 1) = 24 + 24 * n by ring, bytesAt_add]
    simp only [scalars24, List.flatMap_cons]
    rw [scalar24_scalarAt b o (by omega)]
    congr 1
    exact scalars24_scalarsAt b n (o + 24) (by omega)

/-- **A round's message as the channel reads it** from byte `o` (`msgsAt`'s head). -/
def msgOf (b : Array UInt8) (o : ℕ) (r : RoundSpec) : UMsg :=
  ((if r.root then some (halvesAt b o) else none),
    (List.range r.nv).map fun k => scalarAt b (o + (if r.root then 32 else 0) + 24 * k))

theorem msgsAt_cons (b : Array UInt8) (o : ℕ) (r : RoundSpec) (rs : List RoundSpec) :
    msgsAt b o (r :: rs) = msgOf b o r :: msgsAt b (o + roundBytes r) rs := rfl

/-- **A round's message as the chain hashes it** is the stream's bytes it is read from. -/
theorem uniEnc_msgOf (b : Array UInt8) (o : ℕ) (r : RoundSpec) (h : o + roundBytes r ≤ b.size) :
    uniEnc (toRMsg (msgOf b o r)) = bytesAt b o (roundBytes r) := by
  rcases r with ⟨root, nv, ns⟩
  cases root with
  | false =>
    simp only [roundBytes, Bool.false_eq_true, ite_false, Nat.zero_add] at h ⊢
    have := scalars24_scalarsAt b nv o h
    simp only [scalarsAt] at this
    simpa [msgOf, toRMsg, uniEnc] using this
  | true =>
    simp only [roundBytes, ite_true] at h ⊢
    rw [bytesAt_add, ← revRoot_halvesAt b o (by omega), ← scalars24_scalarsAt b nv (o + 32) (by omega)]
    rfl

/-! ## The bytes each sample absorbs -/

/-- **The bytes the samples absorb**, round by round from byte `o`: a round's first sample the bytes
not yet absorbed (`pre`, then the round's message), its other samples nothing. -/
def wAbs (b : Array UInt8) : ℕ → List UInt8 → List RoundSpec → List (List UInt8)
  | _, _, [] => []
  | o, pre, r :: rs =>
    (pre ++ bytesAt b o (roundBytes r)) :: (List.replicate r.ns [] ++ wAbs b (o + roundBytes r) [] rs)

/-- **The chain absorbs what the walk absorbs**: the encoding of the stream's messages at round
`i`, round `0`'s after the statement's bytes `pre`, are the stream's bytes. -/
theorem absorbsI_wAbs (b : Array UInt8) (pre : List UInt8) :
    ∀ (i o : ℕ) (rs : List RoundSpec), o + roundsBytes rs ≤ b.size →
      absorbsI (fun j m => if j = 0 then pre ++ uniEnc m else uniEnc m) i rs
          ((msgsAt b o rs).map toRMsg) =
        wAbs b o (if i = 0 then pre else []) rs
  | _, _, [], _ => rfl
  | i, o, r :: rs, h => by
    simp only [roundsBytes] at h
    rw [msgsAt_cons, List.map_cons, absorbsI, List.headD_cons, List.tail_cons, wAbs,
      absorbsI_wAbs b pre (i + 1) (o + roundBytes r) rs (by omega), uniEnc_msgOf b o r (by omega)]
    simp only [Nat.add_one_ne_zero, ite_false]
    split_ifs <;> simp

/-- The row counts' 24 bytes are the stream's first 24. -/
theorem rowBytes_toList (b : Array UInt8) (h : 24 ≤ b.size) : (rowBytes b).toList = bytesAt b 0 24 := by
  rw [bytesAt_eq_map b 0 24 (by omega)]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [rowBytes]

/-! ## The channel's reads -/

section Defs

variable {m : Type → Type} [Monad m]

/-- Keccak-256 over `F`, its digests as bytes: the chain's hash. -/
def kB (F : KeccakState → m KeccakState) (x : List UInt8) : m Bytes32 := toB <$> keccak256With F x

/-- **The chain's answers from a state**: each step's input the state, then the step's bytes. -/
def steps (H : List UInt8 → m Bytes32) : Bytes32 → List (List UInt8) → m (List Bytes32)
  | _, [] => pure []
  | st, e :: es => H (stepIn st e) >>= fun st' => (st' :: ·) <$> steps H st' es

end Defs

/-- The bytes read and not yet absorbed. -/
def preOf (c : Chan) : List UInt8 := (c.data.extract c.absorbed c.cursor).toList

/-- The channel after one sample answered `st`. -/
def sampOne (c : Chan) (st : Bytes32) : Chan :=
  { c with absorbed := c.cursor, state := ofB st, challenges := c.challenges.push (chalL uLimbs st) }

/-- The channel after samples answered `sts`. -/
def sampChan (c : Chan) (sts : List Bytes32) : Chan :=
  { c with
    absorbed := c.cursor
    state := ofB (sts.getLastD (toB c.state))
    challenges := (sts.map (chalL uLimbs)).foldl Array.push c.challenges }

/-- A row count as `nextInteger 4` reads it from byte `o`. -/
def intAt (b : Array UInt8) (o : ℕ) : ℕ := (b.extract o (o + 4)).foldl (fun acc x => acc * 256 + x.toNat) 0

/-- The `n` row counts from byte `o`. -/
def countsAt (b : Array UInt8) (o n : ℕ) : List ℕ := (List.range n).map fun k => intAt b (o + 4 * k)

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem run_bind_ok {α β : Type} {x : ChanM m α} {K : α → ChanM m β} {c c' : Chan} {a : α}
    (h : x.run.run c = pure (.ok a, c')) : (x >>= K).run.run c = (K a).run.run c' := by
  simp only [ExceptT.run_bind, StateT.run_bind, h, pure_bind]

theorem run_pure_chan {α : Type} (a : α) (c : Chan) :
    (pure a : ChanM m α).run.run c = pure (.ok a, c) := rfl

theorem toB_ofB (b : Bytes32) : toB (ofB b) = b := LeanVM.Rpm.digestToRpm_ofRpm b

theorem keccak_eq (F : KeccakState → m KeccakState) (x : List UInt8) :
    keccak256With F x = (fun b => ofB b) <$> kB F x := by
  simp only [kB, Functor.map_map, Soundness.ofB_toB_root, id_map']

theorem chalL_eq (st : Bytes32) : PcsQuotient.Transcript.challengeOf (ofB st) = chalL uLimbs st := by
  rw [Bridge.challengeOf_eq, toB_ofB]
  rfl

theorem lift_run {α : Type} (x : m α) (c : Chan) :
    (ExceptT.lift (StateT.lift x) : ChanM m α).run.run c = x >>= fun a => pure (.ok a, c) := by
  simp only [ExceptT.run_lift, StateT.run_map, StateT.run_lift, map_bind, map_pure]

/-- **A sample**: the hash of the state and the bytes not yet absorbed. -/
theorem sample_bind {β : Type} (F : KeccakState → m KeccakState) (K : E → ChanM m β) (c : Chan) :
    (sample F >>= K).run.run c = kB F (stepIn (toB c.state) (preOf c)) >>= fun st =>
      (K (chalL uLimbs st)).run.run (sampOne c st) := by
  have hin : digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList =
      stepIn (toB c.state) (preOf c) := by
    rw [stepIn, Bridge.toB_toList]
    rfl
  simp only [sample, bind_assoc, ExceptT.run_bind, StateT.run_bind, chan_get_run, pure_bind, liftM,
    monadLift, MonadLift.monadLift, lift_run, chan_set_run, hin, keccak_eq,
    bind_map_left, chalL_eq]
  rfl

theorem sampChan_nil (c : Chan) (h : c.absorbed = c.cursor) : sampChan c [] = c := by
  rcases c with ⟨d, cu, ab, st, ch, z⟩
  simp only at h
  subst h
  simp only [sampChan, List.getLastD_nil, Soundness.ofB_toB_root, List.map_nil, List.foldl_nil]

theorem sampChan_sampOne (c : Chan) (st : Bytes32) (sts : List Bytes32) :
    sampChan (sampOne c st) sts = sampChan c (st :: sts) := by
  simp only [sampChan, sampOne, List.getLastD_cons, toB_ofB, List.map_cons, List.foldl_cons]

theorem preOf_self (c : Chan) (h : c.absorbed = c.cursor) : preOf c = [] := by
  simp only [preOf, toList_extract_eq, h, Nat.sub_self, bytesAt, List.take_zero]

theorem toB_sampOne (c : Chan) (st : Bytes32) : toB (sampOne c st).state = st := toB_ofB st

/-- **Samples after the bytes are absorbed**: each the hash of the state alone. -/
theorem repeat_sample_bind {β : Type} (F : KeccakState → m KeccakState) :
    ∀ (n : ℕ) (K : List E → ChanM m β) (c : Chan), c.absorbed = c.cursor →
      (FlockSound.Uni.repeatM (sample F) n >>= K).run.run c =
        steps (kB F) (toB c.state) (List.replicate n []) >>= fun sts =>
          (K (sts.map (chalL uLimbs))).run.run (sampChan c sts)
  | 0, K, c, h => by
    simp only [FlockSound.Uni.repeatM, pure_bind, List.replicate_zero, steps, List.map_nil,
      sampChan_nil c h]
  | n + 1, K, c, h => by
    simp only [FlockSound.Uni.repeatM, bind_assoc, pure_bind]
    rw [sample_bind]
    simp only [List.replicate_succ, steps, preOf_self c h, bind_assoc, bind_map_left]
    congr 1
    funext st
    rw [repeat_sample_bind F n (fun l => K (chalL uLimbs st :: l)) (sampOne c st) rfl]
    simp only [toB_sampOne, sampChan_sampOne, List.map_cons]

/-- **A round's samples**: the first absorbs the bytes not yet absorbed, the others nothing. -/
theorem samples_succ_bind {β : Type} (F : KeccakState → m KeccakState) (n : ℕ)
    (K : List E → ChanM m β) (c : Chan) :
    (samples F (n + 1) >>= K).run.run c =
      steps (kB F) (toB c.state) (preOf c :: List.replicate n []) >>= fun sts =>
        (K (sts.map (chalL uLimbs))).run.run (sampChan c sts) := by
  rw [FlockSound.Uni.samples_eq]
  simp only [FlockSound.Uni.repeatM, bind_assoc, pure_bind]
  rw [sample_bind]
  simp only [steps, bind_assoc, bind_map_left]
  congr 1
  funext st
  rw [repeat_sample_bind F n (fun l => K (chalL uLimbs st :: l)) (sampOne c st) rfl]
  simp only [toB_sampOne, sampChan_sampOne, List.map_cons]

/-! ### Fixed reads -/

theorem takeBytes_ok (n : ℕ) (c : Chan) (h : c.cursor + n ≤ c.data.size) :
    (takeBytes (m := m) n).run.run c =
      pure (.ok (c.data.extract c.cursor (c.cursor + n)), { c with cursor := c.cursor + n }) := by
  rw [takeBytes_run, ite_eq_left h]

theorem nextScalar_ok (c : Chan) (h : c.cursor + 24 ≤ c.data.size) :
    (nextScalar (m := m)).run.run c =
      pure (.ok (scalarAt c.data c.cursor), { c with cursor := c.cursor + 24 }) := by
  simp only [nextScalar, ExceptT.run_bind, StateT.run_bind, takeBytes_ok 24 c h, pure_bind,
    ExceptT.run_pure, StateT.run_pure]
  rw [beWordAt_extract c.data c.cursor 24 16 h (by norm_num),
    beWordAt_extract c.data c.cursor 24 8 h (by norm_num),
    beWordAt_extract c.data c.cursor 24 0 h (by norm_num)]
  rfl

theorem nextScalars_ok (n : ℕ) (c : Chan) (h : c.cursor + 24 * n ≤ c.data.size) :
    (nextScalars (m := m) n).run.run c =
      pure (.ok (scalarsAt c.data c.cursor n), { c with cursor := c.cursor + 24 * n }) := by
  rw [FlockSound.Uni.nextScalars_eq]
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [FlockSound.Uni.repeatM]
    rw [run_bind_ok (nextScalar_ok c (by omega)),
      run_bind_ok (ih { c with cursor := c.cursor + 24 } (by dsimp only; omega)), scalarsAt_succ,
      show c.cursor + 24 * (n + 1) = c.cursor + 24 + 24 * n by ring]
    rfl

theorem nextRoot_ok (c : Chan) (h : c.cursor + 32 ≤ c.data.size) :
    (nextRoot (m := m)).run.run c =
      pure (.ok (halvesAt c.data c.cursor), { c with cursor := c.cursor + 32 }) := by
  simp only [nextRoot, ExceptT.run_bind, StateT.run_bind, takeBytes_ok 16 c (by omega), pure_bind]
  rw [takeBytes_ok 16 _ (by dsimp only; omega)]
  simp only [pure_bind, ExceptT.run_pure, StateT.run_pure]
  rw [beWordAt_extract c.data c.cursor 16 8 (by omega) (by norm_num),
    beWordAt_extract c.data c.cursor 16 0 (by omega) (by norm_num),
    beWordAt_extract c.data (c.cursor + 16) 16 8 (by omega) (by norm_num),
    beWordAt_extract c.data (c.cursor + 16) 16 0 (by omega) (by norm_num)]
  rfl

theorem rootRead_ok (r : Bool) (c : Chan) (h : c.cursor + (if r then 32 else 0) ≤ c.data.size) :
    (rootRead (m := m) r).run.run c =
      pure (.ok (if r then some (halvesAt c.data c.cursor) else none),
        { c with cursor := c.cursor + (if r then 32 else 0) }) := by
  cases r with
  | false => rfl
  | true =>
    simp only [ite_true] at h ⊢
    simp only [rootRead, ite_true, map_eq_bind_pure_comp]
    rw [run_bind_ok (nextRoot_ok c h)]
    rfl

theorem nextInteger_ok (c : Chan) (h : c.cursor + 4 ≤ c.data.size) :
    (nextInteger (m := m) 4).run.run c = pure (.ok (intAt c.data c.cursor), { c with cursor := c.cursor + 4 }) := by
  simp only [nextInteger, ExceptT.run_bind, StateT.run_bind, takeBytes_ok 4 c h, pure_bind,
    ExceptT.run_pure, StateT.run_pure]
  rfl

theorem requireZero_run (z : E) (c : Chan) :
    (requireZero (m := m) z).run.run c = pure (.ok (), collectZ c [z]) := chan_modify_run c _

theorem collectZ_collectZ (c : Chan) (zs ws : List E) :
    collectZ (collectZ c zs) ws = collectZ c (zs ++ ws) := by
  simp only [collectZ, List.foldl_append]

theorem readCount_ok (r : ℕ) (c : Chan) (h : c.cursor + 4 ≤ c.data.size) :
    (readCount (m := m) r).run.run c =
      pure (.ok (intAt c.data c.cursor), collectZ { c with cursor := c.cursor + 4 }
        [intBits (intAt c.data c.cursor) (r + 1) 32,
          intBits (intAt c.data c.cursor) r 1 * intBits (intAt c.data c.cursor) 0 r]) := by
  simp only [readCount]
  rw [run_bind_ok (nextInteger_ok c h), run_bind_ok (requireZero_run _ _),
    run_bind_ok (requireZero_run _ _), collectZ_collectZ]
  rfl

theorem countsAt_succ (b : Array UInt8) (o n : ℕ) :
    countsAt b o (n + 1) = intAt b o :: countsAt b (o + 4) n := by
  simp only [countsAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    Nat.add_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  congr 1
  omega

/-- **The row counts**: `readCounts` reads `4` bytes a height and collects `countZeros`. -/
theorem readCounts_ok : ∀ (hs : List ℕ) (c : Chan), c.cursor + 4 * hs.length ≤ c.data.size →
    (readCounts (m := m) hs).run.run c =
      pure (.ok (countsAt c.data c.cursor hs.length),
        collectZ { c with cursor := c.cursor + 4 * hs.length }
          (countZeros hs (countsAt c.data c.cursor hs.length)))
  | [], c, _ => by
    simp only [readCounts, List.mapM_nil, List.length_nil]
    rfl
  | r :: hs, c, h => by
    simp only [List.length_cons] at h ⊢
    rw [readCounts_eq, List.mapM_cons, run_bind_ok (readCount_ok r c (by omega)), ← readCounts_eq,
      run_bind_ok (readCounts_ok hs _ (by simp only [collectZ]; omega)), countsAt_succ]
    simp only [collectZ, countZeros, List.zip_cons_cons, List.flatMap_cons, List.cons_append, List.nil_append, show c.cursor + 4 * (hs.length + 1) =
        c.cursor + 4 + 4 * hs.length by ring]
    rfl

end Monad

/-! ## The chain's answers -/

section Steps

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem runM_eq_steps (H : List UInt8 → m Bytes32) :
    ∀ (y : List UInt8) (es : List (List UInt8)),
      runM H y es = H y >>= fun st => (st :: ·) <$> steps H st es
  | y, [] => by simp only [runM, steps, map_pure]
  | y, e :: es => by
    simp only [runM, steps, runM_eq_steps H _ es, bind_assoc, map_eq_bind_pure_comp,
      Function.comp_def]

theorem steps_append (H : List UInt8 → m Bytes32) :
    ∀ (st : Bytes32) (es₁ es₂ : List (List UInt8)),
      steps H st (es₁ ++ es₂) = steps H st es₁ >>= fun l₁ =>
        (l₁ ++ ·) <$> steps H (l₁.getLastD st) es₂
  | st, [], es₂ => by simp [steps]
  | st, e :: es₁, es₂ => by
    simp only [List.cons_append, steps, steps_append H _ es₁ es₂, map_bind, bind_assoc,
      bind_map_left, Functor.map_map, List.getLastD_cons]

/-- A list of answers cut or padded to length `n`. -/
def fixB (n : ℕ) (l : List Bytes32) : List Bytes32 := (List.range n).map fun i => l.getD i default

@[simp] theorem length_fixB (n : ℕ) (l : List Bytes32) : (fixB n l).length = n := by simp [fixB]

theorem fixB_succ_cons (n : ℕ) (x : Bytes32) (l : List Bytes32) :
    fixB (n + 1) (x :: l) = x :: fixB n l := by
  simp [fixB, List.range_succ_eq_map, Function.comp_def]

theorem steps_fix (H : List UInt8 → m Bytes32) :
    ∀ (st : Bytes32) (es : List (List UInt8)), steps H st es = fixB es.length <$> steps H st es
  | st, [] => by simp [steps, fixB]
  | st, e :: es => by
    conv_lhs => rw [steps]
    rw [steps]
    simp only [map_bind, Functor.map_map, List.length_cons, fixB_succ_cons]
    congr 1
    funext st'
    conv_lhs => rw [steps_fix H st' es]
    rw [Functor.map_map]

end Steps

/-! ## A chain program on a stream of the bytes it reads -/

/-- The channel after a round: its message read, its zeros `zs` collected, its samples answered
`sts`. -/
def roundChan (c : Chan) (r : RoundSpec) (zs : List E) (sts : List Bytes32) : Chan :=
  sampChan (collectZ { c with cursor := c.cursor + (if r.root then 32 else 0) + 24 * r.nv } zs) sts

theorem foldl_push_toList (zs : List E) :
    ∀ (arr : Array E), (zs.foldl Array.push arr).toList = arr.toList ++ zs := by
  intro arr
  simp

theorem roundChan_data (c : Chan) (r : RoundSpec) (zs : List E) (sts : List Bytes32) :
    (roundChan c r zs sts).data = c.data := rfl

theorem roundChan_cursor (c : Chan) (r : RoundSpec) (zs : List E) (sts : List Bytes32) :
    (roundChan c r zs sts).cursor = c.cursor + roundBytes r := by
  simp only [roundChan, sampChan, collectZ, roundBytes, Nat.add_assoc]

theorem roundChan_state (c : Chan) (r : RoundSpec) (zs : List E) (sts : List Bytes32) :
    toB (roundChan c r zs sts).state = sts.getLastD (toB c.state) := by
  simp only [roundChan, sampChan, collectZ, toB_ofB]

theorem preOf_roundChan (c : Chan) (r : RoundSpec) (zs : List E) (sts : List Bytes32) :
    preOf (roundChan c r zs sts) = [] := preOf_self _ rfl

theorem roundChan_zeros (c : Chan) (r : RoundSpec) (zs : List E) (sts : List Bytes32) :
    (roundChan c r zs sts).zeros.toList = c.zeros.toList ++ zs := by
  simp only [roundChan, sampChan, collectZ, foldl_push_toList]

theorem preOf_round (c : Chan) (r : RoundSpec) (zs : List E) (hab : c.absorbed ≤ c.cursor) :
    preOf (collectZ { c with cursor := c.cursor + (if r.root then 32 else 0) + 24 * r.nv } zs) =
      preOf c ++ bytesAt c.data c.cursor (roundBytes r) := by
  simp only [preOf, collectZ, toList_extract_eq]
  rw [show c.cursor + (if r.root then 32 else 0) + 24 * r.nv - c.absorbed =
      (c.cursor - c.absorbed) + roundBytes r by unfold roundBytes; omega,
    bytesAt_add_of c.data (show c.absorbed + (c.cursor - c.absorbed) = c.cursor by omega)]

section Monad

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **A round of a chain program**: its root and scalars the stream's (`msgOf`), its zeros
collected, its samples the chain's steps on the bytes not yet absorbed then nothing. -/
theorem round_bind {β : Type} (F : KeccakState → m KeccakState) (r : RoundSpec)
    (Z : UMsg → List E) (K : UMsg → List E → ChanM m β) (c : Chan) (hab : c.absorbed ≤ c.cursor)
    (hsz : c.cursor + roundBytes r ≤ c.data.size) :
    (do
      let root ← rootRead (m := m) r.root
      let vals ← nextScalars (m := m) r.nv
      ChainProg.requireZeros (Z (root, vals))
      let chs ← samples F (r.ns + 1)
      K (root, vals) chs).run.run c =
    steps (kB F) (toB c.state)
        ((preOf c ++ bytesAt c.data c.cursor (roundBytes r)) :: List.replicate r.ns []) >>= fun sts =>
      (K (msgOf c.data c.cursor r) (sts.map (chalL uLimbs))).run.run
        (roundChan c r (Z (msgOf c.data c.cursor r)) sts) := by
  unfold roundBytes at hsz
  rw [run_bind_ok (rootRead_ok r.root c (by omega))]
  rw [run_bind_ok (nextScalars_ok r.nv { c with cursor := c.cursor + (if r.root then 32 else 0) }
    (by dsimp only; omega))]
  rw [run_bind_ok (requireZeros_run _ _), samples_succ_bind, ← preOf_round c r _ hab]
  rfl

/-- **The channel and transcript after the rounds**, from the hash answers. -/
def runOut {α : Type} (P : ChainProg α) : List RoundSpec → Done → Chan → List Bytes32 → Done × Chan
  | [], done, c, _ => (done, c)
  | r :: rs, done, c, sts =>
    runOut P rs (done ++ [(msgOf c.data c.cursor r, (sts.take (r.ns + 1)).map (chalL uLimbs))])
      (roundChan c r (P.zeros done (msgOf c.data c.cursor r)) (sts.take (r.ns + 1)))
      (sts.drop (r.ns + 1))

theorem length_round_steps (pre : List UInt8) (n : ℕ) :
    (pre :: List.replicate n ([] : List UInt8)).length = n + 1 := by simp

/-- **The rounds of a chain program**, on a stream holding their bytes: the chain's steps on
`wAbs`, the transcript and channel `runOut`. -/
theorem runRounds_run {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) :
    ∀ (rs : List RoundSpec) (done : Done) (c : Chan), c.absorbed ≤ c.cursor →
      c.cursor + roundsBytes rs ≤ c.data.size →
      (P.runRounds F rs done).run.run c =
        (fun sts => (Except.ok (runOut P rs done c sts).1, (runOut P rs done c sts).2)) <$>
          steps (kB F) (toB c.state) (wAbs c.data c.cursor (preOf c) rs)
  | [], done, c, _, _ => by
    simp only [ChainProg.runRounds, wAbs, steps, map_pure, runOut]
    rfl
  | r :: rs, done, c, hab, hsz => by
    simp only [roundsBytes] at hsz
    rw [runRounds_cons]
    refine (round_bind F r (P.zeros done) (fun msg chs => P.runRounds F rs (done ++ [(msg, chs)])) c
      hab (by omega)).trans ?_
    have IH : ∀ sts : List Bytes32,
        (P.runRounds F rs (done ++ [(msgOf c.data c.cursor r, sts.map (chalL uLimbs))])).run.run
            (roundChan c r (P.zeros done (msgOf c.data c.cursor r)) sts) =
          (fun sts' => (Except.ok (runOut P rs (done ++ [(msgOf c.data c.cursor r,
              sts.map (chalL uLimbs))]) (roundChan c r (P.zeros done (msgOf c.data c.cursor r)) sts) sts').1,
            (runOut P rs (done ++ [(msgOf c.data c.cursor r, sts.map (chalL uLimbs))])
              (roundChan c r (P.zeros done (msgOf c.data c.cursor r)) sts) sts').2)) <$>
            steps (kB F) (sts.getLastD (toB c.state))
              (wAbs c.data (c.cursor + roundBytes r) [] rs) := by
      intro sts
      rw [runRounds_run P F rs _ _ (le_of_eq rfl) (by rw [roundChan_cursor, roundChan_data]; omega),
        roundChan_state, roundChan_data, roundChan_cursor, preOf_roundChan]
    simp only [IH]
    rw [wAbs, ← List.cons_append, steps_append, map_bind]
    rw [steps_fix (kB F) (toB c.state) ((preOf c ++ bytesAt c.data c.cursor (roundBytes r)) ::
      List.replicate r.ns []), length_round_steps, bind_map_left, bind_map_left]
    congr 1
    funext l
    rw [Functor.map_map]
    congr 1
    funext sts'
    have hl := length_fixB (r.ns + 1) l
    simp only [runOut, List.take_left' hl, List.drop_left' hl]

/-- The program's result and channel, from the hash answers. -/
def progOut {α : Type} (P : ChainProg α) (c : Chan) (sts : List Bytes32) : Except UniError α × Chan :=
  (.ok (P.out (runOut P P.rounds [] c sts).1
      (scalarsAt (runOut P P.rounds [] c sts).2.data (runOut P P.rounds [] c sts).2.cursor P.tail)),
    collectZ { (runOut P P.rounds [] c sts).2 with
      cursor := (runOut P P.rounds [] c sts).2.cursor + 24 * P.tail }
      (P.tailZeros (runOut P P.rounds [] c sts).1
        (scalarsAt (runOut P P.rounds [] c sts).2.data (runOut P P.rounds [] c sts).2.cursor P.tail)))

theorem runOut_data {α : Type} (P : ChainProg α) :
    ∀ (rs : List RoundSpec) (done : Done) (c : Chan) (sts : List Bytes32),
      (runOut P rs done c sts).2.data = c.data
  | [], _, _, _ => rfl
  | r :: rs, done, c, sts => by
    rw [runOut, runOut_data P rs, roundChan_data]

theorem runOut_cursor {α : Type} (P : ChainProg α) :
    ∀ (rs : List RoundSpec) (done : Done) (c : Chan) (sts : List Bytes32),
      (runOut P rs done c sts).2.cursor = c.cursor + roundsBytes rs
  | [], _, _, _ => rfl
  | r :: rs, done, c, sts => by
    rw [runOut, runOut_cursor P rs, roundChan_cursor, roundsBytes, Nat.add_assoc]

theorem runOut_done {α : Type} (P : ChainProg α) :
    ∀ (rs : List RoundSpec) (done : Done) (c : Chan) (sts : List Bytes32),
      (runOut P rs done c sts).1 =
        done ++ (msgsAt c.data c.cursor rs).zip (groupK rs (sts.map (chalL uLimbs)))
  | [], _, _, _ => by simp [runOut, msgsAt]
  | r :: rs, done, c, sts => by
    rw [runOut, runOut_done P rs, roundChan_data, roundChan_cursor, msgsAt_cons, groupK]
    simp [List.map_take, List.map_drop]

/-- **The zeros the rounds collect**, each round's given the transcript before it. -/
def zerosFrom {α : Type} (P : ChainProg α) : Done → Done → List E
  | _, [] => []
  | d, x :: xs => P.zeros d x.1 ++ zerosFrom P (d ++ [x]) xs

theorem runOut_zeros {α : Type} (P : ChainProg α) :
    ∀ (rs : List RoundSpec) (done : Done) (c : Chan) (sts : List Bytes32),
      (runOut P rs done c sts).2.zeros.toList = c.zeros.toList ++
        zerosFrom P done ((msgsAt c.data c.cursor rs).zip (groupK rs (sts.map (chalL uLimbs))))
  | [], _, _, _ => by simp [runOut, msgsAt, zerosFrom]
  | r :: rs, done, c, sts => by
    rw [runOut, runOut_zeros P rs, roundChan_data, roundChan_cursor, roundChan_zeros, msgsAt_cons,
      groupK]
    simp [zerosFrom, List.map_take, List.map_drop]

theorem zerosFrom_iff {α : Type} (P : ChainProg α) : ∀ (d N : Done),
    (∀ z ∈ zerosFrom P d N, z = 0) ↔
      ∀ j (h : j < N.length), ∀ z ∈ P.zeros (d ++ N.take j) (N[j]'h).1, z = 0
  | d, [] => by simp [zerosFrom]
  | d, x :: N => by
    simp only [zerosFrom, List.mem_append]
    constructor
    · intro h j hj z hz
      cases j with
      | zero => exact h z (Or.inl (by simpa using hz))
      | succ j =>
        have h2 := (zerosFrom_iff P (d ++ [x]) N).mp (fun z hz => h z (Or.inr hz)) j
          (by simpa using hj) z (by simpa using hz)
        exact h2
    · intro h z hz
      rcases hz with hz | hz
      · exact h 0 (by simp) z (by simpa using hz)
      · refine (zerosFrom_iff P (d ++ [x]) N).mpr (fun j hj z hz => ?_) z hz
        exact h (j + 1) (by simpa using hj) z (by simpa using hz)

/-- **A chain program on a stream holding its bytes** (its rounds' and its tail's, from the
cursor): the chain's steps on `wAbs`, its result and channel `progOut`. -/
theorem progRun {α : Type} (P : ChainProg α) (F : KeccakState → m KeccakState) (c : Chan)
    (hab : c.absorbed ≤ c.cursor)
    (hsz : c.cursor + roundsBytes P.rounds + 24 * P.tail ≤ c.data.size) :
    (P.run F).run.run c =
      progOut P c <$> steps (kB F) (toB c.state) (wAbs c.data c.cursor (preOf c) P.rounds) := by
  simp only [ChainProg.run, ExceptT.run_bind, StateT.run_bind,
    runRounds_run P F P.rounds [] c hab (by omega), bind_map_left]
  rw [map_eq_bind_pure_comp]
  congr 1
  funext sts
  rw [nextScalars_ok P.tail _ (by rw [runOut_cursor, runOut_data]; omega)]
  simp only [pure_bind, StateT.run_bind, requireZeros_run, ExceptT.run_pure, StateT.run_pure,
    Function.comp_apply]
  rfl

end Monad

end UniSound
