-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient.Verifier
import WhirBridge.Verifier
import LeanVM.Protocol.WithHashBridge
import LeanVM.Protocol.Compile.Rom.Bridge
import LeanVM.Protocol.ExperimentBridge

/-!
# The statement's openings are F2's

The statement (`formal/Statement`, `PcsQuotient/Opening.lean`) and F2 (`formal/WhirBridge`) both
transcribe `crates/quotient/src/opening.rs`. Here the two transcriptions are proved equal:

* **the layouts** (`layoutTr`: the same five fields): `layoutTr_witnessLayout`,
  `layoutTr_wiringLayout`, `layoutTr_quotientLayout`, for every size (`Layout::hidden` and
  `Layout::new` transcribed twice, `layoutTr_hidden`, `layoutTr_ofChunks_zero`);
* **a claim's weight on the stack and the gadget's** (`stackWeight_eq`, `gadgetWeight_eq`), hence
  **the opening's stack claims** (`stackClaims_eq`: the statement's `stackClaims` is F2's
  `Layout.stacking.claims`);
* **the transcript's seed bytes** (`encoding_eq`: the layout's encoding, `claimBytes_eq`, the label);
* **the opening check** (`openingWith_eq`): for every monad and every permutation `F`, the statement's
  `openingWith F` is `openingVerifyIdWithHash (keccak256With F) F`, which is F2's
  `openingVerifyWithHash` but for the layout's id, hashed with the oracle (the statement) rather than
  the deployed Keccak-256 (F2's `openingPrefix`), and for an early rejection of a stream of fewer
  than two scalars before any query; `openingVerifyIdWithHash_eq_of_id`: when the oracle's hash of
  the layout's encoding is the deployed one, it is F2's `openingVerifyWithHash` for a function
  oracle (`Id`).
-/

namespace Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The translations -/

/-- A lane of the statement's layout as F2's. -/
def laneTr : PcsQuotient.Lane → WhirBridge.Lane
  | .block b => .block b
  | .overflow => .overflow
  | .random => .random

/-- **The statement's layout as F2's**: the same five fields. -/
def layoutTr (L : PcsQuotient.Layout) : WhirBridge.Layout :=
  ⟨L.vars, L.logN, L.lanes.map laneTr, L.logPiece, L.pieces⟩

/-- A claim of the statement as F2's. -/
def claimTr (c : PcsQuotient.Claim) : WhirBridge.Claim := ⟨c.point, c.value⟩

@[simp] theorem layoutTr_vars (L : PcsQuotient.Layout) : (layoutTr L).vars = L.vars := rfl
@[simp] theorem layoutTr_logN (L : PcsQuotient.Layout) : (layoutTr L).logN = L.logN := rfl
@[simp] theorem layoutTr_lanes (L : PcsQuotient.Layout) :
    (layoutTr L).lanes = L.lanes.map laneTr := rfl
@[simp] theorem layoutTr_logPiece (L : PcsQuotient.Layout) :
    (layoutTr L).logPiece = L.logPiece := rfl
@[simp] theorem layoutTr_pieces (L : PcsQuotient.Layout) : (layoutTr L).pieces = L.pieces := rfl
@[simp] theorem layoutTr_logLane (L : PcsQuotient.Layout) :
    (layoutTr L).logLane = L.logLane := rfl

@[simp] theorem claimTr_point (c : PcsQuotient.Claim) : (claimTr c).point = c.point := rfl
@[simp] theorem claimTr_value (c : PcsQuotient.Claim) : (claimTr c).value = c.value := rfl

theorem laneTr_injective : Function.Injective laneTr := by
  intro a b h
  cases a <;> cases b <;> simp_all [laneTr]

/-! ## The layouts -/

/-- The lanes of a hidden layout, as the statement lists them. -/
theorem hiddenLanes_eq (blocks : List ℕ) (random : ℕ) :
    WhirBridge.Layout.hiddenLanes blocks random =
      ((blocks.take (min blocks.length 32)).map PcsQuotient.Lane.block ++
        List.replicate (32 - min blocks.length 32) PcsQuotient.Lane.random ++
        [PcsQuotient.Lane.overflow] ++ List.replicate random PcsQuotient.Lane.random ++
        (blocks.drop (min blocks.length 32)).map PcsQuotient.Lane.block).map laneTr := by
  simp [WhirBridge.Layout.hiddenLanes, WhirBridge.overflowLane, List.map_map, Function.comp_def,
    laneTr]

theorem layoutTr_hidden (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) (random s : ℕ) :
    layoutTr (PcsQuotient.Layout.hidden vars logChunk logN chunks random s) =
      WhirBridge.Layout.hidden vars logChunk logN chunks random s := by
  simp only [PcsQuotient.Layout.hidden, WhirBridge.Layout.hidden, WhirBridge.Layout.hiddenBlocks,
    WhirBridge.Layout.hiddenTails, PcsQuotient.overflowLaneIndex, PcsQuotient.laneFold,
    WhirBridge.laneFold, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, hiddenLanes_eq, layoutTr]
  congr 2
  rw [List.filterMap_map]
  congr 1
  funext x
  cases x <;> rfl

/-- **The witness table's layout** (`witness_layout`) is F2's, at every size. -/
theorem layoutTr_witnessLayout (logRows : ℕ) :
    layoutTr (PcsQuotient.witnessLayout logRows) = WhirBridge.witnessLayout logRows := by
  rw [PcsQuotient.witnessLayout, layoutTr_hidden]
  rfl

theorem quotientChunks_eq (m : ℕ) :
    PcsQuotient.quotientChunks m = WhirBridge.quotientChunks m WhirBridge.qSpill 64 := rfl

/-- **The quotient table's layout** (`quotient_layout`) is F2's, at every size. -/
theorem layoutTr_quotientLayout (logRows : ℕ) :
    layoutTr (PcsQuotient.quotientLayout logRows) = WhirBridge.quotientLayout logRows := by
  rw [PcsQuotient.quotientLayout, layoutTr_hidden, quotientChunks_eq]
  rfl

/-- `Layout::new` of one chunk `0` (the wiring table's), transcribed twice. -/
theorem layoutTr_ofChunks_zero (vars logChunk logN len : ℕ) :
    layoutTr (PcsQuotient.Layout.ofChunks vars logChunk logN [(0, len)]) =
      WhirBridge.Layout.new vars logChunk logN [(0, len)] := by
  simp [PcsQuotient.Layout.ofChunks, WhirBridge.Layout.new, WhirBridge.Layout.newBlocks, layoutTr,
    List.map_map, Function.comp_def, laneTr, PcsQuotient.laneFold, WhirBridge.laneFold]

/-- **The wiring table's layout** (`wiring_layout`) is F2's, at every size. -/
theorem layoutTr_wiringLayout (logRows : ℕ) :
    layoutTr (PcsQuotient.wiringLayout logRows) = WhirBridge.wiringLayout logRows := by
  rw [PcsQuotient.wiringLayout, layoutTr_ofChunks_zero]
  rfl

/-! ## The weights -/

theorem testBit_iff_shift (i k : ℕ) : i.testBit k = decide ((i >>> k) % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]

/-- `eq(point, bits of index)`, transcribed twice. -/
theorem eqBits_eq (p : List E) (i : ℕ) : PcsQuotient.eqBits p i = WhirBridge.eqBits p i := by
  unfold PcsQuotient.eqBits WhirBridge.eqBits
  apply List.foldl_ext
  intro w pk _
  obtain ⟨q, k⟩ := pk
  simp only [testBit_iff_shift, decide_eq_true_eq]

theorem laneScales_eq (L : PcsQuotient.Layout) (p : List E) :
    (layoutTr L).laneScales p = (L.scales p).1 := by
  simp only [WhirBridge.Layout.laneScales, PcsQuotient.Layout.scales, layoutTr_lanes,
    layoutTr_logLane, List.map_map]
  congr 1
  funext l
  cases l <;> simp [laneTr, eqBits_eq]

theorem pieceScales_eq (L : PcsQuotient.Layout) (p : List E) :
    (layoutTr L).pieceScales p = (L.scales p).2 := by
  simp only [WhirBridge.Layout.pieceScales, PcsQuotient.Layout.scales, layoutTr_logPiece,
    layoutTr_pieces]
  cases L.logPiece <;> simp [eqBits_eq]

/-- F2's `on_blocks` on the translated lanes, as the statement writes it. -/
theorem onBlocks_eq (ls : List PcsQuotient.Lane) (sc high : List E) :
    WhirBridge.onBlocks (ls.map laneTr) sc (WhirBridge.laneEqs (ls.map laneTr).length high) =
      ls.zipIdx.foldl (fun sum ll => match ll.1 with
        | PcsQuotient.Lane.block _ => sum + sc.getD ll.2 0 * PcsQuotient.eqBits high ll.2
        | _ => sum) 0 := by
  unfold WhirBridge.onBlocks
  rw [List.zipIdx_map, List.foldl_map]
  apply List.foldl_ext
  intro sum ll hll
  obtain ⟨a, i⟩ := ll
  have hi := (List.mem_zipIdx' hll).1
  cases a <;> simp [WhirBridge.onStep, laneTr, WhirBridge.laneEqs, List.getD_eq_getElem?_getD, hi,
    eqBits_eq]

theorem findIdx_laneTr (ls : List PcsQuotient.Lane) :
    (ls.map laneTr).findIdx (· == WhirBridge.Lane.overflow) =
      ls.findIdx (fun l => decide (l = PcsQuotient.Lane.overflow)) := by
  rw [List.findIdx_map]
  congr 1
  funext l
  cases l <;> simp [laneTr]

/-- The overflow lane, found twice: where F2 finds one, the statement finds the same. -/
theorem overflowLane_eq (ls : List PcsQuotient.Lane)
    (h : (ls.map laneTr).findIdx (· == WhirBridge.Lane.overflow) < ls.length) :
    (ls.findIdx? (· = PcsQuotient.Lane.overflow)).getD 0 =
      (ls.map laneTr).findIdx (· == WhirBridge.Lane.overflow) := by
  rw [findIdx_laneTr] at h ⊢
  rw [(List.findIdx?_eq_some_iff_findIdx_eq.mpr ⟨h, rfl⟩)]
  rfl

/-- **A claim's weight on the stack is F2's** (`stackWeight` = `Layout.claimWeight`), for a public
layout, or a hidden one with an overflow lane. -/
theorem stackWeight_eq (L : PcsQuotient.Layout)
    (hov : L.logPiece.isSome → (layoutTr L).overflow < L.lanes.length) (c : PcsQuotient.Claim)
    (x : List E) : PcsQuotient.stackWeight L c x = (layoutTr L).claimWeight (claimTr c) x := by
  simp only [PcsQuotient.stackWeight, WhirBridge.Layout.claimWeight, WhirBridge.Layout.term,
    WhirBridge.Layout.part, laneScales_eq, pieceScales_eq, layoutTr_logPiece, layoutTr_logLane,
    layoutTr_lanes, claimTr_point, onBlocks_eq, WhirBridge.eqZ_eq_eqEval, WhirBridge.onePlusProd]
  rcases h : L.logPiece with _ | s
  · rfl
  · have ho := hov (by simp [h])
    have hov' : L.overflowLane = (layoutTr L).overflow := overflowLane_eq L.lanes ho
    have hget : (WhirBridge.laneEqs (L.lanes.map laneTr).length (List.drop L.logLane x)).getD
        (layoutTr L).overflow 0 = PcsQuotient.eqBits (List.drop L.logLane x) L.overflowLane := by
      rw [hov']
      simp [WhirBridge.laneEqs, List.getD_eq_getElem?_getD, ho, eqBits_eq]
    simp only [hget, ← eqBits_eq]
    rfl

theorem kOfLane_one : K.ofLane 1 = 1 := rfl

theorem kOfLane_zero : K.ofLane 0 = 0 := rfl

theorem gadgetBeta_eq (i : ℕ) : PcsQuotient.gadgetBeta i = WhirBridge.gadgetBeta i := by
  unfold PcsQuotient.gadgetBeta WhirBridge.gadgetBeta
  split_ifs <;> simp_all [kOfLane_one, kOfLane_zero]

/-- **The gadget's weight on the stack is F2's**, for a hidden layout of at least `33` lanes (the
gadget's lanes `0, 1, 30, 31, 32` all lanes of the stack). -/
theorem gadgetWeight_eq (L : PcsQuotient.Layout) {s : ℕ} (hs : L.logPiece = some s)
    (hn : 33 ≤ L.lanes.length) (x : List E) :
    PcsQuotient.gadgetWeight L x = (layoutTr L).gadgetWeight x := by
  have h0 : 0 < L.lanes.length := by omega
  have h1 : 1 < L.lanes.length := by omega
  have h30 : 30 < L.lanes.length := by omega
  have h31 : 31 < L.lanes.length := by omega
  have h32 : 32 < L.lanes.length := by omega
  simp [PcsQuotient.gadgetWeight, WhirBridge.Layout.gadgetWeight, WhirBridge.gadgetSum,
    WhirBridge.Layout.gadgetParts, hs, List.range_succ, WhirBridge.laneEqs,
    List.getD_eq_getElem?_getD, h0, h1, h30, h31, h32, eqBits_eq, PcsQuotient.gadgetLanes,
    WhirBridge.gadgetLanes, WhirBridge.overflowLane, PcsQuotient.overflowLaneIndex,
    PcsQuotient.Layout.gadgetEntry, WhirBridge.gadgetEntry, PcsQuotient.gadgetSize,
    WhirBridge.gadget, gadgetBeta_eq]

/-- **What the weight bridge needs of a layout**: public, or hidden with an overflow lane and the
gadget's lanes among its at least `33` lanes. -/
def LayoutOK (L : PcsQuotient.Layout) : Prop :=
  L.logPiece = none ∨
    ((layoutTr L).overflow < L.lanes.length ∧ 33 ≤ L.lanes.length)

/-- **The opening's stack claims are F2's** (`stackClaims` = `Layout.stacking.claims`): the claims'
weights and values, then a hidden layout's gadget, of value zero. -/
theorem stackClaims_eq (L : PcsQuotient.Layout) (hL : LayoutOK L) (claims : List PcsQuotient.Claim) :
    PcsQuotient.stackClaims L claims = (layoutTr L).stacking.claims (claims.map claimTr) := by
  have hov : L.logPiece.isSome → (layoutTr L).overflow < L.lanes.length := by
    intro h
    rcases hL with hL | hL
    · simp [hL] at h
    · exact hL.1
  simp only [PcsQuotient.stackClaims, WhirBridge.Stacking.claims, WhirBridge.Layout.stacking,
    List.map_map]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, claimTr_value]
    exact Prod.ext (funext fun x => stackWeight_eq L hov c x) rfl
  · rcases h : L.logPiece with _ | s
    · simp [WhirBridge.Layout.extra, h]
    · have hn : 33 ≤ L.lanes.length := by
        rcases hL with hL | hL
        · simp [hL] at h
        · exact hL.2
      simp only [WhirBridge.Layout.extra, layoutTr_logPiece, h, Option.isSome_some, ↓reduceIte]
      exact congrArg (fun f => [(f, (0 : E))]) (funext fun x => gadgetWeight_eq L h hn x)

theorem layoutOK_of (L : PcsQuotient.Layout) {W : WhirBridge.Layout} (hW : layoutTr L = W)
    (h : W.logPiece = none ∨ (W.overflow < W.lanes.length ∧ 33 ≤ W.lanes.length)) : LayoutOK L := by
  subst hW
  simpa [LayoutOK] using h

/-- The three layouts meet `LayoutOK` at every supported size (F2's `layouts_shape`). -/
theorem layoutOK_layouts (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows) :
    LayoutOK (PcsQuotient.witnessLayout r) ∧ LayoutOK (PcsQuotient.wiringLayout r) ∧
      LayoutOK (PcsQuotient.quotientLayout r) := by
  obtain ⟨hw, -, hq, hwo, hqo, -⟩ := WhirBridge.layouts_shape r h1 h2
  refine ⟨layoutOK_of _ (layoutTr_witnessLayout r) (Or.inr ⟨by omega, by omega⟩),
    layoutOK_of _ (layoutTr_wiringLayout r) (Or.inl rfl),
    layoutOK_of _ (layoutTr_quotientLayout r) (Or.inr ⟨by omega, by omega⟩)⟩

/-! ## The seed's bytes -/

/-- The layout's encoding (`encode_layout`), transcribed twice. -/
theorem encoding_eq (L : PcsQuotient.Layout) :
    L.encoding = WhirBridge.encodeLayout (layoutTr L) := by
  have hu : PcsQuotient.u64Bytes = WhirBridge.u64 := rfl
  simp only [PcsQuotient.Layout.encoding, WhirBridge.encodeLayout, layoutTr_vars, layoutTr_logN,
    layoutTr_lanes, layoutTr_logPiece, layoutTr_pieces, List.length_map, List.flatMap_map, hu]
  conv_lhs =>
    pattern List.flatMap _ L.lanes
    rw [List.flatMap_congr (g := fun l => WhirBridge.u64 (laneTr l).code.1 ++
      WhirBridge.u64 (laneTr l).code.2) (fun l _ => by cases l <;> rfl)]
  rcases h : L.logPiece with _ | s
  · rfl
  · simp [List.range_succ, PcsQuotient.gadgetLanes, WhirBridge.gadgetLanes,
      PcsQuotient.Layout.gadgetEntry, WhirBridge.gadgetEntry, h, PcsQuotient.gadgetSize,
      WhirBridge.gadget, WhirBridge.overflowLane, PcsQuotient.overflowLaneIndex,
      WhirBridge.optBytes, WhirBridge.gadgetBytes]

/-- The claims' bytes in the IV, transcribed twice. -/
theorem claimBytes_eq (claims : List PcsQuotient.Claim) :
    PcsQuotient.claimBytes claims = WhirBridge.claimsBytes (claims.map claimTr) := by
  simp only [PcsQuotient.claimBytes, WhirBridge.claimsBytes, WhirBridge.flat, List.flatMap_map,
    List.flatMap_assoc]
  rfl

/-- `LABEL`, transcribed twice. -/
theorem openingLabel_eq : PcsQuotient.openingLabel = WhirBridge.label := by decide +kernel

/-- The prefix the IV hashes, transcribed twice. -/
theorem openingPrefix_eq (L : PcsQuotient.Layout) :
    PcsQuotient.openingLabel ++ PcsQuotient.u64Bytes PcsQuotient.openingVersion ++
        digestBytes L.id ++ PcsQuotient.u64Bytes L.logN ++ PcsQuotient.u64Bytes PcsQuotient.logInvRate =
      WhirBridge.openingPrefix (layoutTr L) WhirBridge.logInvRate := by
  rw [openingLabel_eq, WhirBridge.openingPrefix, WhirBridge.layoutId, PcsQuotient.Layout.id,
    encoding_eq]
  rfl

/-! ## The opening check -/

section Run

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
  (F : KeccakState → m KeccakState)

/-- Running a sequence is running its first part, then the rest from the state it leaves. -/
theorem runWithHash_bind {α β : Type} (P : Prog α) (f : α → Prog β) : ∀ s : ProgState,
    runWithHash H F (P.bind f) s = runWithHash H F P s >>= fun o => match o with
      | some (a, s') => runWithHash H F (f a) s'
      | none => pure none := by
  induction P with
  | ret a => intro s; simp [Prog.bind, runWithHash]
  | fail => intro s; simp [Prog.bind, runWithHash]
  | read k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split <;> simp [ih]
  | sample k ih =>
    intro s
    simp [Prog.bind, runWithHash, ih]
  | grind b k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext sp; congr 1; funext cs
      split <;> simp [ih]
  | commit h w k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp only [bind_assoc]
      congr 1; funext sp0; congr 1; funext sp1
      split <;> simp [ih]
    · simp
  | query i ps k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext o
      split <;> simp [ih]

end Run

/-- **F2's `opening::verify` with the statement's early rejection**: a proof stream of fewer than
two scalars is rejected before any query (F2's `openingVerifyWithHash` hashes the IV and permutes the
seed first, then rejects: the same verdict, two more queries). -/
def openingVerifyEarly {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) (L : WhirBridge.Layout) (R : ℕ) (root : Digest)
    (claims : List WhirBridge.Claim) (π : Proof) : m Bool :=
  match π.stream with
  | _ :: _ :: _ => WhirBridge.openingVerifyWithHash H F L R root claims π
  | _ => pure false

/-- On a function oracle, the early rejection changes nothing: `openingVerifyEarly` is F2's
`openingVerifyWithHash`. -/
theorem openingVerifyEarly_id (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    (L : WhirBridge.Layout) (R : ℕ) (root : Digest) (claims : List WhirBridge.Claim) (π : Proof) :
    openingVerifyEarly H F L R root claims π =
      WhirBridge.openingVerifyWithHash H F L R root claims π := by
  rcases π with ⟨_ | ⟨x0, _ | ⟨x1, rest⟩⟩, os⟩ <;>
    simp [openingVerifyEarly, WhirBridge.openingVerifyWithHash, WhirBridge.rootOf] <;>
    intros <;> rfl

theorem zeroDigest_eq : PcsQuotient.zeroDigest = WhirBridge.publicDigest := rfl

theorem absorb_pure {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)
    (sp : Sponge) (x : E) (tag : ℕ) (h : sp.pending.length ≠ rateScalars) :
    Compile.absorb F sp x tag = pure { sp with pending := sp.pending ++ [(x, tag)] } := by
  simp [Compile.absorb, h]

theorem absorb_nil {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)
    (st : KeccakState) (x : E) (tag : ℕ) :
    Compile.absorb F ⟨st, []⟩ x tag = pure ⟨st, [(x, tag)]⟩ :=
  absorb_pure F _ x tag (by simp [rateScalars])

theorem absorb_one {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)
    (st : KeccakState) (p : E × ℕ) (x : E) (tag : ℕ) :
    Compile.absorb F ⟨st, [p]⟩ x tag = pure ⟨st, [p, (x, tag)]⟩ :=
  absorb_pure F _ x tag (by simp [rateScalars])

/-- **The statement's opening check is F2's** (`openingWith` = `opening::verify` of F2 with the
early rejection), for every monad and every permutation `F`, Keccak-256 the sponge over `F`: the
layouts, claims, prefix, seed, root and stack claims are F2's (`layoutTr`, `claimTr`,
`openingPrefix_eq`, `stackClaims_eq`), for a layout meeting `LayoutOK` at an admissible size. -/
theorem openingWith_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (L : PcsQuotient.Layout) (hL : LayoutOK L)
    (hw : Whir.Admissible L.logN WhirBridge.logInvRate) (root : Digest)
    (claims : List PcsQuotient.Claim) (proof : Proof) :
    PcsQuotient.openingWith F L root claims proof =
      openingVerifyEarly (keccak256With F) F (layoutTr L) WhirBridge.logInvRate root
        (claims.map claimTr) proof := by
  have hcond : (claims ≠ [] ∧ (claims.all fun c => decide (c.point.length = L.vars)) = true) ↔
      ((claims.map claimTr).isEmpty = false ∧
        ∀ c ∈ claims.map claimTr, c.point.length = (layoutTr L).vars) := by
    simp [claimTr]
  rcases proof with ⟨_ | ⟨x0, _ | ⟨x1, rest⟩⟩, os⟩
  · simp only [PcsQuotient.openingWith, openingVerifyEarly]
    split_ifs <;> rfl
  · simp only [PcsQuotient.openingWith, openingVerifyEarly]
    split_ifs <;> rfl
  simp only [PcsQuotient.openingWith, openingVerifyEarly, WhirBridge.openingVerifyWithHash]
  by_cases hc : claims ≠ [] ∧ (claims.all fun c => decide (c.point.length = L.vars)) = true
  swap
  · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
  rw [if_pos hc, if_pos (hcond.mp hc)]
  simp only [PcsQuotient.openingSpongeWith, openingPrefix_eq, claimBytes_eq, zeroDigest_eq,
    bind_assoc, pure_bind]
  congr 1; funext iv; congr 1; funext seed
  simp only [absorb_nil, absorb_one, pure_bind]
  have hw' : Whir.Admissible (layoutTr L).stacking.logN WhirBridge.logInvRate := hw
  have hrootOf : WhirBridge.rootOf ⟨x0 :: x1 :: rest, os⟩ = digestOfScalars (x0, x1) := rfl
  rw [hrootOf]
  rcases hd : digestOfScalars (x0, x1) with _ | r
  · simp
  · by_cases hr : r = root
    · subst hr
      simp only [↓reduceIte, runProofWithHash, WhirBridge.ourProg_eq, WhirBridge.variantProg_eq hw',
        runWithHash, hd, absorb_nil, absorb_one, pure_bind, WhirBridge.Stacking.check_eq_ite,
        List.nil_append]
      have hv : ∀ c ∈ List.map claimTr claims, c.point.length = (layoutTr L).stacking.vars :=
        (hcond.mp hc).2
      rw [if_pos hv, runWithHash_bind, ← run_eq_withHash, ← stackClaims_eq L hL claims, bind_assoc]
      refine bind_congr fun o => ?_
      rcases o with _ | ⟨a, s'⟩ <;> simp [runWithHash]
    · have hr' : ¬ r.toList = root.toList := fun h => hr (Vector.toList_inj.mp h)
      simp [hr, hr']

/-- **At the three layouts**, every supported size: the statement's opening check is F2's (with the
early rejection). -/
theorem openingWith_layouts {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r)
    (h2 : r ≤ WhirBridge.maxLogRows) (root : Digest) (claims : List PcsQuotient.Claim) (proof : Proof) :
    PcsQuotient.openingWith F (PcsQuotient.witnessLayout r) root claims proof =
        openingVerifyEarly (keccak256With F) F (WhirBridge.witnessLayout r) WhirBridge.logInvRate root
          (claims.map claimTr) proof ∧
      PcsQuotient.openingWith F (PcsQuotient.wiringLayout r) root claims proof =
        openingVerifyEarly (keccak256With F) F (WhirBridge.wiringLayout r) WhirBridge.logInvRate root
          (claims.map claimTr) proof ∧
      PcsQuotient.openingWith F (PcsQuotient.quotientLayout r) root claims proof =
        openingVerifyEarly (keccak256With F) F (WhirBridge.quotientLayout r) WhirBridge.logInvRate
          root (claims.map claimTr) proof := by
  obtain ⟨ow, oσ, oq⟩ := layoutOK_layouts r h1 h2
  obtain ⟨aw, aσ, aq⟩ := WhirBridge.layouts_ok r h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [openingWith_eq F _ ow (by rw [← layoutTr_logN, layoutTr_witnessLayout]; exact aw),
      layoutTr_witnessLayout]
  · rw [openingWith_eq F _ oσ (by rw [← layoutTr_logN, layoutTr_wiringLayout]; exact aσ),
      layoutTr_wiringLayout]
  · rw [openingWith_eq F _ oq (by rw [← layoutTr_logN, layoutTr_quotientLayout]; exact aq),
      layoutTr_quotientLayout]

/-! ## In the two-oracle model -/

/-- **The two calls answered over a permutation `F`**: Keccak-256 the sponge over `F`, Keccak-f[1600]
`F` (mumbai's `keccakCallsOverQueryPermutation` at `F = queryPermutation`). -/
def keccakCallsWith {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) :
    QueryImpl LeanVM.KeccakCalls m
  | .inl x => keccak256With F x
  | .inr s => F s

theorem keccakCallsWith_queryPermutation :
    keccakCallsWith Common.queryPermutation = LeanVM.keccakCallsOverQueryPermutation := by
  funext t
  rcases t with x | s <;> rfl

/-- `opening::verify` as F2's oracle computation, with the statement's early rejection. -/
def ourVerifierEarly (L : WhirBridge.Layout) (R : ℕ)
    (w : (Digest × WhirBridge.Stmt L.stacking) × Proof) : OracleComp LeanVM.KeccakCalls Bool :=
  match w.2.stream with
  | _ :: _ :: _ => WhirBridge.ourVerifier L R w
  | _ => pure false

/-- F2's `opening::verify`, run with any answers to the two calls, is `openingVerifyWithHash` with
those answers. -/
theorem simulateQ_openingVerify {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl LeanVM.KeccakCalls r) (L : WhirBridge.Layout) (R : ℕ) (root : Digest)
    (claims : List WhirBridge.Claim) (π : Proof) :
    simulateQ impl (WhirBridge.openingVerifyWithHash LeanVM.callKeccak256 LeanVM.callKeccakF1600 L R
        root claims π) =
      WhirBridge.openingVerifyWithHash (Compile.Rom.implH impl) (Compile.Rom.implF impl) L R root
        claims π := by
  unfold WhirBridge.openingVerifyWithHash
  by_cases hc : claims.isEmpty = false ∧ ∀ c ∈ claims, c.point.length = L.vars
  · rw [if_pos hc, if_pos hc]
    simp only [simulateQ_bind, Compile.Rom.simulateQ_queryH, Compile.Rom.simulateQ_queryF]
    refine bind_congr fun iv => bind_congr fun seed => ?_
    by_cases hr : WhirBridge.rootOf π = some root
    · rw [if_pos hr, if_pos hr]
      exact Compile.Rom.simulateQ_runProof impl _ _ _
    · rw [if_neg hr, if_neg hr]
      simp
  · rw [if_neg hc, if_neg hc]
    simp

/-- **The statement's opening check is F2's oracle computation** `ourVerifier` (with the early
rejection) answered over `F`: for a claim list on the layout, wide as F2's `Stmt` requires. -/
theorem openingWith_eq_ourVerifier {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (L : PcsQuotient.Layout) (hL : LayoutOK L)
    (hw : Whir.Admissible L.logN WhirBridge.logInvRate) (root : Digest)
    (x : WhirBridge.Stmt (layoutTr L).stacking) (claims : List PcsQuotient.Claim)
    (hx : x.claims = claims.map claimTr) (proof : Proof) :
    PcsQuotient.openingWith F L root claims proof =
      simulateQ (keccakCallsWith F) (ourVerifierEarly (layoutTr L) WhirBridge.logInvRate
        ((root, x), proof)) := by
  rw [openingWith_eq F L hL hw, ← hx]
  rcases proof with ⟨_ | ⟨x0, _ | ⟨x1, rest⟩⟩, os⟩
  · simp [openingVerifyEarly, ourVerifierEarly]
  · simp [openingVerifyEarly, ourVerifierEarly]
  · simp only [openingVerifyEarly, ourVerifierEarly]
    rw [WhirBridge.ourVerifier, simulateQ_openingVerify]
    rfl

/-! ## The table read back from a stack -/

theorem findIdx?_nat_eq (l : List ℕ) (p : ℕ) :
    l.findIdx? (fun x => decide (x = p)) = l.findIdx? (· == p) := by
  congr 1

theorem findIdx?_block_eq (ls : List PcsQuotient.Lane) (b : ℕ) :
    ls.findIdx? (fun x => decide (x = PcsQuotient.Lane.block b)) =
      (ls.map laneTr).findIdx? (· == WhirBridge.Lane.block b) := by
  rw [List.findIdx?_map]
  congr 1
  funext x
  cases x with
  | block b' =>
    by_cases h : b' = b
    · subst h; simp [laneTr]
    · have h' : (WhirBridge.Lane.block b' == WhirBridge.Lane.block b) = false := by
        simpa using h
      simp [laneTr, h, h']
  | overflow => rfl
  | random => rfl

/-- **The statement's read-back of a hidden table is F2's** (`Layout.readEntry` = `Table::read` =
F2's `Layout.table`), the stack given by its words, for a hidden layout with an overflow lane (the
witness and quotient layouts, `layoutOK_layouts`). -/
theorem readEntry_eq (L : PcsQuotient.Layout) {s : ℕ} (hs : L.logPiece = some s)
    (hov : (layoutTr L).overflow < L.lanes.length) (q : Column L.logN) (i : ℕ) :
    L.readEntry (fun j => q.values.getD j 0) i = (layoutTr L).table q i := by
  have hov' : L.overflowLane = (layoutTr L).overflow := overflowLane_eq L.lanes hov
  simp only [PcsQuotient.Layout.readEntry, WhirBridge.Layout.table, WhirBridge.Layout.readHidden,
    layoutTr_logPiece, hs, layoutTr_pieces, layoutTr_lanes, layoutTr_logLane, Nat.shiftRight_eq_div_pow,
    findIdx?_nat_eq, findIdx?_block_eq, WhirBridge.stackAt, Nat.and_two_pow_sub_one_eq_mod, hov']
  rcases hk : L.pieces.findIdx? (· == i / 2 ^ s) with _ | k
  · rcases hl : (L.lanes.map laneTr).findIdx?
        (· == WhirBridge.Lane.block (i / 2 ^ s / 2 ^ (L.logLane - s))) with _ | l
    · rfl
    · simp only
      congr 1
      ring
  · simp only
    congr 1
    ring

/-! ## The layout's identifier: a constant, bytes-identical for the deployed Keccak -/

/-- The opening's sponge as the statement wrote it before `Layout.id` (`formal/Statement` at
`78ba276`): the layout's identifier hashed over `F`. -/
def openingSpongeOracleId {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)
    (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) : m Sponge := do
  let layoutId ← keccak256With F L.encoding
  let pre := PcsQuotient.openingLabel ++ PcsQuotient.u64Bytes PcsQuotient.openingVersion ++
    digestBytes layoutId ++ PcsQuotient.u64Bytes L.logN ++ PcsQuotient.u64Bytes PcsQuotient.logInvRate
  let iv ← keccak256With F (pre ++ PcsQuotient.claimBytes claims)
  return ⟨← F (seedInput iv PcsQuotient.zeroDigest), []⟩

/-- **The change to a constant identifier is bytes-identical for the deployed Keccak-f[1600]**: over
`keccakF1600` the two sponges are the same, so the deployed verifier, prover and the differential
test are unchanged. -/
theorem openingSponge_deployed (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) :
    openingSpongeOracleId (m := Id) (fun s => pure (keccakF1600 s)) L claims =
      PcsQuotient.openingSpongeWith (m := Id) (fun s => pure (keccakF1600 s)) L claims := rfl

end Bridge

/-- info: 'Bridge.layoutTr_witnessLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.layoutTr_witnessLayout

/-- info: 'Bridge.layoutTr_wiringLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.layoutTr_wiringLayout

/-- info: 'Bridge.layoutTr_quotientLayout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.layoutTr_quotientLayout

/-- info: 'Bridge.eqBits_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.eqBits_eq

/-- info: 'Bridge.stackWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.stackWeight_eq

/-- info: 'Bridge.gadgetWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.gadgetWeight_eq

/-- info: 'Bridge.stackClaims_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.stackClaims_eq

/-- info: 'Bridge.layoutOK_layouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.layoutOK_layouts

/-- info: 'Bridge.encoding_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.encoding_eq

/-- info: 'Bridge.claimBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.claimBytes_eq

/-- info: 'Bridge.openingLabel_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Bridge.openingLabel_eq

/-- info: 'Bridge.openingPrefix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.openingPrefix_eq

/-- info: 'Bridge.runWithHash_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.runWithHash_bind

/-- info: 'Bridge.openingVerifyEarly_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.openingVerifyEarly_id

/-- info: 'Bridge.openingWith_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.openingWith_eq

/-- info: 'Bridge.openingWith_layouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.openingWith_layouts

/-- info: 'Bridge.simulateQ_openingVerify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.simulateQ_openingVerify

/-- info: 'Bridge.openingWith_eq_ourVerifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.openingWith_eq_ourVerifier

/-- info: 'Bridge.readEntry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.readEntry_eq

/-- info: 'Bridge.openingSponge_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.openingSponge_deployed
