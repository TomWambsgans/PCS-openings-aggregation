-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The transcript is
-- `crates/leanvm_flock_gas/src/transcript.rs`'s (`KeccakChannel`), as `formal/UniStatement`
-- transcribes it (`Transcript.lean`); the framework is `formal/Compose/Compose/ListChainU.lean`.
import UniSound.Fs
import Compose.ListChainKRpmS

/-!
# The univariate transcript as a chain over an encoding

`Compose.ChainSpecU` for `UniStatement`'s channel (`KeccakChannel`): **`uniSpec rounds`**.

* **The statement** (`FSt`): the transcript's IV (the contract's, `contractIvWith`), the public
  input, the row counts' 24 bytes; the PIOP's statement (`USt`) is the input and the counts they
  announce (`ustOf`, `rowsOf`).
* **The label** (`uniLabel`): the seed's input `name ‖ iv ‖ input` (80 bytes; `seedWith`); every
  label starts with the 16-byte `name` (the tag: a fresh answer starting with it is a bad event,
  `2^-128`).
* **The statement's bytes before round `0`'s message** (`pre`): the row counts' 24 bytes, absorbed
  with `C1`'s root (`readCounts`, then `nextRoot`).
* **A message's encoding** (`uniEnc`): the root as the stream carries it (`revRoot`: the digest's
  two 16-byte halves, each reversed: `next_root`), then each scalar's 24 bytes (`scalar24`: limbs
  `2, 1, 0`, big-endian: `next_scalar`).
* **What an input refers to** (`UniRf`): `Compose.Refers`, or a root after a state (`C2`'s, bytes
  `32 … 64`) or after a state and the row counts (`C1`'s, bytes `56 … 88`): at most five digests.

The PIOP's round-by-round soundness on `USt` is lifted to `FSt` (`liftPiop`); the proof the chain
reads is `UPf` (the input, the proof, the IV, the setup's roots), its messages the stream's
(`msgsAt`, from byte `24`), its tail the five scalars after them (`uTail`).
-/

namespace UniSound

open Compose QuotientRpm LeanVM.Parameters LeanVM.Protocol.KeccakHash UniStatement
open scoped ENNReal

/-! ## Bytes -/

/-- A field element as its three limbs, low first (`Soundness.eLimbs`, `F192`'s `(c0, c1, c2)`). -/
def uLimbs : E ≃ Limbs where
  toFun x := ((x.limb 0).lane, (x.limb 1).lane, (x.limb 2).lane)
  invFun l := E.ofLimbs (K.ofLane l.1) (K.ofLane l.2.1) (K.ofLane l.2.2)
  left_inv x := by
    simp only
    have h : ∀ a : K, K.ofLane a.lane = a := fun _ => rfl
    rw [h, h, h, ofLimbs_limb]
  right_inv l := by
    obtain ⟨a, b, c⟩ := l
    have h : ∀ w : UInt64, (K.ofLane w).lane = w := fun _ => rfl
    simp only [limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, h]

/-- **A scalar as the stream carries it** (`next_scalar`): 24 bytes, limbs `2, 1, 0`, each
big-endian. -/
def scalar24 (x : E) : List UInt8 :=
  QuotientRpm.be64 (uLimbs x).2.2 ++ QuotientRpm.be64 (uLimbs x).2.1 ++ QuotientRpm.be64 (uLimbs x).1

@[simp] theorem length_scalar24 (x : E) : (scalar24 x).length = 24 := by
  simp [scalar24]

theorem scalarWord_scalar24 (x : E) : scalarWord (uLimbs x) = List.replicate 8 0 ++ scalar24 x := by
  simp [scalarWord, scalar24, List.append_assoc]

theorem scalar24_injective : Function.Injective scalar24 := fun a b h => by
  apply uLimbs.injective
  apply scalarWord_injective
  rw [scalarWord_scalar24, scalarWord_scalar24, h]

/-- The scalars as the stream carries them. -/
def scalars24 (l : List E) : List UInt8 := l.flatMap scalar24

@[simp] theorem length_scalars24 (l : List E) : (scalars24 l).length = 24 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [scalars24, List.flatMap_cons, List.length_append, length_scalar24,
      List.length_cons] at ih ⊢
    rw [ih]
    ring

theorem scalars24_inj : ∀ {l l' : List E}, l.length = l'.length → scalars24 l = scalars24 l' →
    l = l'
  | [], [], _, _ => rfl
  | a :: l, a' :: l', hl, h => by
    simp only [scalars24, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    rw [scalar24_injective h1, scalars24_inj (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **A root as the stream carries it** (`next_root`): its digest's two 16-byte halves, each
reversed (a half's limbs `1, 0`, big-endian). -/
def revRoot (r : Bytes32) : List UInt8 := (r.toList.take 16).reverse ++ (r.toList.drop 16).reverse

@[simp] theorem length_revRoot (r : Bytes32) : (revRoot r).length = 32 := by
  simp [revRoot]

theorem revRoot_injective : Function.Injective revRoot := fun a b h => by
  unfold revRoot at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  apply Vector.toList_inj.mp
  rw [← List.take_append_drop 16 a.toList, ← List.take_append_drop 16 b.toList,
    List.reverse_inj.mp h1, List.reverse_inj.mp h2]

/-- **A round's message as the chain hashes it**: the root's bytes, then the scalars'. -/
def uniEnc (m : RMsg E) : List UInt8 :=
  (match m.1 with
    | some r => revRoot r
    | none => []) ++ scalars24 m.2

theorem uniEnc_inj {sp : RoundSpec} {m m' : RMsg E} (h : m.Fits sp) (h' : m'.Fits sp)
    (he : uniEnc m = uniEnc m') : m = m' := by
  obtain ⟨r, l⟩ := m
  obtain ⟨r', l'⟩ := m'
  obtain ⟨hr, hl⟩ := h
  obtain ⟨hr', hl'⟩ := h'
  simp only at hr hl hr' hl'
  have hll : l.length = l'.length := hl.trans hl'.symm
  cases r with
  | none =>
    cases r' with
    | none =>
      simp only [uniEnc, List.nil_append] at he
      rw [scalars24_inj hll he]
    | some _ => exact absurd (hr.trans hr'.symm) (by simp)
  | some a =>
    cases r' with
    | none => exact absurd (hr.trans hr'.symm) (by simp)
    | some a' =>
      simp only [uniEnc] at he
      obtain ⟨h1, h2⟩ := List.append_inj he (by simp)
      rw [revRoot_injective h1, scalars24_inj hll h2]

/-! ## What an input refers to -/

/-- **An input refers to a digest**: `Refers` (a Merkle node's children, a chain state), or the
digest is the root the input absorbs after a state (bytes `32 … 64`, `C2`'s) or after a state
and the row counts (bytes `56 … 88`, `C1`'s). -/
def UniRf (y : List UInt8) (d : Bytes32) : Prop :=
  Refers y d ∨ revRoot d = (y.drop 32).take 32 ∨ revRoot d = (y.drop 56).take 32

open Classical in
/-- The digests an input refers to. -/
noncomputable def uniRefs (y : List UInt8) : List Bytes32 :=
  (Finset.univ.filter fun d : Bytes32 => UniRf y d).toList

set_option maxRecDepth 100000 in
theorem uniRf_refs (y : List UInt8) (d : Bytes32) (h : UniRf y d) : d ∈ uniRefs y := by
  classical
  unfold uniRefs
  rw [Finset.mem_toList, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, h⟩

open Classical in
-- The linter runs out of recursion depth on this proof.
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- An input refers to at most five digests. -/
theorem length_uniRefs (y : List UInt8) : (uniRefs y).length ≤ 5 := by
  unfold uniRefs
  rw [Finset.length_toList]
  have h1 : ∀ z : List UInt8,
      (Finset.univ.filter fun u : Bytes32 => revRoot u = z).card ≤ 1 :=
    fun z => Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact revRoot_injective (ha.2.trans hb.2.symm)
  have hsub : (Finset.univ.filter fun u : Bytes32 => UniRf y u) ⊆
      ((Finset.univ.filter fun u : Bytes32 => Refers y u) ∪
        (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 32).take 32)) ∪
        (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 56).take 32) := by
    intro u hu'
    simp only [Finset.mem_filter] at hu'
    obtain ⟨-, h⟩ := hu'
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases h with h | h | h
    · exact Or.inl (Or.inl ⟨Finset.mem_univ _, h⟩)
    · exact Or.inl (Or.inr ⟨Finset.mem_univ _, h⟩)
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h2 := Finset.card_union_le (Finset.univ.filter fun u : Bytes32 => Refers y u)
    (Finset.univ.filter fun u : Bytes32 => revRoot u = (y.drop 32).take 32)
  have h3 := card_refers_le y
  have h4 := h1 ((y.drop 32).take 32)
  have h5 := h1 ((y.drop 56).take 32)
  omega

/-! ## The statement -/

/-- **The chain's statement**: the transcript's IV, the public input, the row counts' 24 bytes. -/
abbrev FSt := Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 24

/-- The row counts 24 bytes announce (`rowsOf`). -/
def rowsOfBytes (rb : Vector UInt8 24) : List ℕ := rowsOf rb.toArray

/-- **The PIOP's statement**: the input and the row counts. -/
def ustOf (s : FSt) : USt := (s.2.1, rowsOfBytes s.2.2)

/-- **The seed's input** (`keccak_seed`): `name ‖ iv ‖ input`. -/
def uniLabel (s : FSt) : List UInt8 := name ++ s.1.toList ++ s.2.1.toList

theorem name_length : name.length = 16 := by decide +kernel

theorem uniLabel_take (s : FSt) : (uniLabel s).take name.length = name := by
  unfold uniLabel
  rw [List.append_assoc]
  exact List.take_left' rfl

theorem uniLabel_inj {s s' : FSt} (h : uniLabel s = uniLabel s') : s.1 = s'.1 ∧ s.2.1 = s'.2.1 := by
  unfold uniLabel at h
  rw [List.append_assoc, List.append_assoc] at h
  have h1 := List.append_cancel_left h
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  exact ⟨Vector.toList_inj.mp h2, Vector.toList_inj.mp h3⟩

theorem uniStmt_inj (s s' : FSt) (hl : uniLabel s = uniLabel s')
    (hp : s.2.2.toList = s'.2.2.toList) : s = s' := by
  obtain ⟨h1, h2⟩ := uniLabel_inj hl
  obtain ⟨a, b, c⟩ := s
  obtain ⟨a', b', c'⟩ := s'
  simp only at h1 h2 hp
  rw [h1, h2, Vector.toList_inj.mp hp]

/-! ## The chain's specification -/

/-- The `ChainSpec` of the rounds (its label the seed's input and the row counts' bytes: only its
limbs and rounds are read). -/
def uniK (rounds : List RoundSpec) : ChainSpec E FSt where
  lim := uLimbs
  label s := uniLabel s ++ s.2.2.toList
  label_injective s s' h := by
    have hl : (uniLabel s).length = (uniLabel s').length := by simp [uniLabel]
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact uniStmt_inj s s' h1 h2
  label_len s := by
    have : (uniLabel s ++ s.2.2.toList).length = 104 := by
      simp [uniLabel, name_length]
    rw [this]
    decide
  rounds := rounds

/-- **The univariate transcript as a chain over an encoding** (`KeccakChannel` on the rounds). -/
noncomputable def uniSpec (rounds : List RoundSpec) : ChainSpecU E FSt where
  K := uniK rounds
  label := uniLabel
  tag := name
  tag_le := by rw [name_length]; decide
  label_tag := uniLabel_take
  pre s := s.2.2.toList
  pre_len s s' := by simp
  stmt_inj := uniStmt_inj
  enc := uniEnc
  enc_inj := uniEnc_inj
  Rf := UniRf
  nRf := 5
  refs := uniRefs
  rf_refs := uniRf_refs
  length_refs := length_uniRefs
  refers_rf y d h := Or.inl h
  rf_enc st r l := by
    refine Or.inr (Or.inl ?_)
    simp only [stepIn, uniEnc]
    rw [List.drop_left' (by simp), List.take_left' (by simp)]
  rf_pre s st r l := by
    refine Or.inr (Or.inr ?_)
    simp only [stepIn, uniEnc]
    rw [show (st.toList ++ (s.2.2.toList ++ (revRoot r ++ scalars24 l))).drop 56 =
        revRoot r ++ scalars24 l by
      rw [show (56 : ℕ) = 32 + 24 from rfl, ← List.drop_drop, List.drop_left' (by simp),
        List.drop_left' (by simp)]]
    rw [List.take_left' (by simp)]

@[simp] theorem uniSpec_rounds (rounds : List RoundSpec) : (uniSpec rounds).K.rounds = rounds :=
  rfl

theorem uniSpec_tagBound (rounds : List RoundSpec) :
    (uniSpec rounds).tagBound = ((256 ^ 16 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold ChainSpecU.tagBound
  show ((256 ^ (32 - name.length) : ℕ) : ℝ≥0∞) / 2 ^ 256 = _
  rw [name_length]

/-! ## The protocol on the chain's statement -/

/-- **The PIOP's round-by-round soundness, on the chain's statement** (the IV and the counts'
bytes read as the PIOP's statement, `ustOf`). -/
def liftPiop (K : ChainSpec E FSt) {rounds : List RoundSpec} (R : RbrPiop rounds USt Stk)
    (hK : K.rounds = rounds) : Piop K Stk where
  pre s := R.pre (ustOf s)
  post s := R.post (ustOf s)
  pre_post s := R.pre_post (ustOf s)
  err := R.err
  sound j s p m hj hp := by
    have h := R.sound j (ustOf s) p m (hK ▸ hj) hp
    simpa only [ChainSpec.spec, hK] using h

/-! ## The proof the chain reads -/

/-- **The proof as the verifier reads it**: the public input, the univariate proof, the transcript's
IV and the setup's roots. -/
structure UPf where
  input : Vector UInt8 32
  proof : UniProof
  iv : Vector UInt8 32
  roots : SetupRoots

/-- The stream's scalar at byte `o` (`next_scalar`). -/
def scalarAt (b : Array UInt8) (o : ℕ) : E :=
  eNew (beWordAt b (o + 16)) (beWordAt b (o + 8)) (beWordAt b o)

/-- The stream's root at byte `o`, its two halves (`next_root`). -/
def halvesAt (b : Array UInt8) (o : ℕ) : E × E :=
  (eNew (beWordAt b (o + 8)) (beWordAt b o) 0, eNew (beWordAt b (o + 24)) (beWordAt b (o + 16)) 0)

/-- A round's bytes: `32` for a root, `24` a scalar. -/
def roundBytes (r : RoundSpec) : ℕ := (if r.root then 32 else 0) + 24 * r.nv

/-- The rounds' bytes. -/
def roundsBytes : List RoundSpec → ℕ
  | [] => 0
  | r :: rs => roundBytes r + roundsBytes rs

/-- **The rounds' messages the stream carries**, from byte `o` on: each round's root (if it has
one) and its scalars. -/
def msgsAt (b : Array UInt8) : ℕ → List RoundSpec → List UMsg
  | _, [] => []
  | o, r :: rs => ((if r.root then some (halvesAt b o) else none),
      (List.range r.nv).map fun k => scalarAt b (o + (if r.root then 32 else 0) + 24 * k)) ::
      msgsAt b (o + roundBytes r) rs

/-- A channel message as the chain's: the root's digest (`rootOf`) as 32 bytes. -/
def toRMsg (m : UMsg) : RMsg E := (m.1.map fun h => toB (rootOf h), m.2)

/-- The row counts' 24 bytes (missing bytes `0`). -/
def rowBytes (b : Array UInt8) : Vector UInt8 24 := Vector.ofFn fun i => b.getD i.val 0

/-- **What the chain reads of a proof**: the statement (the IV, the input, the counts' bytes) and
the rounds' messages, from byte `24`. -/
def uView (rounds : List RoundSpec) (π : UPf) : FSt × List (RMsg E) :=
  ((π.iv, π.input, rowBytes π.proof.stream), (msgsAt π.proof.stream 24 rounds).map toRMsg)

/-- **The transcript the chain program reads**: the messages and the challenges. -/
def uDone (rounds : List RoundSpec) (π : UPf) (ch : List (List E)) : Done :=
  (msgsAt π.proof.stream 24 rounds).zip ch

/-- **The tail**: the five scalars after the rounds. -/
def uTail (rounds : List RoundSpec) (π : UPf) : List E :=
  (List.range 5).map fun k => scalarAt π.proof.stream (24 + roundsBytes rounds + 24 * k)

@[simp] theorem length_uTail (rounds : List RoundSpec) (π : UPf) : (uTail rounds π).length = 5 := by
  simp [uTail]

theorem length_msgsAt (b : Array UInt8) : ∀ (o : ℕ) (rs : List RoundSpec),
    (msgsAt b o rs).length = rs.length
  | _, [] => rfl
  | o, r :: rs => by simp [msgsAt, length_msgsAt b _ rs]

/-- The stream's messages fit the rounds. -/
theorem fitsAll_msgsAt (b : Array UInt8) : ∀ (o : ℕ) (rs : List RoundSpec),
    FitsAll rs ((msgsAt b o rs).map toRMsg)
  | _, [] => trivial
  | o, r :: rs => by
    simp only [msgsAt, List.map_cons]
    refine ⟨⟨?_, by simp [toRMsg]⟩, fitsAll_msgsAt b _ rs⟩
    cases r.root <;> simp [toRMsg]

theorem fitsAll_uView (rounds : List RoundSpec) (π : UPf) :
    FitsAll rounds (uView rounds π).2 :=
  fitsAll_msgsAt _ _ _

end UniSound
