-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `formal/UniSound/UniSound/FsChain.lean`,
-- `FsOps.lean`, `FsProof.lean` (the setup), `FsGame.lean` (the IV in the verifier) and `FsCouple.lean` (the bridge facts)
-- to π2's transcript (`formal/RecStatement/RecStatement/Verifier.lean`, `Calls.lean`, `Security.lean`).
import RecCompose.Layers
import RecCompose.Pi2Run
import UniSound.FsGame
import Compose.ListChainUDoom128S

/-!
# π2's Fiat–Shamir layer: the chain, the openings, the setup, the composed verifier

The objects `Compose.knowledgeSoundness_listChainU_closed128S` is applied to for π2's verifier at the real
deployment's circuit (`cc = Data.circuit`: `2^24` positions, rows of `16`, the reads `C1`'s and `C2`'s roots then
`17` elements, `472` bytes):

* **the chain** (`pi2Spec`, `Compose.ChainSpecU`): the statement `FSt2` (π2's IV, the public input, the public
  data's `472` bytes), the label the seed's input `name ‖ iv ‖ input` (`RecStatement.name`, 16 bytes), the public
  data the statement's bytes before round `0`'s message (`W`'s root), the messages as the stream carries them
  (`UniSound.uniEnc`: a root's reversed halves, `24`-byte scalars), `RecPiop.pi2Rounds 4`;
* **the proof the chain reads** (`P2Pf`: the input, the recursive proof, the IV, the setup's four roots) and its view
  (`p2View`: the stream's messages from byte `472`);
* **the six openings** (`p2Ops`), in the contract's order: π1's `C1`, `C2`, `F` (plain layouts of `27`, `27`, `24`
  variables; nothing concluded of them: `p2Stk = none`), π2's `W` (round `0`, plain `2^24`), the setup (`κ`, `κ + σ`,
  `2^25` words, its stack read off the proof's roots: `p2Stk`), `Q` (round `1`, `2^28` words, two claims);
* **the setup** (`p2Setup`): π1's three trees (`UniSound.uSetup`), then π2's tree of the circuit's setup table at π1's
  contract IV of those roots;
* **the composed verifier** (`p2Ver`): π2's IV (the circuit's digest, three Keccak-256 calls, then the IV's), then
  the chain and the six openings; the IV moved into the adversary (`p2IvAdv`);
* **the protocol** (`liftPiop2`): a protocol on `pi2K` (`Pi2FsLayer`'s) on the chain's statement, `stOf`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local instance high] Completeness.instSampleableTypeE_completeness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack RecStatement.layoutWords

/-! ## The circuit's public data -/

/-- The real deployment's circuit (`RecDeployment.Real`: at every IV). -/
abbrev cc : RecStatement.Circuit := Data.circuit

/-- The public data's bytes (`2 · 32 + 17 · 24`). -/
abbrev pLen : ℕ := 472

/-- The stream's bytes: the public data, `W`'s and `Q`'s roots, the `2^4 + 1` values. -/
abbrev sLen : ℕ := 944

/-! ## The chain -/

/-- **π2's chain statement**: π2's IV, the public input, the public data's `472` bytes. -/
abbrev FSt2 : Type := Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 pLen

/-- **The seed's input** (`runWith`): `name ‖ iv ‖ input`. -/
def p2Label (s : FSt2) : List UInt8 := RecStatement.name ++ s.1.toList ++ s.2.1.toList

theorem name_length : RecStatement.name.length = 16 := by decide +kernel

theorem p2Label_length (s : FSt2) : (p2Label s).length = 80 := by
  simp [p2Label, name_length]

theorem p2Label_take (s : FSt2) : (p2Label s).take RecStatement.name.length = RecStatement.name := by
  unfold p2Label
  rw [List.append_assoc]
  exact List.take_left' rfl

theorem p2Label_inj {s s' : FSt2} (h : p2Label s = p2Label s') : s.1 = s'.1 ∧ s.2.1 = s'.2.1 := by
  unfold p2Label at h
  rw [List.append_assoc, List.append_assoc] at h
  have h1 := List.append_cancel_left h
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  exact ⟨Vector.toList_inj.mp h2, Vector.toList_inj.mp h3⟩

theorem p2Stmt_inj (s s' : FSt2) (hl : p2Label s = p2Label s') (hp : s.2.2.toList = s'.2.2.toList) :
    s = s' := by
  obtain ⟨h1, h2⟩ := p2Label_inj hl
  obtain ⟨a, b, c⟩ := s
  obtain ⟨a', b', c'⟩ := s'
  simp only at h1 h2 hp
  rw [h1, h2, Vector.toList_inj.mp hp]

/-- The `ChainSpec` of π2's rounds (its label the seed's input and the public data: only its limbs and rounds are
read). -/
def p2K : ChainSpec E FSt2 where
  lim := UniSound.uLimbs
  label s := p2Label s ++ s.2.2.toList
  label_injective s s' h := by
    have hl : (p2Label s).length = (p2Label s').length := by rw [p2Label_length, p2Label_length]
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact p2Stmt_inj s s' h1 h2
  label_len s := by
    have : (p2Label s ++ s.2.2.toList).length = 552 := by
      simp [p2Label_length, pLen]
    rw [this]
    decide
  rounds := RecPiop.pi2Rounds 4

/-- **An input refers to a digest**: `Compose.Refers`, or the digest is the root the input absorbs after a state
(bytes `32 … 64`, `Q`'s) or after a state and the public data (bytes `504 … 536`, `W`'s). -/
def p2Rf (y : List UInt8) (d : Bytes32) : Prop :=
  Refers y d ∨ UniSound.revRoot d = (y.drop 32).take 32 ∨ UniSound.revRoot d = (y.drop (32 + pLen)).take 32

open Classical in
/-- The digests an input refers to. -/
noncomputable def p2Refs (y : List UInt8) : List Bytes32 :=
  (Finset.univ.filter fun d : Bytes32 => p2Rf y d).toList

set_option maxRecDepth 100000 in
theorem p2Rf_refs (y : List UInt8) (d : Bytes32) (h : p2Rf y d) : d ∈ p2Refs y := by
  classical
  unfold p2Refs
  rw [Finset.mem_toList, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, h⟩

open Classical in
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- An input refers to at most five digests. -/
theorem length_p2Refs (y : List UInt8) : (p2Refs y).length ≤ 5 := by
  unfold p2Refs
  rw [Finset.length_toList]
  have h1 : ∀ z : List UInt8,
      (Finset.univ.filter fun u : Bytes32 => UniSound.revRoot u = z).card ≤ 1 :=
    fun z => Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact UniSound.revRoot_injective (ha.2.trans hb.2.symm)
  have hsub : (Finset.univ.filter fun u : Bytes32 => p2Rf y u) ⊆
      ((Finset.univ.filter fun u : Bytes32 => Refers y u) ∪
        (Finset.univ.filter fun u : Bytes32 => UniSound.revRoot u = (y.drop 32).take 32)) ∪
        (Finset.univ.filter fun u : Bytes32 => UniSound.revRoot u = (y.drop (32 + pLen)).take 32) := by
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
    (Finset.univ.filter fun u : Bytes32 => UniSound.revRoot u = (y.drop 32).take 32)
  have h3 := card_refers_le y
  have h4 := h1 ((y.drop 32).take 32)
  have h5 := h1 ((y.drop (32 + pLen)).take 32)
  omega

/-- **π2's transcript as a chain over an encoding** (`KeccakChannel` on `RecPiop.pi2Rounds 4`, the public data
before `W`'s root). -/
noncomputable def pi2Spec : ChainSpecU E FSt2 where
  K := p2K
  label := p2Label
  tag := RecStatement.name
  tag_le := by rw [name_length]; decide
  label_tag := p2Label_take
  pre s := s.2.2.toList
  pre_len s s' := by simp
  stmt_inj := p2Stmt_inj
  enc := UniSound.uniEnc
  enc_inj := UniSound.uniEnc_inj
  Rf := p2Rf
  nRf := 5
  refs := p2Refs
  rf_refs := p2Rf_refs
  length_refs := length_p2Refs
  refers_rf y d h := Or.inl h
  rf_enc st r l := by
    refine Or.inr (Or.inl ?_)
    simp only [stepIn, UniSound.uniEnc]
    rw [List.drop_left' (by simp), List.take_left' (by simp)]
  rf_pre s st r l := by
    refine Or.inr (Or.inr ?_)
    simp only [stepIn, UniSound.uniEnc]
    rw [show (st.toList ++ (s.2.2.toList ++ (UniSound.revRoot r ++ UniSound.scalars24 l))).drop (32 + pLen) =
        UniSound.revRoot r ++ UniSound.scalars24 l by
      rw [← List.drop_drop, List.drop_left' (by simp), List.drop_left' (by simp)]]
    rw [List.take_left' (by simp)]

@[simp] theorem pi2Spec_rounds : pi2Spec.K.rounds = RecPiop.pi2Rounds 4 := rfl

/-! ## The protocol on the chain's statement -/

/-- **π2's PIOP statement of a chain statement**: the public input, and the public scalars (`pi2Pubs`: the input's
four words, then the reads' scalars of the public data). -/
def stOf (s : FSt2) : Pi2St := (s.2.1, pi2Pubs (Spec.of cc) s.2.1.toList s.2.2.toArray)

/-- **A protocol on `pi2K` on the chain's statement** (`stOf`; the same rounds). -/
def liftPiop2 (R : Compose.Piop pi2K Stk) : Compose.Piop pi2Spec.K Stk where
  pre s := R.pre (stOf s)
  post s := R.post (stOf s)
  pre_post s := R.pre_post (stOf s)
  err := R.err
  sound j s p m hj hp := R.sound j (stOf s) p m hj hp

/-! ## The proof the chain reads -/

/-- **The composed setup's output**: π1's three roots (`F`, `A0`, `B0`) and π2's setup root. -/
abbrev SOut : Type := (Bytes32 × Bytes32 × Bytes32) × Bytes32

/-- The setup's roots of the composed setup's output. -/
def rootsOfOut (s : SOut) : RecSetupRoots := ⟨UniSound.rootsOfS s.1, ofB s.2⟩

/-- **The proof as π2's composed verifier reads it**: the public input, the recursive proof, π2's IV, the setup's
roots. -/
structure P2Pf where
  input : Vector UInt8 32
  proof : RecProof
  iv : Vector UInt8 32
  roots : SOut

/-- The proof with the setup's roots (`fix`). -/
def p2Fix (s : SOut) (π : P2Pf) : P2Pf := { π with roots := s }

/-- The proof with an IV. -/
def setIv2 (iv : Vector UInt8 32) (π : P2Pf) : P2Pf := { π with iv := iv }

/-- The setup's roots a proof carries. -/
def p2Roots (π : P2Pf) : RecSetupRoots := rootsOfOut π.roots

/-- The public data's `472` bytes (missing bytes `0`). -/
def pubBytes (b : Array UInt8) : Vector UInt8 pLen := Vector.ofFn fun i => b.getD i.val 0

/-- **The rounds' messages the stream carries**, from byte `472`. -/
def p2Msgs (π : P2Pf) : List UniSound.UMsg := UniSound.msgsAt π.proof.stream pLen (RecPiop.pi2Rounds 4)

/-- **What the chain reads of a proof**: the statement (the IV, the input, the public data) and the messages. -/
def p2View (π : P2Pf) : FSt2 × List (RMsg E) :=
  ((π.iv, π.input, pubBytes π.proof.stream), (p2Msgs π).map UniSound.toRMsg)

/-- **The transcript's inputs to the arithmetic**: the public scalars, `α, β, γ`, `t`, the `16` fold values, `ξ`,
`ρ`. -/
def p2Inputs (π : P2Pf) (ch : List (List E)) : Inputs E :=
  let vals := ((p2Msgs π).getD 2 default).2
  ⟨(stOf (p2View π).1).2, (ch.getD 0 []).getD 0 0, (ch.getD 0 []).getD 1 0, (ch.getD 0 []).getD 2 0,
    (ch.getD 1 []).getD 0 0, vals.take 16, vals.getD 16 0, (ch.getD 2 []).getD 0 0⟩

/-- **The arithmetic's values** on the transcript. -/
def p2Out (π : P2Pf) (ch : List (List E)) : Out E := (Spec.of cc).core.run (p2Inputs π ch)

/-- **The run's result** on the transcript (`reduceWith`'s `Reduced`). -/
def p2Reduced (π : P2Pf) (ch : List (List E)) : RecStatement.Reduced :=
  ⟨(p2Inputs π ch).scalars, (p2Inputs π ch).scalars.map pairPoint,
    ((((p2Msgs π).getD 0 default).1.getD default), (((p2Msgs π).getD 1 default).1.getD default)),
    p2Inputs π ch, p2Out π ch⟩

/-! ## The layouts, the shapes, the decoders -/

theorem newOK_setup : NewOK 25 24 25 [(0, 2 ^ 24), (1, 2 ^ 24)] := by decide +kernel

theorem newOK_quotient : NewOK 29 24 28 (RecStatement.quotientChunks 24) := by decide +kernel

/-- `W`'s shape: the plain layout of `2^24` words. -/
@[reducible] noncomputable def shW : WhirShape := UniSound.plainShape 24 le_rfl (by norm_num)

/-- The setup's shape: `κ` then `κ + σ`, `2^25` words. -/
@[reducible] noncomputable def shS : WhirShape :=
  WhirShape.large 25 24 25 [(0, 2 ^ 24), (1, 2 ^ 24)] newOK_setup (by decide) (by decide)

/-- `Q`'s shape: `h` and `q`'s four chunks, three limbs each, `2^28` words, `29` variables. -/
@[reducible] noncomputable def shQ : WhirShape :=
  WhirShape.large 29 24 28 (RecStatement.quotientChunks 24) newOK_quotient (by decide) (by decide)

/-- π1's `k`-th opening's shape: the plain layout of `27`, `27`, `24` variables (its layout word's byte `24`). -/
def pi1Vars (k : ℕ) : ℕ := if k = 2 then 24 else 27

theorem pi1Vars_lo (k : ℕ) : 24 ≤ pi1Vars k := by unfold pi1Vars; split_ifs <;> norm_num

theorem pi1Vars_hi (k : ℕ) : pi1Vars k ≤ 28 := by unfold pi1Vars; split_ifs <;> norm_num

/-- π1's `k`-th opening's shape. -/
@[reducible] noncomputable def sh1 (k : ℕ) : WhirShape :=
  UniSound.plainShape (pi1Vars k) (pi1Vars_lo k) (pi1Vars_hi k)

/-- A column's words as a stack (zero past them). -/
def stackOf {μ : ℕ} (q : Column μ) : Stk := fun j => q.values.toArray.getD j 0

/-- **The decoder of a layout's root, listing stacks**: the Merkle tree of level 0 (height `rootHeight`, leaves of
`8 · 2^6` bytes), the certified list bound `listHi`, the decoded stacks of the Merkle word. -/
noncomputable def colCode (L : WhirBridge.Layout) (R : ℕ) (hw : Whir.Admissible L.logN R) : TableCode Stk where
  height := WhirBridge.rootHeight L.logN R
  leafLen := leafBytes
  bound := (Whir.Params.certOf L.logN R 0).listHi
  dec w := (decodeColumns L.logN R (wordOfMerkle (WhirBridge.rootHeight L.logN R) (2 ^ WhirBridge.laneFold) w)).map
    stackOf
  length_dec w := by
    rw [List.length_map]
    exact length_decodeColumns_le hw _

/-- **The decoders**: `W`'s (round `0`) and `Q`'s (round `1`). -/
noncomputable def p2Tc (i : ℕ) : TableCode Stk :=
  if i = 0 then colCode shW.L shW.R shW.adm else colCode shQ.L shQ.R shQ.adm

/-! ## The claims, the openings -/

/-- π1's calls' words, from the stream and the run's result (`pcsCalls`' first three). -/
def pi1Words (D : RecDeployment) (π : P2Pf) (ch : List (List E)) : List (List (List UInt8)) :=
  (pi1CallsWith D.pi1Calls (p2Roots π).pi1.bytecode).map (·.map (callWord cc.reads π.proof.stream (p2Reduced π ch)))

/-- **π1's `k`-th call decoded** under the registry (`decodeWith`). -/
def pi1Dec (D : RecDeployment) (π : P2Pf) (ch : List (List E)) (k : ℕ) :
    Option (Digest × Opener × List PcsQuotient.Claim) :=
  decodeWith (registryOf D.pi1.shape cc.logN) ((pi1Words D π ch).getD k [])

/-- π1's `k`-th call's claims, as F2's. -/
def pi1Claims (D : RecDeployment) (π : P2Pf) (ch : List (List E)) (k : ℕ) : List WhirBridge.Claim :=
  match pi1Dec D π ch k with
  | some (_, _, cs) => cs.map Bridge.claimTr
  | none => []

/-- π1's `k`-th call's root: its root word's (`rootOfWord`; the word is the stream's or the setup's, not the run's). -/
def pi1Root (D : RecDeployment) (π : P2Pf) (k : ℕ) : Bytes32 :=
  toB (rootOfWord (((pi1Words D π []).getD k []).headD []))

/-- `W`'s claim (its fold at `ρ`). -/
noncomputable def clW (π : P2Pf) (ch : List (List E)) : Stmt shW.L.stacking :=
  toStmt shW.L [⟨(p2Out π ch).witnessPoint, (p2Out π ch).fold⟩]

/-- The setup's claim (at `β`, value `ξ`). -/
noncomputable def clS (π : P2Pf) (ch : List (List E)) : Stmt shS.L.stacking :=
  toStmt shS.L [⟨(p2Out π ch).setupPoint, (p2Inputs π ch).ξ⟩]

/-- `Q`'s two claims (the combination at `t`, `h`'s top coefficient). -/
noncomputable def clQ (π : P2Pf) (ch : List (List E)) : Stmt shQ.L.stacking :=
  toStmt shQ.L [⟨(p2Out π ch).quotientPoint, (p2Out π ch).quotientValue⟩,
    ⟨(p2Out π ch).sumPoint, (p2Out π ch).sumValue⟩]

/-- π1's `k`-th call's claims on its plain layout. -/
noncomputable def cl1 (D : RecDeployment) (k : ℕ) (π : P2Pf) (ch : List (List E)) : Stmt (sh1 k).L.stacking :=
  toStmt (sh1 k).L (pi1Claims D π ch k)

/-- The setup's table at a proof's roots (`Pi2Circuit.setupStack` of the circuit for π1's contract IV). -/
def setupStackAt (D : RecDeployment) (roots : RecSetupRoots) : Array K := (D.circuitAt roots.pi1).setupStack

/-- The setup's table as a column of `2^25` words. -/
def setupCol (D : RecDeployment) (roots : RecSetupRoots) : Column 25 := UniSound.colOf (setupStackAt D roots) 25

/-- A dummy column (a setup target's fixed stack, not read: `p2Stk` gives the stacks). -/
def col0 (μ : ℕ) : Column μ := UniSound.colOf #[] μ

/-- **The six openings**, in the contract's order: π1's `C1`, `C2`, `F` (their roots the calls' root words), π2's
`W` (round `0`), the setup (its root the proof's), `Q` (round `1`). -/
noncomputable def p2Ops (D : RecDeployment) : List (WhirOp P2Pf E Stk) :=
  [⟨sh1 0, cl1 D 0, fun π => π.proof.c1, .setup (fun π => pi1Root D π 0) (col0 _)⟩,
    ⟨sh1 1, cl1 D 1, fun π => π.proof.c2, .setup (fun π => pi1Root D π 1) (col0 _)⟩,
    ⟨sh1 2, cl1 D 2, fun π => π.proof.f, .setup (fun π => pi1Root D π 2) (col0 _)⟩,
    ⟨shW, clW, fun π => π.proof.w, .round 0 stackOf⟩,
    ⟨shS, clS, fun π => π.proof.setup, .setup (fun π => π.roots.2) (col0 _)⟩,
    ⟨shQ, clQ, fun π => π.proof.q, .round 1 stackOf⟩]

/-- **The openings' stacks**: the setup's table at the proof's roots for the setup's opening (the only one of
`2^25` words), none for the others. -/
noncomputable def p2Stk (D : RecDeployment) (o : WhirOp P2Pf E Stk) : Option (P2Pf → Column o.S.L.logN) :=
  if h : o.S.L.logN = 25 then some fun π => cast (by rw [h]) (setupCol D (p2Roots π)) else none

/-! ## The setup -/

/-- The plain shape of `2^25` words, on which the setup's tree is built (its height and leaves are `shS`'s). -/
@[reducible] noncomputable def sh25 : WhirShape := UniSound.plainShape 25 (by norm_num) (by norm_num)

/-- **The composed setup**: π1's three trees (`UniSound.uSetup`), then π2's, of the setup's table at π1's contract IV
of those roots. -/
noncomputable def p2Setup (D : RecDeployment) (hs : UniSound.UniShapes D.pi1) : OracleComp KeccakCalls SOut :=
  UniSound.uSetup D.pi1 hs >>= fun r =>
    stackSetupS sh25 (setupCol D ⟨UniSound.rootsOfS r, default⟩) >>= fun r2 => pure (r, r2)

/-! ## π2's IV, the composed verifier -/

/-- σ's hash input (`digestWith`): its tags, four little-endian bytes each. -/
def sigmaBytes (c : Pi2Circuit) : List UInt8 := (List.range c.n).flatMap fun i ↦ (le64 (c.sigma i)).take 4

/-- κ's hash input: eight bytes each. -/
def kappaBytes (c : Pi2Circuit) : List UInt8 := (List.range c.n).flatMap fun i ↦ le64 (c.kappa i).lane.toNat

/-- The circuit's digest's input (`digestWith`): the encoding, σ's and κ's hashes. -/
def digIn (c : Pi2Circuit) (sg kp : Bytes32) : List UInt8 := c.circuit.encoding ++ sg.toList ++ kp.toList

/-- π2's IV's input (`prover::iv`): the tag, π1's contract IV, π2's setup root, the circuit's digest, the layout words. -/
def ivIn (D : RecDeployment) (roots : RecSetupRoots) (d : Bytes32) : List UInt8 :=
  ivTag ++ D.pi1IvAt roots.pi1 ++ digestBytes roots.pi2 ++ d.toList ++
    (RecStatement.layoutWords cc.logN).1 ++ (RecStatement.layoutWords cc.logN).2.1 ++
    (RecStatement.layoutWords cc.logN).2.2

/-- **π2's IV** as the composed verifier computes it, with its intermediate answers: σ's and κ's hashes, the circuit's
digest, then the IV (`prover::iv`), four Keccak-256 calls. -/
def p2IvKC4 (D : RecDeployment) (π : P2Pf) : OracleComp KeccakCalls (Bytes32 × Bytes32 × Bytes32 × Bytes32) :=
  hash256 (sigmaBytes (D.circuitAt (p2Roots π).pi1)) >>= fun sg =>
    hash256 (kappaBytes (D.circuitAt (p2Roots π).pi1)) >>= fun kp =>
      hash256 (digIn (D.circuitAt (p2Roots π).pi1) sg kp) >>= fun d =>
        hash256 (ivIn D (p2Roots π) d) >>= fun iv => pure (sg, kp, d, iv)

/-- The four IV calls' log (input, answer), from their answers. -/
def ivLog (D : RecDeployment) (π : P2Pf) (x : Bytes32 × Bytes32 × Bytes32 × Bytes32) : Transcript :=
  [(sigmaBytes (D.circuitAt (p2Roots π).pi1), x.1), (kappaBytes (D.circuitAt (p2Roots π).pi1), x.2.1),
    (digIn (D.circuitAt (p2Roots π).pi1) x.1 x.2.1, x.2.2.1), (ivIn D (p2Roots π) x.2.2.1, x.2.2.2)]

/-- **The composed verifier with the IV**: π2's IV, then the chain and the six openings on the proof carrying it. -/
noncomputable def p2Ver (D : RecDeployment) (π : P2Pf) :
    OracleComp KeccakCalls ((Bytes32 × Bytes32 × Bytes32 × Bytes32) × (List (List E) × List Bool)) :=
  p2IvKC4 D π >>= fun x => (fun v => (x, v)) <$>
    verU pi2Spec p2View (opsRun p2View (p2Ops D)) (setIv2 x.2.2.2 π)

/-- The outcome with the IV written in the proof. -/
def ivOut2 (z : P2Pf × ((Bytes32 × Bytes32 × Bytes32 × Bytes32) × (List (List E) × List Bool))) :
    P2Pf × (List (List E) × List Bool) :=
  (setIv2 z.2.1.2.2.2 z.1, z.2.2)

/-- **The two-oracle adversary with the IV**: `A₀`, then the IV of the proof the setup fixes. -/
def p2IvAdv (D : RecDeployment) (A₀ : SOut → OracleComp KeccakCalls P2Pf) (s : SOut) :
    OracleComp KeccakCalls P2Pf :=
  A₀ s >>= fun π => (fun x => setIv2 x.2.2.2 π) <$> p2IvKC4 D (p2Fix s π)

/-- **The adversary of the composed game**: π2's adversary given the setup's roots, its input and proof. -/
def p2Adv (A : RecAdversary) (s : SOut) : OracleComp Common.RandomPermutationOracles P2Pf :=
  (fun z : Vector UInt8 32 × RecProof => (⟨z.1, z.2, Vector.replicate 32 0, s⟩ : P2Pf)) <$> A (rootsOfOut s)

/-! ## The check, the links -/

/-- **The verifier's check** (what an accepting run satisfies): the stream of `944` bytes, the challenges of the
rounds' lengths, and the value the contract requires nonzero. -/
def p2Check (π : P2Pf) (ch : List (List E)) : Prop :=
  π.proof.stream.size = sLen ∧ ch.length = 3 ∧ (ch.getD 0 []).length = 3 ∧ (ch.getD 1 []).length = 1 ∧
    (ch.getD 2 []).length = 1 ∧ (p2Out π ch).all ≠ 0

/-- **A candidate is good**: at `W`'s round, a stack satisfying `W`'s claim; at `Q`'s, one satisfying both of
`Q`'s. -/
def p2Good (i : ℕ) (π : P2Pf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧
      ClaimOn (layoutsOf cc.logN).1 q ((p2Out π ch).witnessPoint, (p2Out π ch).fold)
  else if i = 1 then ∃ q, c = some q ∧
      ClaimOn (layoutsOf cc.logN).2.1 q ((p2Out π ch).quotientPoint, (p2Out π ch).quotientValue) ∧
      ClaimOn (layoutsOf cc.logN).2.1 q ((p2Out π ch).sumPoint, (p2Out π ch).sumValue)
  else True

/-- **The setup's table is good**: it satisfies the setup's claim. -/
def p2GoodS (D : RecDeployment) (π : P2Pf) (ch : List (List E)) : Prop :=
  ClaimOn (layoutsOf cc.logN).2.2 (fun j ↦ (setupStackAt D (p2Roots π)).getD j 0)
    ((p2Out π ch).setupPoint, (p2Inputs π ch).ξ)

/-! ## The composed event, the bridge facts -/

/-- **π2's break on the composed game's outcome**: the check, the six openings accept, and no candidate of `W`'s
root read off the transcript has `P`. -/
def P2BreaksRel (D : RecDeployment) (P : RecSetupRoots → Pi2St → Stk → Prop) (z : OutK P2Pf E (List Bool)) : Prop :=
  p2Check z.1.1 z.1.2.1 ∧ (∀ k < (p2Ops D).length, z.1.2.2.getD k false = true) ∧
    ∀ c ∈ extractorK (fun i => (p2Tc i).commit) p2View z, ∀ q, c = some q →
      ¬ P (p2Roots z.1.1) (stOf (p2View z.1.1).1) q

/-- The setup's roots as bytes. -/
def rootsB2 (t : RecSetupTrees) : SOut :=
  ((toB t.pi1.bytecode.root, toB t.pi1.a0.root, toB t.pi1.b0.root), toB t.pi2.root)

/-- The setup's Keccak-256 evaluations as a transcript. -/
def setupTr2 (t : RecSetupTrees) : Transcript := t.evaluations.map fun e => (e.1, toB e.2)

/-- **SETUP**: the composed setup over `π`, logged, is the Statement's `setupTreesWith` over `π`, its roots as bytes,
its log the trees' evaluations. -/
def Pi2SetupBridge (D : RecDeployment) (hs : UniSound.UniShapes D.pi1) : Prop :=
  simulateQ keccakCallsOverQueryPermutation (loggedKC (p2Setup D hs)) =
    (fun t : RecSetupTrees => (rootsB2 t, setupTr2 t)) <$> D.setupTreesWith Common.queryPermutation

/-- **WALK**: on a stream of `944` bytes, in every lawful monad and over every permutation, π2's run's verdict and
result are the chain's challenges read by the value the contract requires nonzero and the result `p2Reduced`, the
chain over Keccak-256 the sponge over the permutation. -/
def Pi2Walk : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (π : P2Pf), π.proof.stream.size = sLen →
      (fun o : RecStatement.Outcome => (o.accepts, o.result)) <$>
          runWith F (Spec.of cc) π.iv.toList π.input.toList π.proof.stream =
        (fun ch => ((p2Reduced π ch).out.all != 0,
            (Except.ok (p2Reduced π ch) : Except UniStatement.UniError RecStatement.Reduced))) <$>
          pi2Spec.chain (fun x => toB <$> keccak256With F x) (p2View π).1 (p2View π).2

/-- **WALK REJECTS**: on a stream of another length, every outcome of π2's run over `π` rejects. -/
def Pi2WalkReject : Prop :=
  ∀ π : P2Pf, π.proof.stream.size ≠ sLen →
    ∀ o ∈ support (runWith Common.queryPermutation (Spec.of cc) π.iv.toList π.input.toList π.proof.stream),
      o.accepts = false

/-- **EXTRACTOR READING**: on a stream holding `W`'s root, a candidate of `W`'s root that the composed extractor reads
off the setup's log and a permutation transcript is a stack of π2's extractor's list (`wCandidates`) on the setup's
evaluations and that transcript. (On a shorter stream the composed view pads the root with zeros in place, π2's
extractor's `streamRoot` reads the shorter slice: the two roots may differ.) -/
def Pi2ExtractBridge (D : RecDeployment) : Prop :=
  ∀ (t : RecSetupTrees) (T : Common.OracleQueryLog) (z : P2Pf × (List (List E) × List Bool)) (q : Stk),
    pLen + 32 ≤ z.1.proof.stream.size →
    some q ∈ extractorK (fun i => (p2Tc i).commit) p2View (z, setupTr2 t ++ evalTr (permutationQueries T)) →
      ∃ w ∈ wCandidates D t.roots (preimagesOf t.evaluations T) z.1.proof, stkOf w = q

end RecCompose
