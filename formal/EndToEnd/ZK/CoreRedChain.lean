-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The chain (`Chain.startWith`, `squeezeWith`, `reduceWith`), Keccak-256 over a permutation
-- (`keccak256With`), the opening's sponge (`Sponge`, `seedInput`) and the byte helpers
-- (`bytesLane`, `Digest.toRpm`, `Digest.ofRpm`) are leanerVM's (branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0), as `formal/Statement` adapts them.
import ZK.CoreDefs
import ZK.ProverBridgeDuplex
import ZK.ProverBridgeMerkle
import Bridge.Chain

/-!
# The skeleton's chain and seeds are the statement's

The skeleton (`Deployed.skel`) runs the reduction's Keccak-256 chain and each opening's seed as
oracle queries; against the oracle `G = Gof (kDet π) π gH gF` (Keccak-256 over `π` and `π`, any
completions) they are the statement's computations over `π` (`reduceWith`, `proveWith`'s chain,
`openingSpongeWith`). Here, without evaluating anything large:

* **the bytes**: a digest's 32 bytes and back, both ways (`toBytes_digestOfBytes'`; the skeleton's
  answers carry bytes, the statement's chain digests); the two decodings of a chain answer agree
  (**`dH_eq_chainChal`**: the joint model's `dH` with the deployed limbs is the renderer's
  `chainChal`, for every answer); a value's limbs round-trip (`eOfLimbs_limbsOf`);
* **the chain's steps** (`startWith_run`, `squeezeWith_run`): the statement's seed and squeezes over
  `π` are `G`'s answers decoded;
* **the chain** (`chainOuts`: the five answers the skeleton's chain receives, from the index root, the
  two roots, the statement's bytes and the five values' limbs): **`reduceWith_skel`**, the statement's
  reduction over `π` on the proof the roots and values make is `chainClaims` (the verifier's claims
  at the decoded answers) with the roots; `chainClaims_chainOuts`: those claims are `claimsAt` at the
  decoded answers;
* **the values** (`valsOf`, `reductionOf_valsOf`): the skeleton's five value limbs read back by `fmt`
  are the values;
* **the opening's seed** (`seed_rel`, `runDet_seed`): the skeleton's seed from its IV is related
  (`Duplex.Rel`, nothing pending) to the statement's `openingSpongeWith`, when the IV's prefix is the
  statement's (`ivPrefix_eq`; the three deployed shapes: `ivPrefix_witness`, `ivPrefix_wiring`,
  `ivPrefix_quotient`, the layouts' identifiers never evaluated).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Sponge seedInput)
open QuotientZk.Deployed (Inp Out Msg Item KSt DSpec Tbl Pos kcTag)
open QuotientRpm (Limbs rootWords scalarWord stateLimbs)

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

open Render (limbsOf chainChal)

/-! ## Bytes and limbs -/

/-- The deployed limbs of `E` are the statement's (`Soundness.eLimbs`). -/
theorem limbsE_eq : limbsE = Soundness.eLimbs := Equiv.ext fun _ ↦ rfl

theorem eLimbs_apply (x : E) : Soundness.eLimbs x = limbsOf x := rfl

/-- **A value's limbs read back.** -/
theorem eOfLimbs_limbsOf (x : E) : eOfLimbs (limbsOf x) = x :=
  Soundness.eLimbs.symm_apply_apply x

theorem bytesLane_take8 (l : List UInt8) :
    LeanVM.Rpm.bytesLane (l.take 8) = LeanVM.Rpm.bytesLane l := by
  unfold LeanVM.Rpm.bytesLane
  congr 1
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldr_append, List.foldr_cons,
    List.foldr_nil, List.getD_eq_getElem?_getD, List.getElem?_take]
  simp

/-- **Every 32 bytes are a digest's**: read as lanes and written back. -/
theorem digestBytes_digestOfBytes (b : QuotientRpm.Bytes32) :
    digestBytes (digestOfBytes b) = b.toList := by
  have e : (digestOfBytes b).toList = List.ofFn fun i : Fin 4 ↦ leLane b.toList i := by
    unfold digestOfBytes
    rw [Vector.toList_ofFn]
    refine congrArg List.ofFn (funext fun i ↦ ?_)
    rw [bytesLane_take8, LeanVM.Rpm.leLane_eq_bytesLane]
  calc digestBytes (digestOfBytes b)
      = LeanVM.Rpm.lanesBytes (List.ofFn fun i : Fin 4 ↦ leLane b.toList i) := congrArg _ e
    _ = b.toList := LeanVM.Rpm.lanesBytes_ofFn_leLane _ 4 (by simp)

theorem toBytes_digestOfBytes' (b : QuotientRpm.Bytes32) : Digest.toBytes (digestOfBytes b) = b :=
  Vector.toList_inj.mp (by rw [Merkle.toBytes_toList, digestBytes_digestOfBytes])

theorem toB_eq_toBytes (d : Digest) : Compose.toB d = Digest.toBytes d :=
  Vector.toList_inj.mp (by rw [Bridge.toB_toList, Merkle.toBytes_toList])

theorem toB_digestOfBytes (b : QuotientRpm.Bytes32) : Compose.toB (digestOfBytes b) = b := by
  rw [toB_eq_toBytes, toBytes_digestOfBytes']

/-- **A chain answer's challenge** (`chainChal`) is its state's low 192 bits as limbs. -/
theorem chainChal_eq (o : Out) : chainChal o = Soundness.eLimbs.symm (stateLimbs o.1) := by
  unfold Render.chainChal
  rw [Bridge.challengeOf_eq, toB_digestOfBytes]

/-- **The two decodings of a chain answer agree**: the joint model's `dH` with the deployed limbs is
the renderer's `chainChal`. -/
theorem dH_eq_chainChal (o : Out) : QuotientZk.Instance.dH deployedRep.limbs o = chainChal o := by
  rw [chainChal_eq]
  show limbsE.symm _ = _
  rw [limbsE_eq]

/-- A scalar's chain word (`scalarBytes`) is the skeleton's `scalarWord` of its limbs. -/
theorem scalarBytes_eq (x : E) : Transcript.scalarBytes x = scalarWord (limbsOf x) := rfl

/-- A root's two scalars as the chain hashes them are the skeleton's `rootWords` of its bytes. -/
theorem rootWords_toBytes (r : Digest) :
    rootWords (Digest.toBytes r) =
      Transcript.scalarBytes (digestScalars r).1 ++ Transcript.scalarBytes (digestScalars r).2 := by
  rw [← toB_eq_toBytes]
  exact Bridge.rootScalars_eq _ r (digestOfScalars_digestScalars r)

/-- **The chain's label** as the skeleton hashes it: the tag, the index root's bytes, `y ‖ root`. -/
theorem label_bytes (ir : Digest) (stmt : Statement) :
    label ir stmt = kcTag ++ (Digest.toBytes ir).toList ++ (stmtBytesD stmt).toList := by
  rw [Bridge.label_eq, Compose.labelOf, toB_eq_toBytes]
  rfl

/-! ## The oracle's Keccak-256 answers -/

section Oracle

variable (π : Equiv.Perm Eager.St) (gH : List UInt8 → KSt) (gF : KSt → DigestBytes)

local notation "G" => Gof (kDet π) π gH gF

/-- Keccak-256 over `π`, as a digest. -/
abbrev kS (m : List UInt8) : Digest := (keccak256With (permId π) m).run

theorem kDet_eq (m : List UInt8) : kDet π m = Digest.toBytes (kS π m) := rfl

theorem G_fst (m : List UInt8) : (G (.inl m)).1 = kDet π m := rfl

theorem digestOfBytes_kDet (m : List UInt8) : digestOfBytes (kDet π m) = kS π m :=
  Merkle.digestOfBytes_toBytes _

theorem chainChal_G (m : List UInt8) :
    chainChal (G (.inl m)) = Transcript.challengeOf (kS π m) := by
  unfold Render.chainChal
  rw [G_fst, digestOfBytes_kDet]

/-- **The chain's seed** over `π`: the digest of `G`'s answer. -/
theorem startWith_run (l : List UInt8) :
    (Transcript.Chain.startWith (permId π) l).run = ⟨digestOfBytes (kDet π l), []⟩ := by
  rw [digestOfBytes_kDet]
  rfl

/-- **A squeeze** over `π`: the challenge `chainChal` of `G`'s answer to the state's bytes and the
pending scalars' words, the new state its digest. -/
theorem squeezeWith_run (c : Transcript.Chain) :
    (c.squeezeWith (permId π)).run =
      (chainChal (G (.inl (digestBytes c.state ++ c.pending.flatMap Transcript.scalarBytes))),
        ⟨digestOfBytes (G (.inl (digestBytes c.state ++
          c.pending.flatMap Transcript.scalarBytes))).1, []⟩) := by
  rw [chainChal_G, G_fst, digestOfBytes_kDet]
  rfl

/-! ## The chain -/

/-- **The skeleton's five value limbs** of the values `v` (`whirRenderer`'s step-4 message). -/
def valsOf (v : QuotientZk.Instance.Vals E) : List Limbs := (List.ofFn v.1 ++ [v.2]).map limbsOf

/-- **The skeleton's chain answers** against `G` (`skel`): from the index root `ir`, the witness
and quotient roots `rW`, `rQ`, the statement's bytes `sb` and the five values' limbs `vals`, the
answers `o₁ … o₅` of `α, β, γ, t, ρ`. -/
def chainOuts (ir rW rQ : Digest) (sb : Vector UInt8 64) (vals : List Limbs) : List Out :=
  let st₀ := kDet π (kcTag ++ (Digest.toBytes ir).toList ++ sb.toList)
  let o₁ := G (.inl (st₀.toList ++ rootWords (Digest.toBytes rW)))
  let o₂ := G (.inl o₁.1.toList)
  let o₃ := G (.inl o₂.1.toList)
  let o₄ := G (.inl (o₃.1.toList ++ rootWords (Digest.toBytes rQ)))
  let o₅ := G (.inl (o₄.1.toList ++ vals.flatMap scalarWord))
  [o₁, o₂, o₃, o₄, o₅]

theorem length_chainOuts (ir rW rQ : Digest) (sb : Vector UInt8 64) (vals : List Limbs) :
    (chainOuts π gH gF ir rW rQ sb vals).length = 5 := rfl

theorem ofFn_four {α : Type} (f : Fin 4 → α) : List.ofFn f = [f 0, f 1, f 2, f 3] := by
  simp [List.ofFn_succ]

/-- The values' words (`Wire.valueWords`) are the skeleton's words of their limbs. -/
theorem valueWords_eq (v : QuotientZk.Instance.Vals E) :
    (Soundness.deployedWire instD).valueWords v = (valsOf v).flatMap scalarWord := by
  simp only [QuotientRpm.Wire.valueWords, QuotientRpm.Wire.word, valsOf, ofFn_four, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]
  rfl

/-- **F4's chain over `π`** on the proof the roots and the values make: its challenges are the
decoded answers of `chainOuts`. -/
theorem chainWith_run (ir rW rQ : Digest) (stmt : Statement) (a : Vector E 4) (next : E) :
    (Compose.chainWith (Soundness.deployedWire instD)
      (fun l ↦ Compose.toB <$> keccak256With (permId π) l)
      (Bridge.rootProofIr ir stmt ⟨digestScalars rW, digestScalars rQ, a, next⟩ rW rQ)).run =
      ⟨chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 0 default),
        chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 1 default),
        chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 2 default),
        chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 3 default),
        chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 4 default)⟩ := by
  have hH : ∀ l, (Compose.toB <$> keccak256With (permId π) l : Id QuotientRpm.Bytes32) =
      pure (kDet π l) := fun l ↦ by
    rw [kDet_eq, ← toB_eq_toBytes]
    rfl
  have hc : ∀ st, (Soundness.deployedWire instD).chal st = Soundness.eLimbs.symm (stateLimbs st) :=
    fun _ ↦ rfl
  simp only [Compose.chainWith, hH, pure_bind, Id.run_pure, Bridge.rootProofIr,
    QuotientRpm.Wire.afterRoot, QuotientRpm.Wire.afterValues, valueWords_eq, Compose.labelOf,
    toB_eq_toBytes, chainOuts, List.getD_cons_zero, List.getD_cons_succ, chainChal_eq, G_fst, hc,
    stmtBytesD]
  rfl

theorem ofFn_get_vec (a : Vector E 4) : Vector.ofFn a.get = a :=
  Vector.ext fun i hi ↦ by rw [Vector.getElem_ofFn]; rfl

/-- **The verifier's claims at the skeleton's chain answers** (`chainClaims`) are `claimsAt` at
their decoded challenges. -/
theorem chainClaims_chainOuts (ir rW rQ : Digest) (stmt : Statement) (vals : List Limbs)
    (rest : List Out) (v : QuotientZk.Instance.Vals E) :
    Render.chainClaims stmt (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) vals ++ rest) v =
      claimsAt logRows stmt
        (chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) vals).getD 0 default))
        (chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) vals).getD 1 default))
        (chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) vals).getD 2 default))
        (chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) vals).getD 3 default))
        (chainChal ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) vals).getD 4 default))
        (Vector.ofFn v.1) v.2 := by
  have e : ∀ i < 5, (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) vals ++ rest).getD i default =
      (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) vals).getD i default := fun i hi ↦ by
    rw [List.getD_append _ _ _ _ (by rw [length_chainOuts]; exact hi)]
  unfold Render.chainClaims
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num)]

/-- **The statement's reduction over `π` is the skeleton's chain**: on the proof the roots `rW`,
`rQ` and the values `a`, `next` make, `reduceWith` (the index root `ir`) returns the roots and the
verifier's claims at the decoded answers of `chainOuts` (`chainClaims`), the skeleton's chain on the
same roots and on the values' limbs. -/
theorem reduceWith_skel (ir rW rQ : Digest) (stmt : Statement) (a : Vector E 4) (next : E) :
    (reduceWith (permId π) logRows ir stmt ⟨digestScalars rW, digestScalars rQ, a, next⟩).run =
      (Render.chainClaims stmt (chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next)))
        (a.get, next)).map fun cl ↦ ⟨rW, rQ, cl⟩ := by
  show (reduceWith (permId π) 22 ir stmt ⟨digestScalars rW, digestScalars rQ, a, next⟩).run = _
  rw [Bridge.reduceWith_eq (permId π) (Soundness.deployedWire instD) rfl ir stmt _ rW rQ
    (digestOfScalars_digestScalars rW) (digestOfScalars_digestScalars rQ), Id.run_map,
    chainWith_run π gH gF]
  have e := chainClaims_chainOuts π gH gF ir rW rQ stmt (valsOf (a.get, next)) [] (a.get, next)
  rw [List.append_nil] at e
  rw [e, ofFn_get_vec]
  rfl

/-- **The decoded chain answers are the statement's challenges**: `reduceWith`'s claims are
`claimsAt` at `chainChal oᵢ`, equivalently at `dH deployedRep.limbs oᵢ` (`dH_eq_chainChal`). -/
theorem reduceWith_skel_claimsAt (ir rW rQ : Digest) (stmt : Statement) (a : Vector E 4)
    (next : E) :
    (reduceWith (permId π) logRows ir stmt ⟨digestScalars rW, digestScalars rQ, a, next⟩).run =
      (claimsAt logRows stmt
        (QuotientZk.Instance.dH deployedRep.limbs
          ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 0 default))
        (QuotientZk.Instance.dH deployedRep.limbs
          ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 1 default))
        (QuotientZk.Instance.dH deployedRep.limbs
          ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 2 default))
        (QuotientZk.Instance.dH deployedRep.limbs
          ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 3 default))
        (QuotientZk.Instance.dH deployedRep.limbs
          ((chainOuts π gH gF ir rW rQ (stmtBytesD stmt) (valsOf (a.get, next))).getD 4 default))
        a next).map fun cl ↦ ⟨rW, rQ, cl⟩ := by
  have e := chainClaims_chainOuts π gH gF ir rW rQ stmt (valsOf (a.get, next)) [] (a.get, next)
  rw [List.append_nil, ofFn_get_vec] at e
  rw [reduceWith_skel, e]
  simp only [dH_eq_chainChal]

/-! ## The chain's steps (the statement's prover's chain, `proveWith`) -/

/-- **The seed** of the chain over `π` from the label: the digest of the skeleton's first hash. -/
theorem startWith_label (ir : Digest) (stmt : Statement) :
    (Transcript.Chain.startWith (permId π) (label ir stmt)).run =
      ⟨digestOfBytes (kDet π (kcTag ++ (Digest.toBytes ir).toList ++ (stmtBytesD stmt).toList)), []⟩ := by
  rw [startWith_run, label_bytes]

/-- **A squeeze after a root**: from the state `st` (as a digest, nothing pending), the root `r`'s two
halves absorbed, the challenge is `chainChal` of `G`'s answer to `st ‖ rootWords r` (the skeleton's
`α`, `t` queries). -/
theorem squeeze_root (st : QuotientRpm.Bytes32) (r : Digest) :
    ((((⟨digestOfBytes st, []⟩ : Transcript.Chain).absorb (digestScalars r).1).absorb
        (digestScalars r).2).squeezeWith (permId π)).run =
      (chainChal (G (.inl (st.toList ++ rootWords (Digest.toBytes r)))),
        ⟨digestOfBytes (G (.inl (st.toList ++ rootWords (Digest.toBytes r)))).1, []⟩) := by
  rw [squeezeWith_run]
  have e : digestBytes (((⟨digestOfBytes st, []⟩ : Transcript.Chain).absorb (digestScalars r).1).absorb
        (digestScalars r).2).state ++
      ((((⟨digestOfBytes st, []⟩ : Transcript.Chain).absorb (digestScalars r).1).absorb
        (digestScalars r).2).pending.flatMap Transcript.scalarBytes) =
      st.toList ++ rootWords (Digest.toBytes r) := by
    simp only [Transcript.Chain.absorb, digestBytes_digestOfBytes, List.nil_append,
      List.singleton_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      rootWords_toBytes]
  rw [e]

/-- **A plain squeeze** (`β`, `γ`): the challenge of `G`'s answer to the state's bytes. -/
theorem squeeze_plain (st : QuotientRpm.Bytes32) :
    ((⟨digestOfBytes st, []⟩ : Transcript.Chain).squeezeWith (permId π)).run =
      (chainChal (G (.inl st.toList)), ⟨digestOfBytes (G (.inl st.toList)).1, []⟩) := by
  rw [squeezeWith_run]
  have e : digestBytes (⟨digestOfBytes st, []⟩ : Transcript.Chain).state ++
      (⟨digestOfBytes st, []⟩ : Transcript.Chain).pending.flatMap Transcript.scalarBytes =
      st.toList := by
    simp only [digestBytes_digestOfBytes, List.flatMap_nil, List.append_nil]
  rw [e]

theorem flatMap_limbsOf (l : List E) :
    (l.map limbsOf).flatMap scalarWord = l.flatMap Transcript.scalarBytes := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, List.flatMap_cons, ih, List.flatMap_cons]; rfl

/-- **The squeeze after the values** (`ρ`): the values absorbed in order, the challenge of `G`'s
answer to the state's bytes and the values' limbs' words. -/
theorem squeeze_vals (st : QuotientRpm.Bytes32) (a : Vector E 4) (next : E) :
    (((a.toList.foldl Transcript.Chain.absorb (⟨digestOfBytes st, []⟩ : Transcript.Chain)).absorb
        next).squeezeWith (permId π)).run =
      (chainChal (G (.inl (st.toList ++ (valsOf (a.get, next)).flatMap scalarWord))),
        ⟨digestOfBytes (G (.inl (st.toList ++ (valsOf (a.get, next)).flatMap scalarWord))).1, []⟩) := by
  rw [squeezeWith_run]
  have hv : (valsOf (a.get, next)).flatMap scalarWord =
      (a.toList ++ [next]).flatMap Transcript.scalarBytes := by
    rw [valsOf, ← flatMap_limbsOf]
    congr 2
    rw [← Vector.toList_ofFn, ofFn_get_vec]
  have e : digestBytes ((a.toList.foldl Transcript.Chain.absorb
        (⟨digestOfBytes st, []⟩ : Transcript.Chain)).absorb next).state ++
      ((a.toList.foldl Transcript.Chain.absorb
        (⟨digestOfBytes st, []⟩ : Transcript.Chain)).absorb next).pending.flatMap
          Transcript.scalarBytes =
      st.toList ++ (valsOf (a.get, next)).flatMap scalarWord := by
    rw [hv]
    simp only [Transcript.Chain.absorb, Bridge.foldl_absorb, Bridge.foldl_absorb_state,
      digestBytes_digestOfBytes, List.nil_append]
  rw [e]

/-- **The skeleton's chain answers are the statement's squeezes**: `chainOuts`'s answers are `G`'s to
the inputs the statement's chain hashes, step by step (`startWith_label`, `squeeze_root`,
`squeeze_plain`, `squeeze_vals`). -/
theorem chainOuts_eq (ir rW rQ : Digest) (sb : Vector UInt8 64) (vals : List Limbs) :
    chainOuts π gH gF ir rW rQ sb vals =
      let st₀ := kDet π (kcTag ++ (Digest.toBytes ir).toList ++ sb.toList)
      let o₁ := G (.inl (st₀.toList ++ rootWords (Digest.toBytes rW)))
      let o₂ := G (.inl o₁.1.toList)
      let o₃ := G (.inl o₂.1.toList)
      let o₄ := G (.inl (o₃.1.toList ++ rootWords (Digest.toBytes rQ)))
      [o₁, o₂, o₃, o₄, G (.inl (o₄.1.toList ++ vals.flatMap scalarWord))] := rfl

/-- The skeleton's chain queries against an oracle: the answer, recorded while challenges remain. -/
theorem runDet_chalH {S₀ : Type} (P : QuotientZk.Proto S₀ Inp Out Msg Tbl Pos) (G' : Inp → Out)
    (s : S₀) (m : List UInt8) (hist : List Out) :
    runDet P G' s (QuotientZk.Deployed.chalH m) hist =
      ((G' (.inl m)).1, if hist.length < P.n then hist ++ [G' (.inl m)] else hist) := by
  unfold QuotientZk.Deployed.chalH
  rw [runDet_query_bind]
  exact Merkle.runDet_pure P G' s _ _

/-! ## The values -/

theorem length_valsOf (v : QuotientZk.Instance.Vals E) : (valsOf v).length = 5 := by
  simp [valsOf]

/-- **The skeleton reads the five values' limbs** from the step-4 message. -/
theorem takeScalars_valsOf (v : QuotientZk.Instance.Vals E) (rest : Msg) :
    QuotientZk.Deployed.takeScalars (.scalars (valsOf v) :: rest) 5 = (valsOf v, rest) := by
  simp only [QuotientZk.Deployed.takeScalars,
    List.take_append_of_le_length (le_of_eq (length_valsOf v).symm),
    List.take_of_length_le (le_of_eq (length_valsOf v))]

theorem getD_valsOf_lt (v : QuotientZk.Instance.Vals E) (j : Fin 4) :
    (valsOf v).getD j.val (0, 0, 0) = limbsOf (v.1 j) := by
  fin_cases j <;> simp [valsOf]

theorem getD_valsOf_four (v : QuotientZk.Instance.Vals E) :
    (valsOf v).getD 4 (0, 0, 0) = limbsOf v.2 := by
  simp [valsOf]

/-- **`fmt`'s reduction proof of the skeleton's**: roots that are the digests' bytes and the values'
limbs give the digests' halves and the values. -/
theorem reductionOf_valsOf (rW rQ : Digest) (v : QuotientZk.Instance.Vals E)
    (os : List (List Limbs × List (List ℕ × List (List UInt64) × List QuotientRpm.Bytes32))) :
    reductionOf ⟨Digest.toBytes rW, Digest.toBytes rQ, valsOf v, os⟩ =
      ⟨digestScalars rW, digestScalars rQ, Vector.ofFn v.1, v.2⟩ := by
  unfold reductionOf
  simp only [Merkle.digestOfBytes_toBytes, getD_valsOf_four, eOfLimbs_limbsOf]
  congr 1
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  rw [getD_valsOf_lt v ⟨i, hi⟩, eOfLimbs_limbsOf]

/-! ## The opening's seed -/

/-- The seed's input from an IV that is a digest's bytes is the statement's (`seedInput` with the
zero public digest). -/
theorem seedInput_toBytes (d : Digest) :
    QuotientZk.Deployed.seedInput (Digest.toBytes d) = seedInput d PcsQuotient.zeroDigest := by
  apply Vector.ext
  intro i hi
  have hl : ∀ j (hj : j < 4), LeanVM.Rpm.bytesLane
      (((Digest.toBytes d).toList.drop (8 * j)).take 8) = d[j] := fun j hj ↦ by
    have h := congrArg (fun x : Digest ↦ x[j]) (Merkle.digestOfBytes_toBytes d)
    simpa only [digestOfBytes, Vector.getElem_ofFn] using h
  simp only [QuotientZk.Deployed.seedInput, seedInput, Vector.getElem_ofFn]
  by_cases h4 : i < 4
  · simp only [h4, ↓reduceIte, ↓reduceDIte]
    exact hl i h4
  · by_cases h8 : i < 8
    · simp [h4, h8, PcsQuotient.zeroDigest]
    · simp [h4, h8]

/-- **The skeleton's seed is related to the statement's opening sponge**: from the IV
`kDet π (prefix ‖ claims)`, when the skeleton's IV prefix is the statement's, the permuted seed
input (nothing pending) is `Duplex.Rel`ated to `openingSpongeWith` over `π`. -/
theorem seed_rel (L : Layout) (sh : QuotientZk.Deployed.OpenShape)
    (hpre : sh.ivPrefix = openingLabel ++ u64Bytes openingVersion ++ digestBytes L.id ++
      u64Bytes L.logN ++ u64Bytes logInvRate) (cls : List Claim) :
    Duplex.Rel ⟨π (QuotientZk.Deployed.seedInput (kDet π (sh.ivPrefix ++ claimBytes cls))), []⟩
      (openingSpongeWith (permId π) L cls).run := by
  have e : (openingSpongeWith (permId π) L cls).run =
      ⟨π (seedInput (kS π (sh.ivPrefix ++ claimBytes cls)) PcsQuotient.zeroDigest), []⟩ := by
    rw [hpre]
    rfl
  rw [e, kDet_eq, seedInput_toBytes]
  exact ⟨fun i _ ↦ (Duplex.lane_eq_getElem _ i).symm, rfl⟩

/-- **The skeleton's IV and seed against `G`**: the IV is `kDet π` of the bytes, the duplex the
permuted seed input with nothing pending, the challenges untouched. -/
theorem runDet_seed {S₀ : Type} (P : QuotientZk.Proto S₀ Inp Out Msg Tbl Pos) (s : S₀)
    (b : List UInt8) (hist : List Out) :
    runDet P G s (QuotientZk.Deployed.hashH b >>= QuotientZk.Deployed.seed) hist =
      (⟨π (QuotientZk.Deployed.seedInput (kDet π b)), []⟩, hist) := by
  rw [Merkle.runDet_bind, Merkle.runDet_hashH]
  unfold QuotientZk.Deployed.seed
  rw [Merkle.runDet_bind, Duplex.runDet_perm, Merkle.runDet_pure]
  rfl

/-- **The skeleton's seed of an opening is the statement's**, as runs: `runDet_seed` and
`seed_rel`. -/
theorem runDet_seed_rel {S₀ : Type} (P : QuotientZk.Proto S₀ Inp Out Msg Tbl Pos) (s : S₀)
    (L : Layout) (sh : QuotientZk.Deployed.OpenShape)
    (hpre : sh.ivPrefix = openingLabel ++ u64Bytes openingVersion ++ digestBytes L.id ++
      u64Bytes L.logN ++ u64Bytes logInvRate) (cls : List Claim) (hist : List Out) :
    (runDet P G s (QuotientZk.Deployed.hashH (sh.ivPrefix ++ claimBytes cls) >>=
        QuotientZk.Deployed.seed) hist).2 = hist ∧
      Duplex.Rel (runDet P G s (QuotientZk.Deployed.hashH (sh.ivPrefix ++ claimBytes cls) >>=
        QuotientZk.Deployed.seed) hist).1 (openingSpongeWith (permId π) L cls).run := by
  rw [runDet_seed]
  exact ⟨rfl, seed_rel π L sh hpre cls⟩

end Oracle

/-! ## The deployed prefixes -/

/-- **The skeleton's IV prefix is the statement's** for a layout's identifier and size. -/
theorem ivPrefix_eq (L : Layout) (n : ℕ) (hn : L.logN = n) :
    QuotientZk.Deployed.ivPrefix (Digest.toBytes L.id) n =
      openingLabel ++ u64Bytes openingVersion ++ digestBytes L.id ++ u64Bytes L.logN ++
        u64Bytes logInvRate := by
  rw [hn]
  unfold QuotientZk.Deployed.ivPrefix
  rw [Merkle.toBytes_toList]
  rfl

theorem logN_witness : (witnessLayout logRows).logN = 25 := rfl
theorem logN_wiring : (wiringLayout logRows).logN = 24 := rfl
theorem logN_quotient : (quotientLayout logRows).logN = 28 := rfl

/-- The witness opening's prefix. -/
theorem ivPrefix_witness :
    (QuotientZk.Deployed.witnessShape idWD).ivPrefix =
      openingLabel ++ u64Bytes openingVersion ++ digestBytes (witnessLayout logRows).id ++
        u64Bytes (witnessLayout logRows).logN ++ u64Bytes logInvRate :=
  ivPrefix_eq _ 25 logN_witness

/-- The wiring opening's prefix (any rows). -/
theorem ivPrefix_wiring (rows : List (List UInt8)) :
    (QuotientZk.Deployed.wiringShape idσD rows).ivPrefix =
      openingLabel ++ u64Bytes openingVersion ++ digestBytes (wiringLayout logRows).id ++
        u64Bytes (wiringLayout logRows).logN ++ u64Bytes logInvRate :=
  ivPrefix_eq _ 24 logN_wiring

/-- The quotient opening's prefix. -/
theorem ivPrefix_quotient :
    (QuotientZk.Deployed.quotientShape idQD).ivPrefix =
      openingLabel ++ u64Bytes openingVersion ++ digestBytes (quotientLayout logRows).id ++
        u64Bytes (quotientLayout logRows).logN ++ u64Bytes logInvRate :=
  ivPrefix_eq _ 28 logN_quotient

end PcsQuotient.EndToEnd.Core
