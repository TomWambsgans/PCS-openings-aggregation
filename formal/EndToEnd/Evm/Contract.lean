-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The calldata is `crates/evm/src/quotient.rs`'s `calldata`; the calls of `PCS_OPEN` are
-- `crates/evm/src/quotient.rs`'s `build` and `crates/evm/src/machine.rs`'s `pcs_open_input`.
import Evm.Formula
import Evm.PcsOpen
import Bridge.Verifier

/-!
# The contract is the statement's verifier

The deployed contract (`crates/evm`) is F5's recorded graph (`Implementation.run`, `accepts`) with the
deployed Keccak-256 (`keccakBytes`), the circuit's commitment read from storage (the setup root's 32
bytes, `Compose.toB ir`), on the calldata of a proof (`calldata`: the statement's 64 bytes, the two
roots, the five values, as `quotient.rs` writes them). Here, against the statement's verifier
`PcsQuotient.verifyWith` at `π = Keccak-f[1600]`:

* **`run_calldata`**: the contract reaches its three calls of `PCS_OPEN` exactly when
  `PcsQuotient.reduce` accepts the reduction, and then its calls are exactly `callsOf`: the witness
  table's root, layout and claim, the circuit's commitment, the wiring layout and claim, the quotient
  table's root, layout and two claims, of the statement's reduction — the same roots, layout ids,
  points and values, byte for byte (`openInput`);
* **`evm_accepts_iff_verifyWith`**: with `PCS_OPEN`'s semantics `pcsOpen` (the input read as the
  precompile reads it, then the statement's `PcsQuotient.opening` with the proof's opening of the
  table the layout names, `openingProofs`), the contract accepts exactly when
  `PcsQuotient.verifyWith` accepts;
* `verifyWith_of_calldata_none`: a proof with no calldata (a root's scalars naming no digest) is one
  the statement's verifier rejects.

The proof composes F5 (`graph_reaches_iff_F192`, `run_words_formula`: the graph's leaves are F4a's
chain on the calldata, its outputs `Formula`), the formulas (`Formula.lean`: `Formula` is
`Compose.Reduce.reduce` at the statement's constants), the bridge (`Bridge.reduceWith_eq`: the
statement's reduction is F4's chain `Compose.chainWith`, then `claimsAt`; `Bridge.claimsAt_eq_reduce`:
`claimsAt` is `Compose.Reduce.reduce`), and `chain_eq` here: F4's chain gives F5's leaves.
-/

set_option linter.unusedSectionVars false

namespace Evm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash QuotientRpm
open Implementation

local notation "C" => Bridge.statementConsts

/-! ## The deployed contract -/

/-- **The deployed Keccak-256 on bytes** (`KECCAK256`, F5's `H`): Keccak-f[1600]'s sponge, the
statement's `keccak256`, as 32 bytes. -/
def keccakBytes (l : List UInt8) : Bytes32 := Compose.toB (keccak256 l)

/-- **The calldata of a proof** (`quotient.rs`'s `calldata`, F5's `calldataOf`): the selector, the
statement's 64 bytes `y ‖ root`, the two roots (each the low limbs `c1, c0` of its two scalars,
big-endian), the four values and `next` (each its limbs `c2, c1, c0`, big-endian). A proof whose root
scalars name no digest (a top limb set) has none, and the statement's verifier rejects it
(`verifyWith_of_calldata_none`). -/
def calldata (stmt : PcsQuotient.Statement) (p : PcsQuotient.ReductionProof) : Option (List UInt8) :=
  match digestOfScalars p.witnessRoot, digestOfScalars p.quotientRoot with
  | some r₁, some r₂ =>
    some (calldataOf limbsEquiv (stmt.y ++ stmt.root) (Compose.toB r₁) (Compose.toB r₂)
      [p.values[0], p.values[1], p.values[2], p.values[3], p.next])
  | _, _ => none

/-- **The calls of `PCS_OPEN` of the statement's reduction**: the witness table's root, the witness
layout's id, its claim; the circuit's commitment `ir`, the wiring layout's id, its claim; the quotient
table's root, the quotient layout's id, its two claims. -/
def callsOf (ir : Digest) (r : PcsQuotient.Reduced) : List (List UInt8) :=
  [openInput r.witnessRoot (layoutId 1 22) [r.claims.witness],
    openInput ir (layoutId 2 22) [r.claims.wiring],
    openInput r.quotientRoot (layoutId 3 22) [r.claims.quotient, r.claims.sum]]

/-- **The block's opening proofs**: for a call naming the layout `id`, the opening `w`, `f` or `q`
of the table the id names (`1` the witness table, `2` the wiring table, `3` the quotient table). -/
def openingsOf (w f q : Compile.Proof) (id : ℕ) : Compile.Proof :=
  if id / 256 = 1 then w else if id / 256 = 2 then f else q

/-- **The block's opening proofs, as a proof carries them**: its three openings (`openingsOf`). -/
def openingProofs (proof : PcsQuotient.Proof) : ℕ → Compile.Proof :=
  openingsOf proof.witness proof.wiring proof.quotient

/-! ## F4's chain gives F5's leaves -/

/-- **F4's chain on a proof is F5's chain on its calldata**: the challenges `Compose.chainWith`
draws (over any hash, with the limbs `eLimbs`) are the leaves `modelVals` of the calldata. -/
theorem chain_eq {P : QuotientSecurity.Params E} {B : P.Bounds} (W : Wire P B)
    (hW : W.limbs = Soundness.eLimbs) (H : List UInt8 → Bytes32) (ir : Digest)
    (stmt : PcsQuotient.Statement) (p : PcsQuotient.ReductionProof) (r₁ r₂ : Digest) :
    Compose.chainWith (m := Id) W H (Bridge.rootProofIr ir stmt p r₁ r₂) =
      pure ⟨(modelVals H (Compose.toB ir) (stmt.y ++ stmt.root) (Compose.toB r₁) (Compose.toB r₂)
          limbsEquiv p.values[0] p.values[1] p.values[2] p.values[3] p.next).α,
        (modelVals H (Compose.toB ir) (stmt.y ++ stmt.root) (Compose.toB r₁) (Compose.toB r₂)
          limbsEquiv p.values[0] p.values[1] p.values[2] p.values[3] p.next).β,
        (modelVals H (Compose.toB ir) (stmt.y ++ stmt.root) (Compose.toB r₁) (Compose.toB r₂)
          limbsEquiv p.values[0] p.values[1] p.values[2] p.values[3] p.next).γ,
        (modelVals H (Compose.toB ir) (stmt.y ++ stmt.root) (Compose.toB r₁) (Compose.toB r₂)
          limbsEquiv p.values[0] p.values[1] p.values[2] p.values[3] p.next).t,
        (modelVals H (Compose.toB ir) (stmt.y ++ stmt.root) (Compose.toB r₁) (Compose.toB r₂)
          limbsEquiv p.values[0] p.values[1] p.values[2] p.values[3] p.next).ρ⟩ := by
  have hc : ∀ st, W.chal st = limbsEquiv.symm (stateLimbs st) := fun st => by
    rw [Wire.chal, hW, ← limbsEquiv_eq_eLimbs]
  have hw : ∀ x, W.word x = scalarWord (limbsEquiv x) := fun x => by
    rw [Wire.word, hW, ← limbsEquiv_eq_eLimbs]
  simp only [Compose.chainWith, Bridge.rootProofIr, Wire.afterRoot, Wire.afterValues,
    Wire.valueWords, hc, hw, modelVals, st0, st1, st2, st3, st4, st5, Compose.labelOf,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-! ## The statement's reduction is F5's formulas -/

section Reduce

variable (ir : Digest) (stmt : PcsQuotient.Statement) (p : PcsQuotient.ReductionProof)
  (r₁ r₂ : Digest)

local notation "LV" => modelVals keccakBytes (Compose.toB ir) (stmt.y ++ stmt.root) (Compose.toB r₁)
  (Compose.toB r₂) limbsEquiv p.values[0] p.values[1] p.values[2] p.values[3] p.next

/-- The wire the bridge reads the chain with (any with the limbs `eLimbs`). -/
noncomputable abbrev wire : Wire (Soundness.inst C Bridge.isCantor_statementConsts).params
    (Soundness.inst C Bridge.isCantor_statementConsts).bounds :=
  Soundness.deployedWire (Soundness.inst C Bridge.isCantor_statementConsts)

variable {r₁ r₂} (h₁ : digestOfScalars p.witnessRoot = some r₁)
  (h₂ : digestOfScalars p.quotientRoot = some r₂)

include h₁ h₂ in
/-- **The statement's reduction at Keccak-f[1600] is `Compose.Reduce.reduce` at the leaves of the
calldata** (`modelVals`), with the statement's constants and halves. -/
theorem reduce_eq : PcsQuotient.reduce 22 ir stmt p =
    (Compose.Reduce.reduce C 24 (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) (LV).α (LV).β
      (LV).γ (LV).t (fun i => p.values.get i) p.next (LV).ρ).map
      fun cl => (⟨r₁, r₂, Bridge.reducedTr cl⟩ : PcsQuotient.Reduced) := by
  unfold PcsQuotient.reduce
  rw [Bridge.reduceWith_eq _ wire rfl ir stmt p r₁ r₂ h₁ h₂, chain_eq wire rfl]
  simp only [map_pure, Id.run_pure]
  rw [Bridge.claimsAt_eq_reduce, Option.map_map]
  rfl

include h₁ h₂ in
/-- The claims of an accepted reduction have the layouts' variables: `25`, `24`, `30`, `30`. -/
theorem reduce_lengths {r : PcsQuotient.Reduced} (h : PcsQuotient.reduce 22 ir stmt p = some r) :
    r.claims.witness.point.length = 25 ∧ r.claims.wiring.point.length = 24 ∧
      r.claims.quotient.point.length = 30 ∧ r.claims.sum.point.length = 30 := by
  rw [reduce_eq ir stmt p h₁ h₂] at h
  obtain ⟨cl, hcl, rfl⟩ := Option.map_eq_some_iff.mp h
  exact Bridge.reduce_lengths hcl

end Reduce

/-! ## The calls -/

theorem rootWord_toB (d : Digest) : rootWord (Compose.toB d).toList = rootWordOf d := by
  have hle : ∀ a b : UInt64, leNat (wordBytes a ++ wordBytes b) = a.toNat + 2 ^ 64 * b.toNat := by
    intro a b
    rw [leNat, List.reverse_append, beNat_append, List.length_reverse, LeanVM.Rpm.wordBytes_len]
    have ha := beNat_be64 a
    have hb := beNat_be64 b
    rw [be64] at ha hb
    rw [ha, hb]
    norm_num
    ring
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [a, b, c, e], _ =>
    have hbytes : (Compose.toB ⟨⟨[a, b, c, e]⟩, rfl⟩).toList =
        (wordBytes a ++ wordBytes b) ++ (wordBytes c ++ wordBytes e) := by
      rw [Bridge.toB_toList]
      simp [digestBytes]
    have h16 : (wordBytes a ++ wordBytes b).length = 16 := by simp [LeanVM.Rpm.wordBytes_len]
    rw [rootWord, hbytes, List.take_left' h16, List.drop_left' h16, hle, hle, rootWordOf]
    rfl

theorem calls_three (A B D : List ℕ) (hA : A.length = 29) (hB : B.length = 28)
    (hD : D.length = 65) :
    calls (A ++ B ++ D) =
      [A.flatMap (beBytes 32), B.flatMap (beBytes 32), D.flatMap (beBytes 32)] := by
  unfold calls
  rw [show Emitted.runs = [29, 28, 65] from rfl]
  simp only [splitRuns, List.append_assoc, List.take_left' hA, List.drop_left' hA,
    List.take_left' hB, List.drop_left' hB, List.take_of_length_le (le_of_eq hD), List.map_cons,
    List.map_nil]

/-- **The words of F5's formulas are the calls of `reduce`'s claims**: on `reduce`'s claims (as F5's
words), the contract's words cut into its three calls are `callsOf`. -/
theorem calls_eq (ir r₁ r₂ : Digest) (cl : Compose.Reduce.Reduced)
    (h1 : cl.witness.point.length = 25) (h2 : cl.wiring.point.length = 24)
    (h3 : cl.quotient.point.length = 30) (h4 : cl.sum.point = Compose.Reduce.sumPoint 24) :
    calls ([rootWord (Compose.toB r₁).toList, 256 * 1 + 22, 1] ++
        (cl.witness.point ++ [cl.witness.value]).map (word limbsEquiv) ++
        [rootWord (Compose.toB ir).toList, 256 * 2 + 22, 1] ++
        (cl.wiring.point ++ [cl.wiring.value]).map (word limbsEquiv) ++
        [rootWord (Compose.toB r₂).toList, 256 * 3 + 22, 2] ++
        (cl.quotient.point ++ [cl.quotient.value]).map (word limbsEquiv) ++
        (Compose.Reduce.sumPoint 24).map (word limbsEquiv) ++ [word limbsEquiv cl.sum.value]) =
      callsOf ir ⟨r₁, r₂, Bridge.reducedTr cl⟩ := by
  have hw : word limbsEquiv = elementWord := funext fun _ => rfl
  have e : [rootWord (Compose.toB r₁).toList, 256 * 1 + 22, 1] ++
        (cl.witness.point ++ [cl.witness.value]).map (word limbsEquiv) ++
        [rootWord (Compose.toB ir).toList, 256 * 2 + 22, 1] ++
        (cl.wiring.point ++ [cl.wiring.value]).map (word limbsEquiv) ++
        [rootWord (Compose.toB r₂).toList, 256 * 3 + 22, 2] ++
        (cl.quotient.point ++ [cl.quotient.value]).map (word limbsEquiv) ++
        (Compose.Reduce.sumPoint 24).map (word limbsEquiv) ++ [word limbsEquiv cl.sum.value] =
      openWords r₁ (layoutId 1 22) [Bridge.claimOfW cl.witness] ++
        openWords ir (layoutId 2 22) [Bridge.claimOfW cl.wiring] ++
        openWords r₂ (layoutId 3 22) [Bridge.claimOfW cl.quotient, Bridge.claimOfW cl.sum] := by
    simp only [openWords, claimWords, layoutId, Bridge.claimOfW, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil, rootWord_toB, hw, h4,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append]
  rw [e, calls_three _ _ _ (by simp [openWords, claimWords, Bridge.claimOfW, h1])
    (by simp [openWords, claimWords, Bridge.claimOfW, h2])
    (by simp [openWords, claimWords, Bridge.claimOfW, h3, h4, Compose.Reduce.sumPoint])]
  rfl

section Run

variable (ir : Digest) (stmt : PcsQuotient.Statement) (p : PcsQuotient.ReductionProof)
  {r₁ r₂ : Digest} (h₁ : digestOfScalars p.witnessRoot = some r₁)
  (h₂ : digestOfScalars p.quotientRoot = some r₂)

local notation "LV" => modelVals keccakBytes (Compose.toB ir) (stmt.y ++ stmt.root) (Compose.toB r₁)
  (Compose.toB r₂) limbsEquiv p.values[0] p.values[1] p.values[2] p.values[3] p.next

local notation "CD" => calldataOf limbsEquiv (stmt.y ++ stmt.root) (Compose.toB r₁) (Compose.toB r₂)
  [p.values[0], p.values[1], p.values[2], p.values[3], p.next]

include h₁ h₂ in
/-- **The contract on a proof's calldata calls `PCS_OPEN` exactly as the statement's reduction
leaves its claims**: it reaches its calls exactly when `PcsQuotient.reduce` (at Keccak-f[1600], the
circuit's commitment `ir` stored as its 32 bytes) accepts, and its calls are then `callsOf` of the
reduction: the same root words, layout ids, claim points and values, byte for byte. -/
theorem run_calldata :
    (run keccakBytes (Compose.toB ir) CD).map calls =
      (PcsQuotient.reduce 22 ir stmt p).map (callsOf ir) := by
  have hs : (LV).s = Compose.Reduce.stmtHalves (stmt.y ++ stmt.root) := elem_halfOf stmt
  have ha : (LV).a = fun i => p.values.get i := by
    funext i
    fin_cases i <;> rfl
  have hreach := graph_reaches_iff_F192 keccakBytes (Compose.toB ir) (stmt.y ++ stmt.root)
    (Compose.toB r₁) (Compose.toB r₂) p.values[0] p.values[1] p.values[2] p.values[3] p.next
  have hn : (LV).next = p.next := rfl
  rw [check_eq, hn] at hreach
  rw [reduce_eq ir stmt p h₁ h₂, ← ha]
  unfold Compose.Reduce.reduce
  by_cases h0 : (Compose.Reduce.denominators C 24 (LV).α (LV).β (LV).t (LV).a p.next).prod = 0
  · rw [if_pos h0, Option.map_none, Option.map_none]
    rcases hr : run keccakBytes (Compose.toB ir) CD with _ | ws
    · rfl
    · exact absurd (hreach.mp (by rw [hr]; rfl)) (fun h => h h0)
  · rw [if_neg h0, Option.map_some, Option.map_some]
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (hreach.mpr h0)
    rw [hws, Option.map_some]
    refine congrArg some ?_
    obtain ⟨hW, hF, hQ, hS⟩ := formula_claims (LV) (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) hs
    rw [run_words_formula _ _ _ _ _ _ _ _ _ _ ws hws, hW, hF, hQ, hS, sumPointWords_eq]
    exact calls_eq ir r₁ r₂ _ (by simp [Compose.Reduce.witness_point_eq])
      (by simp [Compose.Reduce.wiring_point_eq]) (by simp [Compose.Reduce.quotient_point_eq])
      (Compose.Reduce.sum_point_eq ..)

end Run

/-! ## The verdicts -/

/-- **The statement's verifier at Keccak-f[1600]**: the reduction, then the three openings. -/
theorem verifyWith_eq (ir : Digest) (stmt : PcsQuotient.Statement) (proof : PcsQuotient.Proof) :
    Id.run (PcsQuotient.verifyWith (m := Id) (fun s ↦ pure (keccakF1600 s)) 22 ir stmt proof) =
      match PcsQuotient.reduce 22 ir stmt proof.reduction with
      | none => false
      | some r =>
        PcsQuotient.opening (PcsQuotient.witnessLayout 22) r.witnessRoot [r.claims.witness]
            proof.witness &&
          PcsQuotient.opening (PcsQuotient.wiringLayout 22) ir [r.claims.wiring] proof.wiring &&
          PcsQuotient.opening (PcsQuotient.quotientLayout 22) r.quotientRoot
            [r.claims.quotient, r.claims.sum] proof.quotient := by
  unfold PcsQuotient.verifyWith PcsQuotient.reduce PcsQuotient.opening
  simp only [Id.run_bind]
  cases (PcsQuotient.reduceWith (m := Id) (fun s ↦ pure (keccakF1600 s)) 22 ir stmt
    proof.reduction : Option PcsQuotient.Reduced) with
  | none => rfl
  | some r =>
    dsimp only [Id.run]
    generalize (PcsQuotient.openingWith (m := Id) (fun s ↦ pure (keccakF1600 s))
      (PcsQuotient.witnessLayout 22) r.witnessRoot [r.claims.witness] proof.witness : Bool) = b1
    generalize (PcsQuotient.openingWith (m := Id) (fun s ↦ pure (keccakF1600 s))
      (PcsQuotient.wiringLayout 22) ir [r.claims.wiring] proof.wiring : Bool) = b2
    cases b1 <;> cases b2 <;> rfl

theorem openingProofs_witness (proof : PcsQuotient.Proof) :
    openingProofs proof (layoutId 1 22) = proof.witness := by
  simp [openingProofs, openingsOf, layoutId]

theorem openingProofs_wiring (proof : PcsQuotient.Proof) :
    openingProofs proof (layoutId 2 22) = proof.wiring := by
  simp [openingProofs, openingsOf, layoutId]

theorem openingProofs_quotient (proof : PcsQuotient.Proof) :
    openingProofs proof (layoutId 3 22) = proof.quotient := by
  simp [openingProofs, openingsOf, layoutId]

/-- **`PCS_OPEN` on the calls of an accepted reduction is the statement's three openings.** -/
theorem all_callsOf (proof : PcsQuotient.Proof) (ir : Digest) (r : PcsQuotient.Reduced)
    (hl : r.claims.witness.point.length = 25 ∧ r.claims.wiring.point.length = 24 ∧
      r.claims.quotient.point.length = 30 ∧ r.claims.sum.point.length = 30) :
    (callsOf ir r).all (pcsOpen (openingProofs proof)) =
      (PcsQuotient.opening (PcsQuotient.witnessLayout 22) r.witnessRoot [r.claims.witness]
          proof.witness &&
        PcsQuotient.opening (PcsQuotient.wiringLayout 22) ir [r.claims.wiring] proof.wiring &&
        PcsQuotient.opening (PcsQuotient.quotientLayout 22) r.quotientRoot
          [r.claims.quotient, r.claims.sum] proof.quotient) := by
  obtain ⟨l1, l2, l3, l4⟩ := hl
  have v1 : (PcsQuotient.witnessLayout 22).vars = 25 := rfl
  have v2 : (PcsQuotient.wiringLayout 22).vars = 24 := rfl
  have v3 : (PcsQuotient.quotientLayout 22).vars = 30 := rfl
  simp only [callsOf, List.all_cons, List.all_nil, Bool.and_true]
  rw [pcsOpen_openInput _ (root := r.witnessRoot) (claims := [r.claims.witness]) layoutOf_witness
      (by simp) (by simp [v1, l1]) (by norm_num [layoutId]) (by norm_num),
    pcsOpen_openInput _ (root := ir) (claims := [r.claims.wiring]) layoutOf_wiring
      (by simp) (by simp [v2, l2]) (by norm_num [layoutId]) (by norm_num),
    pcsOpen_openInput _ (root := r.quotientRoot) (claims := [r.claims.quotient, r.claims.sum])
      layoutOf_quotient (by simp) (by simp [v3, l3, l4]) (by norm_num [layoutId]) (by norm_num),
    openingProofs_witness, openingProofs_wiring, openingProofs_quotient, Bool.and_assoc]

theorem calldata_eq_some {stmt : PcsQuotient.Statement} {p : PcsQuotient.ReductionProof}
    {cd : List UInt8} (h : calldata stmt p = some cd) :
    ∃ r₁ r₂, digestOfScalars p.witnessRoot = some r₁ ∧ digestOfScalars p.quotientRoot = some r₂ ∧
      cd = calldataOf limbsEquiv (stmt.y ++ stmt.root) (Compose.toB r₁) (Compose.toB r₂)
        [p.values[0], p.values[1], p.values[2], p.values[3], p.next] := by
  unfold calldata at h
  split at h
  · next r₁ r₂ h₁ h₂ => exact ⟨r₁, r₂, h₁, h₂, (Option.some.inj h).symm⟩
  · cases h

/-- **The contract's verdict is the statement's verifier's** (`Bool` equality): on the calldata of a
proof, with `PCS_OPEN` the opening check `pcsOpen` given the proof's three openings, the deployed
contract (F5's graph, the deployed Keccak-256, the circuit's commitment `ir` in storage) accepts
exactly when `PcsQuotient.verifyWith` at Keccak-f[1600] accepts. -/
theorem evm_accepts_eq_verifyWith (ir : Digest) (stmt : PcsQuotient.Statement)
    (proof : PcsQuotient.Proof) {cd : List UInt8} (hcd : calldata stmt proof.reduction = some cd) :
    accepts (pcsOpen (openingProofs proof)) keccakBytes (Compose.toB ir) cd =
      Id.run (PcsQuotient.verifyWith (m := Id) (fun s ↦ pure (keccakF1600 s)) 22 ir stmt proof) := by
  obtain ⟨r₁, r₂, h₁, h₂, rfl⟩ := calldata_eq_some hcd
  have hrun := run_calldata ir stmt proof.reduction h₁ h₂
  rw [verifyWith_eq]
  unfold accepts
  rcases hr : PcsQuotient.reduce 22 ir stmt proof.reduction with _ | r
  · rw [hr, Option.map_none] at hrun
    rw [Option.map_eq_none_iff.mp hrun]
  · rw [hr, Option.map_some] at hrun
    obtain ⟨ws, hws, hc⟩ := Option.map_eq_some_iff.mp hrun
    rw [hws]
    dsimp only
    rw [hc, all_callsOf proof ir r (reduce_lengths ir stmt proof.reduction h₁ h₂ hr)]

/-- **The EVM contract accepts exactly when `PcsQuotient.verifyWith` accepts** (at `π =
Keccak-f[1600]`, the deployed Keccak-256): on the calldata of a statement and proof (`calldata`), the
deployed contract — F5's recorded graph run on it (`Implementation.accepts`), its index root the
circuit's commitment `ir` (the setup root, from storage) — with `PCS_OPEN`'s semantics `pcsOpen` (the
input read as the precompile reads it, then `PcsQuotient.opening` with the proof's opening of the
table its layout names, `openingProofs`), accepts iff the statement's verifier accepts the proof. -/
theorem evm_accepts_iff_verifyWith (ir : Digest) (stmt : PcsQuotient.Statement)
    (proof : PcsQuotient.Proof) {cd : List UInt8} (hcd : calldata stmt proof.reduction = some cd) :
    accepts (pcsOpen (openingProofs proof)) keccakBytes (Compose.toB ir) cd = true ↔
      Id.run (PcsQuotient.verifyWith (m := Id) (fun s ↦ pure (keccakF1600 s)) 22 ir stmt proof) =
        true := by
  rw [evm_accepts_eq_verifyWith ir stmt proof hcd]

/-- The same with the statement's `PcsQuotient.verify` (`verifyWith` over Keccak-f[1600]). -/
theorem evm_accepts_iff_verify (ir : Digest) (stmt : PcsQuotient.Statement)
    (proof : PcsQuotient.Proof) {cd : List UInt8} (hcd : calldata stmt proof.reduction = some cd) :
    accepts (pcsOpen (openingProofs proof)) keccakBytes (Compose.toB ir) cd = true ↔
      PcsQuotient.verify 22 ir stmt proof = true :=
  evm_accepts_iff_verifyWith ir stmt proof hcd

/-- **A proof with no calldata is rejected**: if a root's scalars name no digest, the statement's
verifier rejects (so the contract, which cannot be sent the proof, loses nothing). -/
theorem verifyWith_of_calldata_none (ir : Digest) (stmt : PcsQuotient.Statement)
    (proof : PcsQuotient.Proof) (h : calldata stmt proof.reduction = none) :
    Id.run (PcsQuotient.verifyWith (m := Id) (fun s ↦ pure (keccakF1600 s)) 22 ir stmt proof) =
      false := by
  have hred : PcsQuotient.reduce 22 ir stmt proof.reduction = none := by
    unfold calldata at h
    unfold PcsQuotient.reduce PcsQuotient.reduceWith
    rcases hw : digestOfScalars proof.reduction.witnessRoot with _ | r₁
    · rfl
    · rcases hq : digestOfScalars proof.reduction.quotientRoot with _ | r₂
      · rfl
      · rw [hw, hq] at h
        cases h
  rw [verifyWith_eq, hred]

/-- **The contract reaches its calls exactly when the statement's reduction accepts.** -/
theorem evm_reaches_iff (ir : Digest) (stmt : PcsQuotient.Statement) (p : PcsQuotient.ReductionProof)
    {cd : List UInt8} (hcd : calldata stmt p = some cd) :
    (run keccakBytes (Compose.toB ir) cd).isSome ↔ (PcsQuotient.reduce 22 ir stmt p).isSome := by
  obtain ⟨r₁, r₂, h₁, h₂, rfl⟩ := calldata_eq_some hcd
  have h := congrArg Option.isSome (run_calldata ir stmt p h₁ h₂)
  simpa using h

/-- **The contract hands `PCS_OPEN` exactly the statement's claims**: when it reaches its calls,
they are `callsOf` of the statement's accepted reduction (roots, layout ids, points and values, byte
for byte). -/
theorem evm_calls (ir : Digest) (stmt : PcsQuotient.Statement) (p : PcsQuotient.ReductionProof)
    {cd : List UInt8} (hcd : calldata stmt p = some cd) {ws : List ℕ}
    (h : run keccakBytes (Compose.toB ir) cd = some ws) :
    ∃ r, PcsQuotient.reduce 22 ir stmt p = some r ∧ calls ws = callsOf ir r := by
  obtain ⟨r₁, r₂, h₁, h₂, rfl⟩ := calldata_eq_some hcd
  have hrun := run_calldata ir stmt p h₁ h₂
  rw [h, Option.map_some] at hrun
  obtain ⟨r, hr, hc⟩ := Option.map_eq_some_iff.mp hrun.symm
  exact ⟨r, hr, hc.symm⟩

end Evm
