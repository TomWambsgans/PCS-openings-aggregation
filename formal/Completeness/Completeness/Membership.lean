-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): Keccak-256 (`Statement/Keccak.lean`, `keccak256`, `Digest.toBytes`,
-- `digestBytes`), the fields `K`, `E` (`Statement/Field.lean`).
import Completeness.Chain
import QuotientSecurity.DeployedHonest
import QuotientSecurity.DeployedConcrete
import QuotientSecurity.DeployedBasis

/-!
# The deployed circuit: completeness with no circuit or field hypothesis

`MembershipCircuit` (`Circuit.lean`) is the interface the end theorems took for the circuit. Here
it is built from F0b's deployed circuit (`QuotientSecurity.deployed`, `formal/Circuit`), and the
end theorems are instantiated with it, with the deployed σ, `coordinate_weight`'s weights over
`F192` (F0c) and a Cantor basis of `K`:

* **the secret** (`Secret.toPcs`): this file's `Secret` (`x`, siblings as `32` bytes, directions as
  `32` bits) as F0b's (`PcsCircuit.Secret`: lists and the directions' `u32`), always well-formed;
  its statement is F0b's (`Secret.toPcs_y`, `Secret.toPcs_root`: `pair` is F0b's `H` of the
  concatenation, both leanerVM's `keccak256`, and the path is folded the same way);
* **the assignment** (`deployedMembership.assign s`): `deployed` evaluated on
  `membership_inputs(s)` (`QuotientSecurity.deployedAssign`); it satisfies every gate, and its
  public bits are the statement's (`deployedAssign_publicBits`: F0b's `membership_public`, the
  bits of a computation holding a secret, applied to this one); words 4 to 7 are laid as
  `finish` lays them (`deployed_word4_one`, …);
* **the wiring** (`deployedSigma_keeps`): the deployed σ (`membership.sigma`, the Rust's, the one
  soundness's `soundness_membership_deployed_concrete` takes) keeps what each cell carries
  (`deployedSigma_cellSrc`), so the honest cells satisfy the relation on it;
* **the instance** (`deployedInstanceE`): soundness's `deployedInstance` with `beta()`'s Cantor
  basis (`QuotientSecurity.deployedBasis`, `F64 = K`'s, embedded in `E`: `hB` by definition; its
  `24` words checked by the kernel and determined by `beta()`'s rule, `deployedBasis_unique`), the
  deployed σ, `coordWeight F192.G F192.Y` (`coordinate_weight`, `rustCoordinateWeight_eq`);
  `instanceOfBasis BK` for any Cantor basis `BK` of `K`.

**`completeness_deployed_concrete`**: for every secret and masks, one set `Bad` of triples
`(α, β, t)`, at most a `(17 · 2^24 + 8) / 2^192 < 2^-163` fraction, such that for every
transcript, hash function, permutation and padding, the honest proof (when the openings' proofs
of work succeed) is accepted by the deployed verifier on the deployed instance unless the run's
`(α, β, t)` is in `Bad`. **`completeness_deployed_keccak`**: the same on `transcript.rs`'s chain.
No hypothesis on the circuit, the wiring, the weights or the basis remains.
-/

set_option linter.unusedSectionVars false

open Finset
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Semantics
open scoped ENNReal

namespace Completeness

open QuotientSecurity Primitives

/-! ## The secret as F0b reads it -/

/-- The directions as a number, bit `i` the direction at level `i` (`statement::Secret`'s
`directions: u32`). -/
def dirBits (d : Fin 32 → Bool) : ℕ := PcsCircuit.bitsToNat (List.ofFn d)

theorem dirBits_testBit (d : Fin 32 → Bool) (i : Fin 32) : (dirBits d).testBit i = d i := by
  rw [dirBits, PcsCircuit.bitsToNat_testBit, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some]

/-- **The secret as F0b reads it** (`PcsCircuit.Secret`): `x` and the siblings as byte lists, the
directions as a number. -/
def Secret.toPcs (s : Secret) : PcsCircuit.Secret where
  x := List.ofFn s.x
  siblings := List.ofFn fun i => List.ofFn (s.siblings i)
  directions := dirBits s.directions

theorem Secret.toPcs_sibling (s : Secret) (i : Fin 32) :
    s.toPcs.siblings.getD i [] = List.ofFn (s.siblings i) := by
  show (List.ofFn fun i => List.ofFn (s.siblings i)).getD i [] = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

theorem Secret.toPcs_direction (s : Secret) (i : Fin 32) :
    s.toPcs.directions.testBit i = s.directions i :=
  dirBits_testBit s.directions i

/-- It is well-formed: `x` and the siblings are `32` bytes. -/
theorem Secret.toPcs_wellFormed (s : Secret) : s.toPcs.WellFormed :=
  ⟨List.length_ofFn, fun i hi => by
    rw [s.toPcs_sibling ⟨i, hi⟩]
    exact List.length_ofFn⟩

theorem bytes32_ofFn (a : Fin 32 → UInt8) : bytes32 (List.ofFn a) = a := by
  funext i
  show (List.ofFn a).getD i 0 = a i
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

theorem ofFn_bytes32 {l : List UInt8} (hl : l.length = 32) : List.ofFn (bytes32 l) = l := by
  apply List.ext_getElem (by rw [List.length_ofFn, hl])
  intro n h1 h2
  rw [List.getElem_ofFn]
  show l.getD n 0 = l[n]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- **`pair` is F0b's `H` of the concatenation**, both leanerVM's `keccak256`, read as 32 bytes. -/
theorem bytes32_H (a b : Fin 32 → UInt8) :
    bytes32 (PcsCircuit.H (List.ofFn a ++ List.ofFn b)) = pair a b := by
  funext i
  have hl := PcsCircuit.digestBytes_length
    (LeanVM.Protocol.KeccakHash.keccak256 (List.ofFn a ++ List.ofFn b))
  unfold bytes32 PcsCircuit.H pair
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact i.isLt),
    Option.getD_some]
  simp [LeanVM.Protocol.Digest.toBytes]

/-- **`y` is F0b's.** -/
theorem Secret.toPcs_y (s : Secret) : bytes32 s.toPcs.y = s.statement.y := by
  show bytes32 (PcsCircuit.H (List.ofFn s.x ++ List.replicate 32 PcsCircuit.yPad)) =
    pair s.x fun _ => yPad
  rw [← bytes32_H, List.ofFn_const]
  rfl

/-- **The root is F0b's**: the same path, folded from the same leaf. -/
theorem Secret.toPcs_root (s : Secret) : bytes32 s.toPcs.root = s.statement.root := by
  have key : ∀ (L : List (Fin 32)) (a : List UInt8) (a' : Fin 32 → UInt8), a.length = 32 →
      bytes32 a = a' →
      bytes32 (L.foldl (fun node (i : Fin 32) => s.toPcs.up node i) a) =
        L.foldl (fun node i => if s.directions i then pair (s.siblings i) node
          else pair node (s.siblings i)) a' := by
    intro L
    induction L with
    | nil => intro a a' _ h; exact h
    | cons i L ih =>
      intro a a' hl h
      simp only [List.foldl_cons]
      refine ih _ _ (PcsCircuit.up_length _ _ _) ?_
      have ha : a = List.ofFn a' := by rw [← h, ofFn_bytes32 hl]
      unfold PcsCircuit.Secret.up
      rw [s.toPcs_direction i, s.toPcs_sibling i, ha]
      by_cases hd : s.directions i = true
      · rw [if_pos hd, if_pos hd]; exact bytes32_H _ _
      · rw [if_neg hd, if_neg hd]; exact bytes32_H _ _
  show bytes32 ((List.range PcsCircuit.depth).foldl s.toPcs.up
      (PcsCircuit.H (List.ofFn s.x ++ List.replicate 32 PcsCircuit.leafPad))) = s.root
  rw [show List.range PcsCircuit.depth = (List.finRange 32).map (fun i : Fin 32 => (i : ℕ)) from
    List.map_coe_finRange_eq_range.symm, List.foldl_map]
  refine key _ _ _ (PcsCircuit.H_length _) ?_
  rw [Secret.leaf, ← bytes32_H, List.ofFn_const]
  rfl

/-! ## The deployed circuit as F0b's interface -/

/-- **Keccak correctness, forward, for this file's secrets**: the public bits of the honest
assignment are the bits of the statement the secret proves. -/
theorem deployedAssign_publicBits (s : Secret) (J : Fin 4) (j : Fin 128) :
    deployed.pubBit (deployedAssign s.toPcs) (Fin.castLE (by norm_num) J) j =
      statementBit s.statement.y s.statement.root J j := by
  rw [deployedAssign_public s.toPcs s.toPcs_wellFormed J j, s.toPcs_y, s.toPcs_root]

/-- **F0b's deployed circuit as the interface `MembershipCircuit`**: `deployed`, the assignment
it computes from `membership_inputs` of a secret, which satisfies every gate and whose public bits
are the statement's, and the constants' words. -/
noncomputable def deployedMembership : MembershipCircuit where
  C := deployed
  assign s := deployedAssign s.toPcs
  satisfies s := deployedAssign_satisfies s.toPcs
  publicBits := deployedAssign_publicBits
  word4_one := deployed_word4_one
  word4 := deployed_word4
  word5 := deployed_word5
  word6 := deployed_word6
  word7 := deployed_word7

/-- **The deployed σ keeps what the deployed circuit's cells carry.** -/
theorem deployedSigma_keeps : WiringKeeps deployedSigma deployedMembership.C :=
  deployedSigma_cellSrc

/-- **The instance of a Cantor basis `BK` of `K`**: soundness's `deployedInstance` (the deployed σ,
`coordWeight F192.G F192.Y`, `coordinate_weight`'s weights) with `BK` embedded in `E`. -/
noncomputable def instanceOfBasis (BK : CantorBasis K (22 + 2)) : Instance E :=
  deployedInstance (BK.map (algebraMap K E))

/-- **The deployed instance over `E`**: `beta()`'s basis (`deployedBasis`, in `K = F64`), the
deployed σ, `coordinate_weight`'s weights; soundness's `deployedInstance` of the same basis. -/
noncomputable def deployedInstanceE : Instance E := instanceOfBasis deployedBasis

/-- Its basis is `beta()`'s, in `K` (`hB`). -/
theorem deployedInstanceE_basis (k : ℕ) :
    deployedInstanceE.basis.β k = algebraMap K E (deployedBasis.β k) := rfl

/-- Its wiring is the deployed σ (`hw`), its weights `coordinate_weight`'s (`hc`). -/
theorem deployedInstanceE_wiring : deployedInstanceE.wiring = deployedSigma := rfl

theorem deployedInstanceE_c : deployedInstanceE.c = coordWeight F192.G F192.Y := rfl

/-- **The honest cells satisfy the relation on the deployed instance**, for the statement's
words, which are `statement::halves` then `1, 0, 0, 0` (`statementWords_G_Y`). -/
theorem honest_relation_deployed (s : Secret) :
    deployedInstanceE.Relation (statementWords F192.G F192.Y s.statement.y s.statement.root)
      (deployed.cellsOfBits (deployedAssign s.toPcs)) :=
  honest_relation deployedMembership deployedInstanceE rfl deployedSigma_keeps s

open Classical in
/-- **End-to-end completeness for any Cantor basis of `K`**: `completeness_end_bad_set` on
`instanceOfBasis BK` with `deployedMembership`, every hypothesis discharged. -/
theorem completeness_deployed_basis (BK : CantorBasis K (22 + 2)) (s : Secret)
    (m : Fin 4 → Fin 3 → K) :
    ∃ Bad : Finset (E × E × E),
      (Bad.card : ℝ≥0∞) / (Fintype.card (E × E × E) : ℝ≥0∞) ≤ (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 ∧
      ∀ (tr : Transcript) (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
        (padW padQ : ℕ → ℕ → K) (π : DeployedProof),
        honestProve (instanceOfBasis BK) F192.G F192.Y BK deployedMembership tr
          witnessOpening.toSystem quotientOpening.toSystem H F fuel s m padW padQ = some π →
        ((honestRun (instanceOfBasis BK) BK deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).α,
          (honestRun (instanceOfBasis BK) BK deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).β,
          (honestRun (instanceOfBasis BK) BK deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).t) ∉ Bad →
        deployedVerify (instanceOfBasis BK) F192.G F192.Y tr wiringOpening
          witnessOpening.toSystem quotientOpening.toSystem H F
          (wiringOpening.root H (wiringStack (instanceOfBasis BK) BK)) s.statement π :=
  completeness_end_bad_set (instanceOfBasis BK) BK (fun _ => rfl) deployedMembership rfl
    deployedSigma_keeps s m

open Classical in
/-- **End-to-end completeness of the deployed membership proof, no circuit or field hypothesis.**
On the deployed instance (the deployed circuit and σ, `coordinate_weight`'s weights over `F192`,
`beta()`'s Cantor basis), with F0b's honest assignment (`deployed` evaluated on
`membership_inputs` of the secret): for each witness (secret and masks) one set `Bad` of triples
`(α, β, t)`, at most a `(17 · 2^24 + 8) / 2^192 < 2^-163` fraction, such that for every
transcript, hash function, permutation and padding, the honest proof, when the openings' proofs
of work succeed, is accepted by the deployed verifier unless the run's `(α, β, t)` is in `Bad`. -/
theorem completeness_deployed_concrete (s : Secret) (m : Fin 4 → Fin 3 → K) :
    ∃ Bad : Finset (E × E × E),
      (Bad.card : ℝ≥0∞) / (Fintype.card (E × E × E) : ℝ≥0∞) ≤ (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 ∧
      ∀ (tr : Transcript) (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
        (padW padQ : ℕ → ℕ → K) (π : DeployedProof),
        honestProve deployedInstanceE F192.G F192.Y deployedBasis deployedMembership tr
          witnessOpening.toSystem quotientOpening.toSystem H F fuel s m padW padQ = some π →
        ((honestRun deployedInstanceE deployedBasis deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).α,
          (honestRun deployedInstanceE deployedBasis deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).β,
          (honestRun deployedInstanceE deployedBasis deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).t) ∉ Bad →
        deployedVerify deployedInstanceE F192.G F192.Y tr wiringOpening witnessOpening.toSystem
          quotientOpening.toSystem H F
          (wiringOpening.root H (wiringStack deployedInstanceE deployedBasis)) s.statement π :=
  completeness_deployed_basis deployedBasis s m

/-- **`transcript.rs`'s chain on the deployed instance**: `keccakTranscript` over `H`, the
circuit's commitment the honest wiring root. -/
noncomputable def deployedChain (H : Bytes → Digest) (limbs : E ≃ QuotientRpm.Limbs) :
    Transcript :=
  keccakTranscript H limbs (wiringOpening.root H (wiringStack deployedInstanceE deployedBasis))

open Classical in
/-- **The same on the deployed chain** (`transcript.rs`, `keccakTranscript`): the circuit's
commitment the honest wiring root, the challenges `H` (Keccak-256 as deployed) of the transcript,
for every reading `limbs` of a challenge's 192 bits as `E`. -/
theorem completeness_deployed_keccak (s : Secret) (m : Fin 4 → Fin 3 → K) :
    ∃ Bad : Finset (E × E × E),
      (Bad.card : ℝ≥0∞) / (Fintype.card (E × E × E) : ℝ≥0∞) ≤ (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 ∧
      ∀ (limbs : E ≃ QuotientRpm.Limbs) (H : Bytes → Digest) (F : KeccakState → KeccakState)
        (fuel : ℕ) (padW padQ : ℕ → ℕ → K) (π : DeployedProof),
        honestProve deployedInstanceE F192.G F192.Y deployedBasis deployedMembership
          (deployedChain H limbs) witnessOpening.toSystem quotientOpening.toSystem H F fuel s m
          padW padQ = some π →
        ((honestRun deployedInstanceE deployedBasis deployedMembership (deployedChain H limbs)
            witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).α,
          (honestRun deployedInstanceE deployedBasis deployedMembership (deployedChain H limbs)
            witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).β,
          (honestRun deployedInstanceE deployedBasis deployedMembership (deployedChain H limbs)
            witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).t) ∉ Bad →
        deployedVerify deployedInstanceE F192.G F192.Y (deployedChain H limbs) wiringOpening
          witnessOpening.toSystem quotientOpening.toSystem H F
          (wiringOpening.root H (wiringStack deployedInstanceE deployedBasis)) s.statement π := by
  obtain ⟨Bad, hcard, hall⟩ := completeness_deployed_concrete s m
  exact ⟨Bad, hcard, fun limbs H F fuel padW padQ π hπ hnot =>
    hall _ H F fuel padW padQ π hπ hnot⟩

open Classical in
/-- **For any instance with the deployed σ**, `coordinate_weight`'s weights and a basis in `K`:
`completeness_end_bad_set` with `deployedMembership`, `hw` discharged. -/
theorem completeness_deployed_sigma (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) {x Y : E} (hc : I.c = coordWeight x Y)
    (hw : I.wiring = deployedSigma) (s : Secret) (m : Fin 4 → Fin 3 → K) :
    ∃ Bad : Finset (E × E × E),
      (Bad.card : ℝ≥0∞) / (Fintype.card (E × E × E) : ℝ≥0∞) ≤ (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 ∧
      ∀ (tr : Transcript) (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
        (padW padQ : ℕ → ℕ → K) (π : DeployedProof),
        honestProve I x Y BK deployedMembership tr
          witnessOpening.toSystem quotientOpening.toSystem H F fuel s m padW padQ = some π →
        ((honestRun I BK deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).α,
          (honestRun I BK deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).β,
          (honestRun I BK deployedMembership tr witnessOpening.toSystem
            quotientOpening.toSystem H s m padW padQ).t) ∉ Bad →
        deployedVerify I x Y tr wiringOpening witnessOpening.toSystem
          quotientOpening.toSystem H F (wiringOpening.root H (wiringStack I BK))
          s.statement π :=
  completeness_end_bad_set I BK hB deployedMembership hc (hw ▸ deployedSigma_keeps) s m

end Completeness
