/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

What leanerVM `mumbai`'s theorems (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0,
MIT OR Apache-2.0) do not cover of this repository's opening: its Fiat-Shamir transcript, stated
here precisely and not proved.
-/
import WhirBridge.Variant

/-!
# The gaps

## This repository's transcript

`opening::verify` (`crates/quotient/src/opening.rs:222-288`) seeds its duplex with
`(keccak256(LABEL), keccak256(root ‖ claims))` (`seed`, `opening.rs:151-161`) and hands the root
to `verify_whir` as an argument: the root is hashed into the seed and **never absorbed** into the
duplex. `openingVerifyWithHash` is that verifier over a hash `H` and a permutation `F` in any
monad (mumbai's `runWithHash`, with the root pre-loaded as commitment `0` of the run's state).

mumbai's random-oracle theorem (`Compile.Rom.romSound`, `lean_vm/LeanVM/Protocol/Compile/Rom/Sound.lean`)
does not apply to it as stated:

* its verifier is `runProofWithHash`, whose run starts with **no** commitment
  (`roots := []`, `lean_vm/LeanVM/Protocol/WithHash.lean`), every root being read from the proof by a
  `Prog.commit` node and absorbed as two scalars;
* its seed's root history may contain no commitment (`Compile.Rom.RootOk`: `commits h = []`,
  `lean_vm/LeanVM/Protocol/Compile/Rom/Decode.lean`), and its failure event recognises roots only
  where a permutation input absorbs them (`Compile.Rom.RootOf`, `pairRoot`, `straddleRoot`,
  `lean_vm/LeanVM/Protocol/Compile/Rom/Log.lean`), the extraction's stability (`extract_take_eq`,
  `Compile/Rom/Extract.lean`) being argued at that absorption.

`OpeningRomSound` states the theorem this repository needs, for an adversary that chooses the
root, the claims and the proof. What it would take:

1. **A root carried by the seed** (the generalisation of `romSound`): `Seeds` whose root history
   holds the statement's commitments, each `Ev.commit` with the word `extract`ed for its root;
   the run started from those roots; `Fail` extended by "a fresh hash answer is the root inside
   an earlier seeding hash input" (the seeding's `offs` already charge a fresh answer equal to a
   chunk of an earlier input: the root sits at offset `0` of `root ‖ claims`); and the final
   inequality (`Compile.Rom.final_ineq`, `Final.lean`) and the potential's step
   (`step_ineqH`, `Potential.lean`) re-proved with commitments at the root. The certificate is
   unchanged: `openingSpec` (proved here) is a specification from the root's doom.
   The seed itself is outside mumbai's `Seeds` too: its second hash answer,
   `keccak256(root ‖ claims)`, sits in the public-digest lanes, where `Seeds.refs` admits no hash
   answer (every answer must be the IV, lanes `0..3`, or inside a later hash input).
   *Or*, change the Rust: absorb the root as the opening's first two stream scalars and seed with
   `keccak256(pre ‖ claims)` alone (`pre`: `LABEL`, a version, the layout's id, `log_n`, the rate),
   a zero public digest; that is `variantProg`, and `variant_sound` (a fixed
   statement) and `family_sound` (claims chosen by the adversary, `Family.lean`) cover it, proved.
2. **An adversarially chosen statement** is covered for that shape: `family_sound` builds, as
   mumbai does for leanVM (`EndToEnd/Sound/Statements.lean`), the seedings naming the claims
   (`Seeds.inj`: `seed`'s encoding of the claims is injective for a fixed layout, every point of
   `vars` coordinates) and one program for all statements. `LABEL` is shared by the three
   openings and the layout is not in the seed: each verifier has its own fixed layout.
3. **The random-permutation model**: mumbai moves leanVM's theorem from two random oracles to one
   random permutation (`LeanVMRpm.lean`, `Common.keccak256_transfer2`, at `q²/2^508`); this bridge
   stops at the two-oracle model.
4. **Pruned Merkle paths and `placed`**: the Rust verifier reads pruned batches
   (`MerkleOpenings::Pruned`) whose level-0 rows leave out the zero lanes past `placed`; mumbai's
   `Proof` has one full path per query. The expansion (`PrunedMerklePaths::expand`,
   `crates/verifier/src/merkle.rs:79-146`) rebuilds the full leaves and paths and checks the
   same roots, so it only restricts what is accepted; it is not formalised (as for leanVM:
   `Statement/LeanVm.lean`, "Scope and trust").
5. **The Rust is the model**: `openingCheck` mirrors `opening::verify` and mumbai's `verifyWhir`
   transcribes the Python verifier at `c445e3d5`; that the vendored Rust `verify_whir` computes
   the same is test evidence (mumbai's `scripts/fuzz-verifier.py`; our vendored verifier is
   byte-identical to leanVM's at that commit), not proof. `Test/Check.lean` runs
   `openingVerifyWithHash` with the deployed Keccak on a Rust opening proof and accepts it.
6. **Composition with the reduction**: an accepted opening gives, except with the bound's
   probability, a candidate among the **at most `2^18`** of the Johnson list of the root's word
   (`candidates_bound` of mumbai) whose table satisfies **all** the opening's claims (one opening
   per commitment: the quotient table's two claims bind one table). There is no out-of-domain
   sample at level 0, so the candidate is not unique: the reduction's soundness, whose claims
   are drawn after the roots, must hold for each of the up to `2^18` candidate tables fixed by
   each root, a union bound that multiplies the reduction's per-candidate error by `2^18` (mumbai
   does the same for leanVM's phases: `L₀ · …` in `EndToEnd/Sound/Assemble.lean`). The three
   openings are separate transcripts; the reduction's analysis must read the words extracted
   when each root entered the reduction's transcript (`extract_take_eq`).
7. **Extraction from the adversary's queries only**: `variant_sound` (as mumbai's `romSound`)
   reads the extracted word off the final cache, the verifier's answers included; mumbai's step
   to an extractor reading only the adversary's transcript (`Sound.extractor_of_extracted`,
   `Sound.prEvent_logged2_root_le`, `lean_vm/LeanVM/Protocol/LeanVMSound.lean`, at `QV / 2^256`)
   is not taken here.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

/-- `LABEL` (`opening.rs:24`). -/
def label : Bytes := "pcs-quotient-opening".toUTF8.toList

/-- A scalar's bytes as `seed` writes them (`opening.rs:155-157`): its three limbs, little-endian. -/
def scalarBytes (x : E) : Bytes := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- The statement's bytes (`seed`, `opening.rs:151-161`): the root, then each claim's point and
value. -/
def statementBytes (root : Digest) (claims : List Claim) : Bytes :=
  digestBytes root ++ claims.flatMap fun c ↦ (c.point ++ [c.value]).flatMap scalarBytes

section Run

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **`opening::verify` compiled** over a hash `H` and a permutation `F`: the seed
`F(H(LABEL) ‖ H(root ‖ claims) ‖ 0)`, then `openingCheck` with the root as commitment `0` of the
run (never absorbed), accepting when the proof is read whole (`transcript.finish()`). -/
def openingVerifyWithHash (L : Layout) (R : ℕ) (root : Digest) (claims : List Claim)
    (π : Proof) : m Bool := do
  let iv ← H label
  let pd ← H (statementBytes root claims)
  let seed ← F (seedInput iv pd)
  match ← runWithHash H F ((openingCheck L R claims).bind fun _ ↦ Prog.ret true)
      ⟨⟨seed, []⟩, π.stream, π.openings, [(root, L.logN - laneFold + R, 2 ^ laneFold)]⟩ with
  | some (true, s) => pure (s.stream.isEmpty && s.openings.isEmpty)
  | _ => pure false

end Run

/-- **The theorem this repository's opening needs** (not proved: see the module docstring): an
adversary of at most `QA` queries to Keccak-256 and Keccak-f[1600] (random oracles) outputs a
root, claims and a proof; the verifier accepts while every candidate of the word extracted for the
root from the oracle's answers (mumbai's `extract`, at level 0's shape) has a table violating one
of the claims with probability at most `(QA + QV) · (ε + fail)`. With the missing pieces, `ε`
would be `2^-128` (`openingSpec`, `whirEps_le`) and `fail` a collision term of the form
`c · (QA + QV) / 2^256`. -/
def OpeningRomSound (L : Layout) (R : ℕ) (QV : ℕ) (ε fail : ℝ≥0∞) : Prop :=
  ∀ (A : OracleComp KeccakCalls ((Digest × List Claim) × Proof)) (QA : ℕ),
    IsTotalQueryBound A QA →
      Pr{let z ← romExperiment A fun w ↦
          openingVerifyWithHash callKeccak256 callKeccakF1600 L R w.1.1 w.1.2 w.2}[
        z.1.2 = true ∧
          ∀ q ∈ Candidates L.logN R (code₀ L.logN R).thr
              (extract (fun x ↦ z.2 (.inl x)) z.1.1.1.1 (L.logN - laneFold + R) (2 ^ laneFold)),
            ∃ c ∈ z.1.1.1.2, L.tableEval q c.point ≠ c.value] ≤
        (QA + QV : ℕ) * (ε + fail)

/-- The program `openingVerifyWithHash` runs is mumbai's stacked opening, after the length
check, then acceptance. -/
theorem openingVerify_program (L : Layout) (R : ℕ) (claims : List Claim) :
    (openingCheck L R claims).bind (fun _ ↦ Prog.ret true) =
      ((Prog.require (∀ c ∈ claims, c.point.length = L.vars)).bind fun _ ↦
        verifyStackedOpening L.logN R (stackClaims L claims)).bind fun _ ↦ Prog.ret true := by
  rw [openingCheck_eq]

/-- The blocks of our layouts are distinct, so `Layout.table` is the committed table: each entry
of a block from the one lane holding it. -/
theorem layouts_nodup : ∀ r, 13 ≤ r → r ≤ 22 →
    (witnessLayout r).blocks.Nodup ∧ (wiringLayout r).blocks.Nodup ∧
      (quotientLayout r).blocks.Nodup := by
  decide +kernel

end WhirBridge
