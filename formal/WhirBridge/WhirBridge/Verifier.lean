/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

`opening::verify` of `crates/quotient/src/opening.rs`, the whole of it (its transcript's start
included), over a hash and a permutation, and its Fiat-Shamir soundness in the random-oracle model
for the layouts the protocol opens, from `family_sound` (`Family.lean`, adapted from leanerVM
`mumbai`, https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0).
-/
import WhirBridge.Family
import WhirBridge.Layouts

/-!
# `opening::verify` and its soundness

`openingVerifyWithHash H F L R root claims π` is `opening::verify(layout, root, claims, proof)`
(`opening.rs:782-892`) with Keccak-256 `H` and Keccak-f[1600] `F` in any monad, step by step:

1. reject unless there is a claim and every claim's point has the table's `vars` coordinates;
2. the IV `H(prefix(L) ‖ claims)` (`iv`, `opening.rs:635-645`; `openingPrefix`: `LABEL`, `VERSION = 2`,
   the layout's id, `log_n`, the rate, 76 bytes; the claims as `claimsBytes`), the sponge
   `F(IV ‖ 0 ‖ 0)` (`Transcript::new(proof, iv, PUBLIC_DIGEST = 0, true)`);
3. reject unless the proof's first two scalars encode the expected root (`opening.rs:797-800`);
4. the program `ourProg`: read those two scalars as the commitment (absorbed), then `Layout.check`
   (the batching challenge, the target, the weight closure, `verify_whir`), accepting when it
   accepts and the proof is read whole.

`Test/Check.lean` runs it with the deployed Keccak on proofs of the Rust prover.

**`openingVerify_imp`**: acceptance by ours implies acceptance by the proven program, `variantProg`
from the seeding `famSeed (openingPrefix L R)`, with the root read from the proof: the root check
only rejects more. **`opening_sound`**: for every valid layout at an admissible shape, an
adversary of at most `QA` queries to the two random oracles that outputs a root, claims on the
layout and a proof makes `opening::verify` accept while **every candidate table** of the word
extracted for that root violates one of the claims with probability at most

`(QA + 10122) · (2^-128 + 5 (QA + 10122) / 2^256)`,

at most `2^-63` for `QA ≤ 2^64` (`opening_bound_le`). **`ours_sound`**: that, for the witness,
wiring and quotient layouts at every supported size (`17 ≤ log_rows ≤ 22`).

The layout's id is a constant of the verifier: `openingPrefix` computes it with the deployed
Keccak-256 (mumbai's `keccak256`), not the oracle, so the theorem is about the verifier with the 76
bytes of its prefix fixed (the same function as the Rust, which computes them each time).
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The prefix (`opening.rs:608-708`) -/

/-- `LABEL` (`opening.rs:41`): the ASCII bytes of `pcs-quotient-opening`. -/
def label : Bytes :=
  [0x70, 0x63, 0x73, 0x2d, 0x71, 0x75, 0x6f, 0x74, 0x69, 0x65, 0x6e, 0x74, 0x2d, 0x6f, 0x70, 0x65,
    0x6e, 0x69, 0x6e, 0x67]

/-- `VERSION` (`opening.rs:48`). -/
def version : ℕ := 2

/-- An integer as 8 little-endian bytes (`(n as u64).to_le_bytes()`). -/
def u64 (n : ℕ) : Bytes := wordBytes n.toUInt64

/-- A lane's kind and block in the layout's encoding (`opening.rs:682-690`): `0` a block, `1` the
overflow lane, `2` a random lane. -/
def Lane.code : Lane → ℕ × ℕ
  | .block b => (0, b)
  | .overflow => (1, 0)
  | .random => (2, 0)

/-- An optional field (`opening.rs:675-678`): `0`, or `1` then the value. -/
def optBytes : Option ℕ → Bytes
  | none => u64 0
  | some v => u64 1 ++ u64 v

/-- The gadget's field (`opening.rs:694-707`): `0` in a public layout; in a hidden one of pieces
`2^s`, `GADGET`, then each pattern's number of lanes, its lanes and its three entries. -/
def gadgetBytes : Option ℕ → Bytes
  | none => u64 0
  | some s => u64 gadget ++ (List.range 3).flatMap fun g ↦
      u64 (gadgetLanes g).length ++ (gadgetLanes g).flatMap u64 ++
        (List.range 3).flatMap fun i ↦ u64 (gadgetEntry s g i)

/-- `encode_layout` (`opening.rs:667-708`): every field of the layout, then the gadget. -/
def encodeLayout (L : Layout) : Bytes :=
  u64 L.vars ++ u64 L.logN ++ u64 L.lanes.length ++
    L.lanes.flatMap (fun l ↦ u64 l.code.1 ++ u64 l.code.2) ++ optBytes L.logPiece ++
    u64 L.pieces.length ++ L.pieces.flatMap u64 ++ gadgetBytes L.logPiece

/-- `layout_id` (`opening.rs:661-665`): Keccak-256 of the encoding, its 32 bytes. -/
def layoutId (L : Layout) : Bytes := digestBytes (keccak256 (encodeLayout L))

/-- **`prefix`** (`opening.rs:616-626`): `LABEL`, `VERSION`, the layout's id, `log_n` and the
rate, in fixed-width fields. -/
def openingPrefix (L : Layout) (R : ℕ) : Bytes :=
  label ++ u64 version ++ layoutId L ++ u64 L.logN ++ u64 R

theorem openingPrefix_length (L : Layout) (R : ℕ) : (openingPrefix L R).length = 76 := by
  simp [openingPrefix, u64, wordBytes, layoutId, digestBytes, label]

/-- `PUBLIC_DIGEST` (`opening.rs:648`): zero. -/
def publicDigest : Digest := #v[0, 0, 0, 0]

theorem publicDigest_eq : publicDigest = default := rfl

/-! ## The verifier -/

/-- The program past the transcript's start: the stack's root read as commitment `0` (the proof's
first two scalars, absorbed), the opening check, then accept. -/
def ourProg (L : Layout) (R : ℕ) (claims : List Claim) : Prog Bool := do
  commitStack L.logN R
  L.check R claims
  return true

theorem ourProg_eq (L : Layout) (R : ℕ) (claims : List Claim) :
    ourProg L R claims = variantProg L.stacking R claims := by
  simp only [ourProg, variantProg, Layout.check_eq]
  rfl

section Run

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **`opening::verify`** (`opening.rs:782-892`) over a hash `H` and a permutation `F`: no claim,
or a point of the wrong length, is rejected first (`opening.rs:792-794`). -/
def openingVerifyWithHash (L : Layout) (R : ℕ) (root : Digest) (claims : List Claim)
    (π : Proof) : m Bool :=
  if claims.isEmpty = false ∧ ∀ c ∈ claims, c.point.length = L.vars then do
    let iv ← H (openingPrefix L R ++ claimsBytes claims)
    let seed ← F (seedInput iv publicDigest)
    if rootOf π = some root then runProofWithHash H F (ourProg L R claims) seed π
    else pure false
  else pure false

end Run

/-- **Acceptance by ours implies acceptance by the proven program**: with the answers `H` and `F`,
if `opening::verify` accepts, the proof's first two scalars encode the expected root and the
seeded verifier of `family_sound` (`famSeed` of the prefix, `variantProg` reading the root from
the proof) accepts. -/
theorem openingVerify_imp {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState}
    {L : Layout} {R : ℕ} {root : Digest} (x : Stmt L.stacking) {π : Proof}
    (h : openingVerifyWithHash H F L R root x.claims π = some true) :
    rootOf π = some root ∧
      LeanVM.Protocol.Compile.Rom.verify H F (famSeed (openingPrefix L R) x)
        (variantProg L.stacking R x.claims) π = some true := by
  unfold openingVerifyWithHash at h
  by_cases hne : x.claims.isEmpty = false
  swap
  · rw [if_neg fun h' ↦ hne h'.1] at h
    exact absurd h (by simp [pure])
  rw [if_pos ⟨hne, x.wide⟩] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨iv, hiv, seed, hseed, h⟩ := h
  split_ifs at h with hr
  swap
  · exact absurd h (by simp [pure])
  refine ⟨hr, ?_⟩
  simp only [LeanVM.Protocol.Compile.Rom.verify, Seed.run, Seed.hsRun, famSeed, bind,
    Option.bind_eq_some_iff]
  refine ⟨seed, ⟨[iv], ⟨iv, ?_, rfl⟩, ?_⟩, ?_⟩
  · simpa using hiv
  · simpa [publicDigest_eq] using hseed
  · rwa [← ourProg_eq]

/-! ## In the random-oracle model -/

/-- **`opening::verify` as an oracle computation** on an adversary's output: the expected root,
claims on the layout, and a proof. -/
def ourVerifier (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof) :
    OracleComp KeccakCalls Bool :=
  openingVerifyWithHash callKeccak256 callKeccakF1600 L R w.1.1 w.1.2.claims w.2

/-- The seed's computation. -/
def seedComp (pre : Bytes) (cs : List Claim) : OracleComp KeccakCalls KeccakState :=
  callKeccak256 (pre ++ claimsBytes cs) >>= fun iv ↦ callKeccakF1600 (seedInput iv default)

theorem ourVerifier_eq (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof) :
    ourVerifier L R w = if w.1.2.claims.isEmpty = false then
      (seedComp (openingPrefix L R) w.1.2.claims >>= fun seed ↦
        if rootOf w.2 = some w.1.1 then
          runProofWithHash callKeccak256 callKeccakF1600 (variantProg L.stacking R w.1.2.claims)
            seed w.2
        else pure false) else pure false := by
  rw [ourVerifier, openingVerifyWithHash]
  by_cases hne : w.1.2.claims.isEmpty = false
  · rw [if_pos ⟨hne, w.1.2.wide⟩, if_pos hne, seedComp, bind_assoc, ourProg_eq, publicDigest_eq]
  · rw [if_neg fun h' ↦ hne h'.1, if_neg hne]

theorem verifierFam_eq (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof) :
    verifierFam (famSeeds L.stacking (openingPrefix L R)) (famProgram L.stacking R) (w.1.2, w.2) =
      seedComp (openingPrefix L R) w.1.2.claims >>= fun seed ↦
        runProofWithHash callKeccak256 callKeccakF1600 (variantProg L.stacking R w.1.2.claims)
          seed w.2 := by
  rw [verifierFam_fam]
  simp only [verifierComp, LeanVM.Protocol.Compile.Rom.verify, Seed.run, Seed.hsRun, famSeed,
    seedComp, bind_assoc, pure_bind, List.nil_append, List.getD_cons_zero]

/-- **A verifier that rejects more**: if `V₁` rejects when `c₀` fails, and otherwise is `V₂` after
a common first step when `c` holds and rejects after it when `c` fails, then `V₁` accepting while
`bad₁` holds is at most as likely as `V₂` accepting while `bad₂` holds, for `bad₁` implying `bad₂`
where `c₀` and `c` hold. -/
theorem romExperiment_le_of_reject {α β : Type} (A : OracleComp KeccakCalls α)
    (S : α → OracleComp KeccakCalls β) (K : α → β → OracleComp KeccakCalls Bool)
    (c₀ c : α → Prop) [DecidablePred c₀] [DecidablePred c]
    (bad₁ bad₂ : α → KeccakCalls.QueryCache → Prop)
    (himp : ∀ a cache, c₀ a → c a → bad₁ a cache → bad₂ a cache) :
    Pr{let z ← romExperiment A (fun a ↦ if c₀ a then
        (S a >>= fun b ↦ if c a then K a b else pure false) else pure false)}[
        z.1.2 = true ∧ bad₁ z.1.1 z.2] ≤
      Pr{let z ← romExperiment A (fun a ↦ S a >>= K a)}[z.1.2 = true ∧ bad₂ z.1.1 z.2] := by
  rw [romExperiment_eq, romExperiment_eq]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p ↦ ?_
  rw [prEvent_map, prEvent_map]
  by_cases hc₀ : c₀ p.1
  swap
  · simp only [hc₀, ↓reduceIte]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hev ↦ ?_) bot_le
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr] at hev
    exact Bool.false_ne_true hev.1
  by_cases hc : c p.1
  · simp only [hc₀, hc, ↓reduceIte]
    exact prEvent_mono _ _ _ fun r hr ↦ ⟨hr.1, himp _ _ hc₀ hc hr.2⟩
  · simp only [hc₀, hc, ↓reduceIte]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hev ↦ ?_) bot_le
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨b, -, hr⟩ := hr
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr] at hev
    exact Bool.false_ne_true hev.1

/-- **The event**: every candidate of the word extracted for the expected root (mumbai's `extract`
from the oracle's answers, at level 0's shape) has a **table** violating one of the claims. The
claims only: the doom mumbai's specification starts from (`OpeningDoom`) counts a hidden layout's
gadget as one more stack claim, so it is "every candidate violates a claim or the gadget", which
this event implies (`FamDoomed`, `Layout.openingDoom_iff`). -/
def OpeningDoomed (L : Layout) (R : ℕ) (w : (Digest × Stmt L.stacking) × Proof)
    (cache : KeccakCalls.QueryCache) : Prop :=
  ∀ q ∈ Candidates L.logN R (code₀ L.logN R).thr
      (extract (fun x ↦ cache (.inl x)) w.1.1 (rootHeight L.logN R) (2 ^ laneFold)),
    ∃ cl ∈ w.1.2.claims, L.tableEval q cl.point ≠ cl.value

/-- The bound: `(QA + QV) · (2^-128 + 5 (QA + QV) / 2^256)`, `QV = 10122`. -/
noncomputable def openingBound (QA : ℕ) : ℝ≥0∞ :=
  ((QA + 10122 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((5 * (QA + 10122) : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- **Fiat-Shamir soundness of `opening::verify`** in the two-oracle random-oracle model, for every
valid layout at an admissible shape: an adversary of at most `QA` queries to Keccak-256 and
Keccak-f[1600] outputs a root, claims on the layout and a proof; the verifier accepts while every
candidate table of the word extracted for the root violates one of the claims with probability at
most `(QA + 10122) · (2^-128 + 5 (QA + 10122) / 2^256)`. -/
theorem opening_sound (L : Layout) (hL : L.Valid) {R : ℕ} (hw : Whir.Admissible L.logN R)
    (A : OracleComp KeccakCalls ((Digest × Stmt L.stacking) × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier L R)}[z.1.2 = true ∧ OpeningDoomed L R z.1.1 z.2] ≤
      openingBound QA := by
  set pre := openingPrefix L R
  set f : (Digest × Stmt L.stacking) × Proof → Stmt L.stacking × Proof := fun w ↦ (w.1.2, w.2)
  have hA' : IsTotalQueryBound (f <$> A) QA := (isQueryBound_map_iff A f QA _ _).mpr hA
  have hfam := family_sound (L := L.stacking) hw pre (f <$> A) QA hA'
  rw [romExperiment_map, prEvent_map] at hfam
  have hbound : (QA + variantQueries : ℕ) * (εWhir + failBound (famSeeds L.stacking pre)
      (QA + variantQueries)) = openingBound QA := by
    rw [variantQueries_eq, openingBound, failBound]
    simp [famSeeds, εWhir]
  rw [hbound] at hfam
  refine le_trans ?_ hfam
  have hV : (fun w ↦ verifierFam (famSeeds L.stacking pre) (famProgram L.stacking R) (f w)) =
      fun w ↦ seedComp pre w.1.2.claims >>= fun seed ↦
        runProofWithHash callKeccak256 callKeccakF1600 (variantProg L.stacking R w.1.2.claims)
          seed w.2 := funext fun w ↦ verifierFam_eq L R w
  have hO : ourVerifier L R = fun w ↦ if w.1.2.claims.isEmpty = false then
      (seedComp pre w.1.2.claims >>= fun seed ↦
        if rootOf w.2 = some w.1.1 then
          runProofWithHash callKeccak256 callKeccakF1600 (variantProg L.stacking R w.1.2.claims)
            seed w.2
        else pure false) else pure false := funext fun w ↦ ourVerifier_eq L R w
  rw [hV, hO]
  refine romExperiment_le_of_reject A (fun w ↦ seedComp pre w.1.2.claims)
    (fun w seed ↦ runProofWithHash callKeccak256 callKeccakF1600
      (variantProg L.stacking R w.1.2.claims) seed w.2)
    (fun w ↦ w.1.2.claims.isEmpty = false) (fun w ↦ rootOf w.2 = some w.1.1)
    (fun w cache ↦ OpeningDoomed L R w cache)
    (fun w cache ↦ FamDoomed L.stacking R (f w) cache) fun w cache _ hr hbad ↦ ?_
  intro r hr' q hq
  rw [hr'] at hr
  obtain rfl := (Option.some.inj hr).symm
  obtain ⟨cl, hcl, hne⟩ := hbad q hq
  exact ⟨cl, hcl, fun h ↦ hne ((L.holds_iff hL cl (w.1.2.wide cl hcl) q).1 h)⟩

/-- **The numbers**: against `2^64` queries the bound is at most `2^-63`. -/
theorem opening_bound_le {QA : ℕ} (hQ : QA ≤ 2 ^ 64) : openingBound QA ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  have h := bound_le (famSeeds (Layout.new 0 0 0 []).stacking []) rfl hQ
  rw [variantQueries_eq] at h
  refine le_of_eq_of_le ?_ h
  rw [openingBound, failBound]
  simp [famSeeds, εWhir]

/-- **Fiat-Shamir soundness of the protocol's three openings**, for every supported size
`17 ≤ log_rows ≤ 22`: the witness opening (hidden, `40` lanes), the wiring opening (public) and
the quotient opening (hidden, `63` lanes), each with its own prefix, at rate `1/2`. -/
theorem ours_sound (r : ℕ) (h1 : minLogRows ≤ r) (h2 : r ≤ maxLogRows) (L : Layout)
    (hLr : L = witnessLayout r ∨ L = wiringLayout r ∨ L = quotientLayout r)
    (A : OracleComp KeccakCalls ((Digest × Stmt L.stacking) × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier L logInvRate)}[
        z.1.2 = true ∧ OpeningDoomed L logInvRate z.1.1 z.2] ≤ openingBound QA := by
  have hv := layouts_valid r h1 h2
  have hok := layouts_ok r h1 h2
  rcases hLr with rfl | rfl | rfl
  · exact opening_sound _ hv.1 hok.1 A QA hA
  · exact opening_sound _ hv.2.1 hok.2.1 A QA hA
  · exact opening_sound _ hv.2.2 hok.2.2 A QA hA

end WhirBridge
