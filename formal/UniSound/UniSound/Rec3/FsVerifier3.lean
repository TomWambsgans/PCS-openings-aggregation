-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsVerifier.lean`
-- (`uniVerifierBridge_of_walk`) for π1-rec3's verifier, `formal/UniStatement/UniStatement/Rec.lean`'s
-- `verifyWithFs … .rec3 true` (the loop over the openings, then no matrices' calls).
import UniSound.Rec3.FsWalk3
import UniSound.FsVerifier

/-!
# π1-rec3's verifier bridge from the walk

**`uniVerifierBridge3_of_walk`**: `UniVerifierBridge3` from the walk's two halves (`UniWalk3`, `UniWalkReject3`)
and `UniOutRoots3`, as `FsVerifier.lean`'s:

* a stream of another length is rejected by the walk; on a stream of π1-rec3's length the walk is the chain over
  Keccak-256, the same chain the composed verifier runs first;
* per challenges: if `uAccB3` is `false` the Statement rejects; else its result is `uOut3`, and the rest of the
  Statement's verifier (`restR3`: `FsVerifier.lean`'s loop `stepR` over the result's openings, unchanged, then
  `matR3`: **with the walk, no matrices' claim**, any claim rejects) accepts only on a result of π1-rec3's shape
  (`GoodR3`: three point claims without a bit slice on `C1`, `C2`, the setup, each of its layout word's
  variables, and no matrices' claim: `restR3_good`); on such a result it is the **three** calls one after the
  other (`restR3_unroll`), each F2's `ourVerifierEarly` (`pcsOpen_eq_early`) on the composed openings' inputs,
  so it accepts at most as often as the three `ourVerifier`s all do, and its acceptance gives `uniCheck3`.

Decision: `matRW` transcribes `verifyWithFs`'s `match r.matrices, walk` for every `walk` (so that
`verifyWithFs_eq_restW` is `rfl` after `bind_map_left`), and `restR3` is the loop then `matRW` at `walk = true`
(`none` keeps the verdict, `some` rejects).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## The Statement's verifier after the run -/

section Rest

variable (shape : UniStatement.Shape) (roots : SetupRoots) (proof : UniProof)
variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The matrices' step at a Fiat–Shamir shape** (`verifyWithFs`' `match r.matrices, walk`, transcribed): without
the walk `A0`'s and `B0`'s calls, with it no claim keeps the verdict, and any other case rejects. -/
def matRW (r : Reduced) (walk : Bool) (ok : Bool) : m Bool :=
  match r.matrices, walk with
  | some mc, false => do
    let b ← pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 3 [])) roots.a0
      [⟨mc.point, mc.a⟩] proof.a0
    let b' ← pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 4 [])) roots.b0
      [⟨mc.point, mc.b⟩] proof.b0
    pure (ok && b && b')
  | none, true => pure ok
  | _, _ => pure false

/-- **π1-rec3's matrices' step** (`matRW` at `walk = true`): no claim keeps the verdict, a claim rejects. -/
abbrev matR3 (r : Reduced) (ok : Bool) : m Bool := matRW shape roots proof F r true ok

/-- **The Statement's π1-rec3 verifier after the run**, on its result: the loop, then the matrices' step. -/
def restR3 (r : Reduced) : m Bool :=
  forIn r.openings (r.openings.map (·.1) == commitments) (stepR shape roots proof F r) >>=
    matR3 shape roots proof F r

/-- **The Statement's verifier at a Fiat–Shamir shape is the run, then the loop and `matRW`.** -/
theorem verifyWithFs_eq_restW [LawfulMonad m] (iv : List UInt8) (input : Vector UInt8 32) (fs : FsShape)
    (walk : Bool) :
    verifyWithFs F shape iv roots input proof fs walk =
      ((fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithFs F shape iv input.toList proof.stream (.flock flockMain) .point fs walk) >>= fun p =>
        if !p.1 then pure false else
          match p.2 with
          | .error _ => pure false
          | .ok r => forIn r.openings (r.openings.map (·.1) == commitments) (stepR shape roots proof F r) >>=
              matRW shape roots proof F r walk := by
  rw [bind_map_left]
  rfl

/-- **The Statement's π1-rec3 verifier is the run, then `restR3`** on an accepting run's result. -/
theorem verifyWithFs_eq_rest3 [LawfulMonad m] (iv : List UInt8) (input : Vector UInt8 32) :
    verifyWithFs F shape iv roots input proof .rec3 true =
      ((fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithFs F shape iv input.toList proof.stream (.flock flockMain) .point .rec3 true) >>= fun p =>
        if !p.1 then pure false else
          match p.2 with
          | .error _ => pure false
          | .ok r => restR3 shape roots proof F r :=
  verifyWithFs_eq_restW shape roots proof F iv input .rec3 true

end Rest

/-! ## What an accepting `restR3` needs -/

section Support

variable (shape : UniStatement.Shape) (roots : SetupRoots) (proof : UniProof)
variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (F : KeccakState → OracleComp spec KeccakState)

/-- **An accepting matrices' step**: started from `ok`, on a result without matrices' claim. -/
theorem matR3_true (r : Reduced) (ok : Bool) :
    ∀ b ∈ support (matR3 shape roots proof F r ok), b = true → ok = true ∧ r.matrices = none := by
  intro b hb hbt
  unfold matR3 matRW at hb
  rcases h : r.matrices with _ | mc
  · rw [h] at hb
    rw [support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨hbt, rfl⟩
  · rw [h] at hb
    rw [support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact absurd hbt (by simp)

/-- **π1-rec3's result**: three point claims without a bit slice, on `C1`, `C2` and the setup, each of its layout
word's variables, and no matrices' claim. -/
def GoodR3 (r : Reduced) : Prop :=
  ∃ (p1 : List E) (v1 : E) (p2 : List E) (v2 : E) (p3 : List E) (v3 : E),
    r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)] ∧ r.matrices = none ∧
    p1.length = layoutWordVars ((layoutWords shape).getD 0 []) ∧
    p2.length = layoutWordVars ((layoutWords shape).getD 1 []) ∧
    p3.length = layoutWordVars ((layoutWords shape).getD 2 [])

/-- **`restR3` accepts only on π1-rec3's result.** -/
theorem restR3_good (r : Reduced) :
    ∀ b ∈ support (restR3 shape roots proof F r), b = true → GoodR3 shape r := by
  intro b hb hbt
  rw [restR3, mem_support_bind_iff] at hb
  obtain ⟨ok, hok, hb⟩ := hb
  obtain ⟨hokt, hmc⟩ := matR3_true shape roots proof F r ok b hb hbt
  subst hokt
  obtain ⟨hc, hall⟩ := forIn_stepR_true shape roots proof F r _ _ _ hok rfl
  rw [beq_iff_eq] at hc
  rcases hl : r.openings with _ | ⟨⟨c₁, o₁⟩, _ | ⟨⟨c₂, o₂⟩, _ | ⟨⟨c₃, o₃⟩, _ | ⟨_, _⟩⟩⟩⟩ <;>
    rw [hl] at hc hall <;> simp [commitments] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  obtain ⟨p1, v1, e1, l1⟩ := hall _ List.mem_cons_self
  obtain ⟨p2, v2, e2, l2⟩ := hall _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨p3, v3, e3, l3⟩ := hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self))
  simp only at e1 e2 e3
  subst e1 e2 e3
  exact ⟨p1, v1, p2, v2, p3, v3, hl, hmc, l1, l2, l3⟩

/-- **On π1-rec3's result, `restR3` is the three calls**, one after the other. -/
theorem restR3_unroll (r : Reduced) (p1 : List E) (v1 : E) (p2 : List E) (v2 : E) (p3 : List E)
    (v3 : E) (ho : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)]) (hm : r.matrices = none) :
    restR3 shape roots proof F r = seqAnd
      [pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 0 [])) (rootOf r.roots.1)
          [⟨p1, v1⟩] proof.c1,
        pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 1 [])) (rootOf r.roots.2)
          [⟨p2, v2⟩] proof.c2,
        pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 2 [])) roots.bytecode
          [⟨p3, v3⟩] proof.setup] true := by
  have hc : (r.openings.map (·.1) == commitments) = true := by
    rw [ho]
    rfl
  rw [restR3, hc, ho]
  simp only [List.forIn_cons, List.forIn_nil, stepR_point, bind_assoc, pure_bind,
    seqAnd]
  unfold matR3 matRW
  rw [hm]
  rfl

end Support

/-! ## The bridge -/

section Bridge

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)

theorem length_uRounds3 : (uRounds3 F3 nV np).length = F3.prog.rounds.length + 4 + np :=
  length_rec3Rounds _ _ _

theorem wellFormed3_of_good (r : Reduced) (p1 : List E) (v1 : E) (p2 : List E) (v2 : E)
    (p3 : List E) (v3 : E)
    (ho : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)]) (hm : r.matrices = none)
    (l1 : p1.length = wv D 0) (l2 : p2.length = wv D 1) (l3 : p3.length = wv D 2) :
    WellFormed3 D r := by
  refine ⟨by rw [ho]; rfl, ?_, ?_, ?_, hm⟩
  · simp [claimsOf, ho, l1]
  · simp [claimsOf, ho, l2]
  · simp [claimsOf, ho, l3]

end Bridge

/-- **π1-rec3's VERIFIER BRIDGE**, from the walk (`UniWalk3`, `UniWalkReject3`) and the chain program's roots
(`UniOutRoots3`). -/
theorem uniVerifierBridge3_of_walk (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ)
    (C : UniCode3 D F3 nV np) (hs : UniShapes D) (hW : UniWalk3 D F3 nV np C)
    (hR : UniWalkReject3 D F3 nV np) (hO : UniOutRoots3 D F3 nV np C) :
    UniVerifierBridge3 D F3 nV np C hs := by
  intro π s
  rw [verifyWithFs_eq_rest3]
  by_cases hlen : π.proof.stream.size = uLen3 F3 nV np
  swap
  · -- a stream of another length: the walk rejects
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun b hb => ?_) s)).trans zero_le
    rw [mem_support_bind_iff] at hb
    obtain ⟨p, hp, hb⟩ := hb
    rw [support_map] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    simp only [hR π hlen o ho, Bool.not_false, ↓reduceIte, support_pure,
      Set.mem_singleton_iff] at hb
    simp [hb]
  -- the walk is the chain; both sides run it first
  rw [hW Common.queryPermutation π hlen, bind_map_left, simulateQ_verU]
  refine mono_bind_supp _ _ _ _ _ _ (fun ch hch s => ?_) s
  obtain ⟨hfits, hlch⟩ := doneFits_of_mem_chain (uRounds3 F3 nV np) π ch _ hch
  dsimp only
  cases hacc : uAccB3 D F3 nV np C π ch
  · -- the walk's verdict rejects
    rw [ite_eq_left (show (!false) = true from rfl), Soundness.zero_pure _ false _ (by simp) s]
    exact zero_le
  rw [ite_eq_right (show ¬ ((!true) = true) by decide)]
  have hz : (C.prog (uSt3 F3 nV np π).1 (uSt3 F3 nV np π).2).ZerosVanish
      (uDone (uRounds3 F3 nV np) π ch) (uTail3 (uRounds3 F3 nV np) π) :=
    (@of_decide_eq_true _ (Classical.propDecidable _) hacc).2
  by_cases hg : GoodR3 D.shape (uOut3 D F3 nV np C π ch)
  swap
  · -- not π1-rec3's result: the Statement rejects
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun b hb hbt => ?_) s)).trans zero_le
    exact hg (restR3_good D.shape π.roots π.proof Common.queryPermutation _ b hb hbt)
  obtain ⟨p1, v1, p2, v2, p3, v3, ho, hm, l1, l2, l3⟩ := hg
  rw [← wv_eq] at l1 l2 l3
  have hcheck : uniCheck3 D F3 nV np C π ch :=
    ⟨hfits, hz, wellFormed3_of_good D _ p1 v1 p2 v2 p3 v3 ho hm l1 l2 l3⟩
  -- the claims
  have hx1 : (cl1_3 D F3 nV np C π ch).claims =
      [(⟨p1, v1⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl1_3, show claimsOf (uOut3 D F3 nV np C π ch) .c1 = [⟨p1, v1⟩] by simp [claimsOf, ho]]
    exact claims_uCl D 0 p1 v1 l1
  have hx2 : (cl2_3 D F3 nV np C π ch).claims =
      [(⟨p2, v2⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl2_3, show claimsOf (uOut3 D F3 nV np C π ch) .c2 = [⟨p2, v2⟩] by simp [claimsOf, ho]]
    exact claims_uCl D 1 p2 v2 l2
  have hx3 : (cl3_3 D F3 nV np C π ch).claims =
      [(⟨p3, v3⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl3_3, show claimsOf (uOut3 D F3 nV np C π ch) .setup = [⟨p3, v3⟩] by simp [claimsOf, ho]]
    exact claims_uCl D 2 p3 v3 l3
  -- the rounds' roots
  have hr1 : ofB (((msgK (uView (uRounds3 F3 nV np)) π 0).1).getD (Vector.replicate 32 0)) =
      rootOf (uOut3 D F3 nV np C π ch).roots.1 := by
    rw [hO π ch]
    exact root_at _ π ch 0 (by rw [length_uRounds3]; omega) hlch (by
      rw [rec3Rounds_zero])
  have hr2 : ofB (((msgK (uView (uRounds3 F3 nV np)) π (F3.prog.rounds.length + 1)).1).getD
      (Vector.replicate 32 0)) = rootOf (uOut3 D F3 nV np C π ch).roots.2 := by
    rw [hO π ch]
    exact root_at _ π ch _ (by rw [length_uRounds3]; omega) hlch (by
      rw [rec3Rounds_c2])
  -- the Statement's three calls, F2's early-stop openings
  rw [restR3_unroll D.shape π.roots π.proof Common.queryPermutation _ p1 v1 p2 v2 p3 v3 ho hm,
    ← wv_eq, ← wv_eq, ← wv_eq,
    pcsOpen_eq_early (wv D 0) (hs.lo 0 (by decide)) (hs.hi 0 (by decide)) _ _ _ hx1,
    pcsOpen_eq_early (wv D 1) (hs.lo 1 (by decide)) (hs.hi 1 (by decide)) _ _ _ hx2,
    pcsOpen_eq_early (wv D 2) (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _ _ _ hx3]
  -- the composed side's three openings
  unfold uOps3 uniOps3
  -- C1
  rw [seqAnd_cons, sim_opsRun_cons]
  refine early_le_rpm _ _ _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · exact Prod.ext (Prod.ext hr1 rfl) rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- C2
  rw [seqAnd_cons, sim_opsRun_cons]
  refine early_le_rpm _ _ _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · exact Prod.ext (Prod.ext hr2 rfl) rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- the setup
  rw [seqAnd_cons, sim_opsRun_cons]
  refine early_le_rpm _ _ _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · exact Prod.ext (Prod.ext (Soundness.ofB_toB_root _) rfl) rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- every opening accepted
  rw [seqAnd, sim_opsRun_nil, simulateQ_pure]
  refine Soundness.le_pure _ _ _ _ _ (fun _ => ⟨hcheck, fun k hk => ?_⟩) s
  have hk3 : k < 3 := hk
  interval_cases k <;> rfl

end UniSound

/-- info: 'UniSound.uniVerifierBridge3_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniVerifierBridge3_of_walk
