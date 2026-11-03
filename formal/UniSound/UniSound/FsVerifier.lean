-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows
-- `formal/EndToEnd/Soundness/EarlyStop.lean` (`es_le`, `early_le`, `mono_bind`, `zero_of_support`)
-- and `formal/EndToEnd/Bridge/Verifier.lean` (`verifyWith_eq_verifyES`, `openingWith_eq_ourVerifier'`)
-- of this repository; the Statement's verifier is `formal/UniStatement/UniStatement/Opening.lean`'s.
import UniSound.FsWalk
import Bridge.Verifier
import Soundness.EarlyStop

/-!
# The verifier bridge from the walk

**`uniVerifierBridge_of_walk`**: `UniVerifierBridge` (`FsCouple.lean`) from the walk's two halves
(`UniWalk`, `UniWalkReject`, `FsWalk.lean`) and `UniOutRoots`.

* **A stream of another length** is rejected by the walk (`UniWalkReject`), so the Statement accepts
  with probability `0` (`Soundness.zero_of_support`).
* **On a stream of the main line's length** the walk is the chain over Keccak-256 (`UniWalk` at the
  model's oracles, `F = Common.queryPermutation`), and the composed verifier's chain, its two calls
  answered over `π` (`keccakCallsOverQueryPermutation`), is the same chain (`simulateQ_verU`): both
  sides run it first (`mono_bind_supp`, on the chain's possible challenges only: they have the
  rounds' lengths, `doneFits_of_mem_chain`).
* **Per challenges**: if the walk's verdict `uAccB` is `false` the Statement rejects. Else its result
  is the chain program's (`uOut`), and the rest of the Statement's verifier (`restR`: the loop over
  the result's openings, `Flock`'s matrices) accepts only on a result of the main line's shape
  (`GoodR`: three point claims without a bit slice, on `C1`, `C2`, the setup, each of its layout
  word's variables, and `Flock`'s matrices' claim of `A0`'s and `B0`'s: `restR_good`, since
  `PcsQuotient.openingWith` rejects claims of another length before any query); on such a result
  it is the five calls one after the other, their verdicts and-ed (`restR_unroll`, `seqAnd`), each
  `PCS_OPEN` call F2's `ourVerifierEarly` on the plain layout (`pcsOpen_eq_early`, by
  `Bridge.openingWith_eq_ourVerifier'`), on the composed openings' inputs (the roots by
  `UniOutRoots` and the rounds' roots, `root_at`; the claims `cl1 … cl5`, `claims_uCl`), so it
  accepts at most as often as the five `ourVerifier`s all do (`early_le_rpm`, five times), and its
  acceptance gives `uniCheck` (`DoneFits` from the chain, `ZerosVanish` from `uAccB`, `WellFormed`
  from `GoodR`, `wellFormed_of_good`).

Decisions: `restR` transcribes `verifyWith`'s code after the run (its loop `stepR`, its matrices'
calls `matR`) so that the loop can be reasoned about; `verifyWith_eq_rest` is `rfl` after
`bind_map_left`. The comparison is made over the model's oracles directly (`early_le_rpm` is
`Soundness.early_le` with the two calls answered over `π`), not after moving both sides to the two
calls. No hypothesis beyond the theorem's: the statement holds as stated.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## Simulated computations -/

section Sim

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ : Type}
  (impl : QueryImpl spec (StateT σ ProbComp))

/-- **A comparison of continuations on the prefix's possible outputs survives a common simulated
prefix** (`Soundness.mono_bind` with the outputs restricted to the support). -/
theorem mono_bind_supp {α β γ : Type} (oa : OracleComp spec α) (k₁ : α → OracleComp spec β)
    (k₂ : α → OracleComp spec γ) (E₁ : β → Prop) (E₂ : γ → Prop)
    (h : ∀ x ∈ support oa, ∀ s, Pr{let y ← (simulateQ impl (k₁ x)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ impl (k₂ x)).run' s}[E₂ y]) (s : σ) :
    Pr{let y ← (simulateQ impl (oa >>= k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ impl (oa >>= k₂)).run' s}[E₂ y] := by
  rw [Soundness.run'_bind, Soundness.run'_bind]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp => h p.1 ?_ p.2
  refine support_simulateQ_run'_subset impl oa s ?_
  rw [StateT.run'_eq, support_map]
  exact ⟨p, hp, rfl⟩

end Sim

/-! ## The chain, its two calls answered over `π` -/

section Chain

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

theorem simulateQ_runM {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) : ∀ (y : List UInt8) (es : List (List UInt8)),
    simulateQ impl (runM hash256 y es) = runM (fun x => simulateQ impl (hash256 x)) y es
  | y, [] => by simp [runM]
  | y, e :: es => by simp [runM, simulateQ_runM impl _ es]

theorem simulateQ_hash256 (x : List UInt8) :
    simulateQ keccakCallsOverQueryPermutation (hash256 x) =
      toB <$> keccak256With Common.queryPermutation x := by
  rw [hash256, simulateQ_bind, Compile.Rom.simulateQ_queryH, map_eq_bind_pure_comp]
  simp only [simulateQ_pure]
  rfl

/-- **The composed verifier, its two calls answered over `π`**: the chain over Keccak-256 the sponge
over `π`, then the openings. -/
theorem simulateQ_verU {β : Type} (U : ChainSpecU E FSt) (view : UPf → FSt × List (RMsg E))
    (post : UPf → List (List E) → OracleComp KeccakCalls β) (π : UPf) :
    simulateQ keccakCallsOverQueryPermutation (verU U view post π) =
      U.chain (fun x => toB <$> keccak256With Common.queryPermutation x) (view π).1 (view π).2 >>=
        fun ch => simulateQ keccakCallsOverQueryPermutation (post π ch >>= fun b => pure (ch, b)) := by
  rw [verU, simulateQ_bind]
  congr 1
  rw [ChainSpecU.chain, ChainSpecU.chain, simulateQ_map, simulateQ_runM]
  simp only [simulateQ_hash256]

/-- A run of the chain returns one state per step and the seed. -/
theorem length_of_mem_runM (H : List UInt8 → OracleComp spec Bytes32) :
    ∀ (y : List UInt8) (es : List (List UInt8)), ∀ sts ∈ support (runM H y es),
      sts.length = es.length + 1
  | y, [], sts, h => by
    simp only [runM, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    rfl
  | y, e :: es, sts, h => by
    simp only [runM, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨_, -, rest, hrest, rfl⟩ := h
    simp [length_of_mem_runM H _ es rest hrest]

/-- The stream's messages and challenges grouped by the rounds complete the rounds. -/
theorem doneFits_zip (b : Array UInt8) : ∀ (o : ℕ) (rs : List RoundSpec) (l : List E),
    l.length = nSteps rs → DoneFits rs ((msgsAt b o rs).zip (groupK rs l))
  | _, [], _, _ => by simp [msgsAt, groupK, DoneFits]
  | o, r :: rs, l, hl => by
    simp only [nSteps] at hl
    simp only [msgsAt, groupK, List.zip_cons_cons, DoneFits]
    refine ⟨⟨?_, by simp⟩, ?_, doneFits_zip b _ rs _ ?_⟩
    · cases r.root <;> rfl
    · rw [List.length_take]
      omega
    · rw [List.length_drop]
      omega

/-- **The chain's possible challenges have the rounds' lengths**: with the stream's messages they
complete the rounds. -/
theorem doneFits_of_mem_chain (rounds : List RoundSpec) (π : UPf) (ch : List (List E))
    (H : List UInt8 → OracleComp spec Bytes32)
    (hch : ch ∈ support ((uniSpec rounds).chain H (uView rounds π).1 (uView rounds π).2)) :
    DoneFits rounds (uDone rounds π ch) ∧ ch.length = rounds.length := by
  rw [ChainSpecU.chain, support_map] at hch
  obtain ⟨sts, hsts, rfl⟩ := hch
  have hl := length_of_mem_runM H _ _ sts hsts
  rw [ChainSpecU.absorbsS, length_absorbsI] at hl
  refine ⟨doneFits_zip _ _ _ _ ?_, length_groupK _ _⟩
  simp only [List.length_map, List.length_tail, hl]
  rfl

end Chain

/-! ## The rounds' roots -/

theorem msgsAt_getElem_fst (b : Array UInt8) : ∀ (o : ℕ) (rs : List RoundSpec) (i : ℕ)
    (h : i < rs.length),
    ((msgsAt b o rs)[i]'(by rw [length_msgsAt]; exact h)).1.isSome = (rs[i]'h).root
  | _, [], _, h => absurd h (by simp)
  | o, r :: rs, 0, _ => by
    simp only [msgsAt, List.getElem_cons_zero]
    cases r.root <;> rfl
  | o, r :: rs, i + 1, h => by
    simp only [msgsAt, List.getElem_cons_succ]
    exact msgsAt_getElem_fst b _ rs i _

/-- **A round's root**: the composed opening reads it off the chain's message (as 32 bytes), the
Statement off the transcript (as two halves); at a round with a root they name the same digest. -/
theorem root_at (rounds : List RoundSpec) (π : UPf) (ch : List (List E)) (i : ℕ)
    (hi : i < rounds.length) (hch : ch.length = rounds.length)
    (hroot : (rounds.getD i ⟨false, 0, 0⟩).root = true) :
    ofB (((msgK (uView rounds) π i).1).getD (Vector.replicate 32 0)) =
      rootOf (((uDone rounds π ch).getD i default).1.1.getD default) := by
  have hl : i < (msgsAt π.proof.stream 24 rounds).length := by rw [length_msgsAt]; exact hi
  have hs := msgsAt_getElem_fst π.proof.stream 24 rounds i hi
  rw [List.getD_eq_getElem _ _ hi] at hroot
  rw [hroot] at hs
  have e1 : msgK (uView rounds) π i = toRMsg ((msgsAt π.proof.stream 24 rounds)[i]'hl) := by
    show ((msgsAt π.proof.stream 24 rounds).map toRMsg).getD i (none, []) = _
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
  have e2 : (uDone rounds π ch).getD i default =
      ((msgsAt π.proof.stream 24 rounds)[i]'hl, ch[i]'(by omega)) := by
    show ((msgsAt π.proof.stream 24 rounds).zip ch).getD i default = _
    rw [List.getD_eq_getElem _ _ (by simp [length_msgsAt]; omega), List.getElem_zip]
  rw [e1, e2]
  rcases hm : ((msgsAt π.proof.stream 24 rounds)[i]'hl).1 with _ | h
  · rw [hm] at hs
    exact absurd hs (by simp)
  · simp only [toRMsg, hm, Option.map_some, Option.getD_some]
    exact Soundness.ofB_toB_root _

/-! ## The Statement's verifier after the run -/

section Rest

variable (shape : UniStatement.Shape) (roots : SetupRoots) (proof : UniProof)

/-- A commitment's call: its root, its layout word, its opening proof. -/
def callOfR (r : Reduced) : Commitment → Digest × List UInt8 × Compile.Proof
  | .c1 => (rootOf r.roots.1, (layoutWords shape).getD 0 [], proof.c1)
  | .c2 => (rootOf r.roots.2, (layoutWords shape).getD 1 [], proof.c2)
  | .setup => (roots.bytecode, (layoutWords shape).getD 2 [], proof.setup)

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- The loop's step over the result's openings. -/
def stepR (r : Reduced) : Commitment × UniStatement.Opening → Bool → m (ForInStep Bool) :=
  fun x ok => match x with
    | (c, opening) => match opening with
      | .point pt value none => match callOfR shape roots proof r c with
        | (root, word, p) => do
          let b ← pcsOpenWith F (layoutWordVars word) root [⟨pt, value⟩] p
          pure (ForInStep.yield (ok && b))
      | _ => pure (ForInStep.yield false)

/-- `Flock`'s matrices' two calls. -/
def matR (r : Reduced) (ok : Bool) : m Bool :=
  match r.matrices with
  | some mc => do
    let b ← pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 3 [])) roots.a0
      [⟨mc.point, mc.a⟩] proof.a0
    let b' ← pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 4 [])) roots.b0
      [⟨mc.point, mc.b⟩] proof.b0
    pure (ok && b && b')
  | none => pure false

/-- **The Statement's verifier after the run**, on its result: the loop, then the matrices. -/
def restR (r : Reduced) : m Bool :=
  forIn r.openings (r.openings.map (·.1) == commitments) (stepR shape roots proof F r) >>=
    matR shape roots proof F r

/-- **The Statement's verifier is the run, then `restR`** on an accepting run's result. -/
theorem verifyWith_eq_rest [LawfulMonad m] (iv : List UInt8) (input : Vector UInt8 32) :
    verifyWith F shape iv roots input proof =
      ((fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWith F shape iv input.toList proof.stream (.flock flockMain) .point) >>= fun p =>
        if !p.1 then pure false else
          match p.2 with
          | .error _ => pure false
          | .ok r => restR shape roots proof F r := by
  rw [bind_map_left]
  rfl

end Rest

/-! ## What an accepting `restR` needs -/

section Support

variable (shape : UniStatement.Shape) (roots : SetupRoots) (proof : UniProof)
variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (F : KeccakState → OracleComp spec KeccakState)

/-- **`PCS_OPEN` rejects a claim of another length**, before any query. -/
theorem pcsOpen_len (vars : ℕ) (root : Digest) (pt : List E) (v : E) (p : Compile.Proof) :
    ∀ b ∈ support (pcsOpenWith F vars root [⟨pt, v⟩] p), b = true → pt.length = vars := by
  intro b hb hbt
  by_contra hne
  unfold pcsOpenWith PcsQuotient.openingWith at hb
  rw [ite_eq_right (by simp [plainLayout, PcsQuotient.Layout.ofChunks, hne])] at hb
  rw [support_pure, Set.mem_singleton_iff] at hb
  rw [hb] at hbt
  exact Bool.false_ne_true hbt

theorem stepR_point (r : Reduced) (c : Commitment) (pt : List E) (v : E) (ok : Bool) :
    stepR shape roots proof F r (c, .point pt v none) ok =
      pcsOpenWith F (layoutWordVars (callOfR shape roots proof r c).2.1)
          (callOfR shape roots proof r c).1 [⟨pt, v⟩] (callOfR shape roots proof r c).2.2 >>=
        fun b => pure (ForInStep.yield (ok && b)) := by
  cases c <;> rfl

theorem stepR_other (r : Reduced) (c : Commitment) (o : UniStatement.Opening)
    (ho : ∀ pt v, o ≠ .point pt v none) (ok : Bool) :
    stepR shape roots proof F r (c, o) ok = pure (ForInStep.yield false) := by
  rcases o with _ | ⟨pt, v, _ | _⟩
  · rfl
  · exact absurd rfl (ho pt v)
  · rfl

/-- **An accepting loop** started from `ok`, and met only point claims without a bit slice, each of
its layout word's variables. -/
theorem forIn_stepR_true (r : Reduced) :
    ∀ (l : List (Commitment × UniStatement.Opening)) (ok : Bool),
      ∀ b ∈ support (forIn l ok (stepR shape roots proof F r)), b = true →
        ok = true ∧ ∀ x ∈ l, ∃ pt v, x.2 = .point pt v none ∧
          pt.length = layoutWordVars (callOfR shape roots proof r x.1).2.1
  | [], ok, b, hb, hbt => by
    rw [List.forIn_nil, support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨hbt, by simp⟩
  | (c, o) :: l, ok, b, hb, hbt => by
    rw [List.forIn_cons, mem_support_bind_iff] at hb
    obtain ⟨y, hy, hb⟩ := hb
    by_cases ho : ∃ pt v, o = .point pt v none
    · obtain ⟨pt, v, rfl⟩ := ho
      rw [stepR_point, mem_support_bind_iff] at hy
      obtain ⟨b1, hb1, hy⟩ := hy
      rw [support_pure, Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨h1, h2⟩ := forIn_stepR_true r l (ok && b1) b hb hbt
      rw [Bool.and_eq_true] at h1
      refine ⟨h1.1, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨pt, v, rfl, pcsOpen_len F _ _ _ _ _ b1 hb1 h1.2⟩
      · exact h2 x hx
    · rw [stepR_other _ _ _ _ _ _ _ (fun pt v h => ho ⟨pt, v, h⟩), support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      exact absurd (forIn_stepR_true r l false b hb hbt).1 (by simp)

/-- **Accepting matrices' calls**: started from `ok`, on a matrices' claim of `A0`'s and `B0`'s
layout words' variables. -/
theorem matR_true (r : Reduced) (ok : Bool) :
    ∀ b ∈ support (matR shape roots proof F r ok), b = true →
      ok = true ∧ ∃ mc, r.matrices = some mc ∧
        mc.point.length = layoutWordVars ((layoutWords shape).getD 3 []) ∧
        mc.point.length = layoutWordVars ((layoutWords shape).getD 4 []) := by
  intro b hb hbt
  unfold matR at hb
  split at hb
  · rename_i mc hmc
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hb
    obtain ⟨bA, hA, bB, hB, rfl⟩ := hb
    simp only [Bool.and_eq_true] at hbt
    exact ⟨hbt.1.1, mc, hmc, pcsOpen_len F _ _ _ _ _ _ hA hbt.1.2,
      pcsOpen_len F _ _ _ _ _ _ hB hbt.2⟩
  · rw [support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact absurd hbt (by simp)

/-- **The main line's result**: three point claims without a bit slice, on `C1`, `C2` and the setup,
each of its layout word's variables, and `Flock`'s matrices' claim of `A0`'s and `B0`'s. -/
def GoodR (r : Reduced) : Prop :=
  ∃ (p1 : List E) (v1 : E) (p2 : List E) (v2 : E) (p3 : List E) (v3 : E) (mc : Flock.MatrixClaim),
    r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)] ∧ r.matrices = some mc ∧
    p1.length = layoutWordVars ((layoutWords shape).getD 0 []) ∧
    p2.length = layoutWordVars ((layoutWords shape).getD 1 []) ∧
    p3.length = layoutWordVars ((layoutWords shape).getD 2 []) ∧
    mc.point.length = layoutWordVars ((layoutWords shape).getD 3 []) ∧
    mc.point.length = layoutWordVars ((layoutWords shape).getD 4 [])

/-- **`restR` accepts only on the main line's result.** -/
theorem restR_good (r : Reduced) :
    ∀ b ∈ support (restR shape roots proof F r), b = true → GoodR shape r := by
  intro b hb hbt
  rw [restR, mem_support_bind_iff] at hb
  obtain ⟨ok, hok, hb⟩ := hb
  obtain ⟨hokt, mc, hmc, h4, h5⟩ := matR_true shape roots proof F r ok b hb hbt
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
  exact ⟨p1, v1, p2, v2, p3, v3, mc, hl, hmc, l1, l2, l3, h4, h5⟩

/-- **Calls one after the other**, their verdicts and-ed onto `ok`. -/
def seqAnd : List (OracleComp spec Bool) → Bool → OracleComp spec Bool
  | [], ok => pure ok
  | P :: Ps, ok => P >>= fun b => seqAnd Ps (ok && b)

theorem seqAnd_cons (P : OracleComp spec Bool) (Ps : List (OracleComp spec Bool)) (ok : Bool) :
    seqAnd (P :: Ps) ok = P >>= fun b => seqAnd Ps (ok && b) := rfl

theorem seqAnd_false : ∀ (Ps : List (OracleComp spec Bool)), ∀ x ∈ support (seqAnd Ps false),
    x = false
  | [], x, hx => by simpa [seqAnd] using hx
  | P :: Ps, x, hx => by
    rw [seqAnd_cons, mem_support_bind_iff] at hx
    obtain ⟨_, -, hx⟩ := hx
    exact seqAnd_false Ps x hx

/-- **On the main line's result, `restR` is the five calls**, one after the other. -/
theorem restR_unroll (r : Reduced) (p1 : List E) (v1 : E) (p2 : List E) (v2 : E) (p3 : List E)
    (v3 : E) (mc : Flock.MatrixClaim)
    (ho : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)]) (hm : r.matrices = some mc) :
    restR shape roots proof F r = seqAnd
      [pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 0 [])) (rootOf r.roots.1)
          [⟨p1, v1⟩] proof.c1,
        pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 1 [])) (rootOf r.roots.2)
          [⟨p2, v2⟩] proof.c2,
        pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 2 [])) roots.bytecode
          [⟨p3, v3⟩] proof.setup,
        pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 3 [])) roots.a0
          [⟨mc.point, mc.a⟩] proof.a0,
        pcsOpenWith F (layoutWordVars ((layoutWords shape).getD 4 [])) roots.b0
          [⟨mc.point, mc.b⟩] proof.b0] true := by
  have hc : (r.openings.map (·.1) == commitments) = true := by
    rw [ho]
    rfl
  rw [restR, hc, ho]
  simp only [List.forIn_cons, List.forIn_nil, stepR_point, bind_assoc, pure_bind,
    seqAnd]
  unfold matR
  rw [hm]
  rfl

end Support

/-! ## The five openings -/

/-- **`PCS_OPEN` is F2's opening with the Statement's early stop**, on the plain layout of
`24 … 28` variables, its two calls answered over `π`. -/
theorem pcsOpen_eq_early (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) (root : Digest)
    (x : Stmt (plainL v).stacking) (cs : List PcsQuotient.Claim)
    (hx : x.claims = cs.map Bridge.claimTr) (p : Compile.Proof) :
    pcsOpenWith Common.queryPermutation v root cs p =
      simulateQ keccakCallsOverQueryPermutation
        (Soundness.ourVerifierEarly (plainL v) logInvRate ((root, x), p)) := by
  rw [pcsOpenWith, Bridge.openingWith_eq_ourVerifier' Common.queryPermutation (plainLayout v)
    (plainL v) (Bridge.layoutTr_ofChunks_zero v v v (2 ^ v)) (Or.inl rfl)
    (admissible_large h1 h2) root x cs hx p, Bridge.keccakCallsWith_queryPermutation]

/-- The early-stop opening accepts at most as often as the opening, over the lazily sampled
permutation, for continuations ordered as accepting implies accepting (`Soundness.early_le` with
the two calls answered over `π`, the inputs given up to equality). -/
theorem early_le_rpm {β γ : Type} (L : WhirBridge.Layout) (R : ℕ)
    (w w' : (Digest × Stmt L.stacking) × Compile.Proof)
    (k₁ : Bool → OracleComp Common.RandomPermutationOracles β)
    (k₂ : Bool → OracleComp Common.RandomPermutationOracles γ) (E₁ : β → Prop) (E₂ : γ → Prop)
    (hw : w' = w)
    (h0 : ∀ s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ false)).run' s}[
      E₁ y] = 0)
    (h1 : ∀ s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ true)).run' s}[
      E₁ y] ≤ Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₂ true)).run' s}[E₂ y])
    (s : Common.PermutationEdges KeccakState) :
    Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles
        (simulateQ keccakCallsOverQueryPermutation (Soundness.ourVerifierEarly L R w) >>=
          k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles
        (simulateQ keccakCallsOverQueryPermutation (WhirBridge.ourVerifier L R w') >>=
          k₂)).run' s}[E₂ y] := by
  subst hw
  have hk : ∀ b s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ b)).run' s}[
      E₁ y] ≤ Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₂ b)).run' s}[E₂ y] := by
    intro b s
    cases b
    · rw [h0 s]
      exact bot_le
    · exact h1 s
  unfold Soundness.ourVerifierEarly
  split
  · exact Soundness.mono_bind _ _ _ _ _ _ hk s
  · rw [simulateQ_pure, pure_bind, h0 s]
    exact bot_le

theorem sim_opsRun_cons {γ : Type} (view : UPf → FSt × List (RMsg E)) (o : WhirOp UPf E Stk)
    (os : List (WhirOp UPf E Stk)) (π : UPf) (ch : List (List E))
    (g : List Bool → OracleComp KeccakCalls γ) :
    simulateQ keccakCallsOverQueryPermutation (opsRun view (o :: os) π ch >>= g) =
      simulateQ keccakCallsOverQueryPermutation
          (WhirBridge.ourVerifier o.S.L o.S.R (WhirOp.input view o π ch)) >>= fun b =>
        simulateQ keccakCallsOverQueryPermutation (opsRun view os π ch >>= fun bs => g (b :: bs)) := by
  rw [opsRun, bind_assoc, simulateQ_bind]
  simp only [bind_map_left]

theorem sim_opsRun_nil {γ : Type} (view : UPf → FSt × List (RMsg E)) (π : UPf)
    (ch : List (List E)) (g : List Bool → OracleComp KeccakCalls γ) :
    simulateQ keccakCallsOverQueryPermutation
        (opsRun view ([] : List (WhirOp UPf E Stk)) π ch >>= g) =
      simulateQ keccakCallsOverQueryPermutation (g []) := by
  rw [opsRun, pure_bind]

/-! ## The bridge -/

section Bridge

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)

theorem length_uRounds : (uRounds Fl nV V).length = Fl.prog.rounds.length + 3 + V := by
  simp [uniRounds]
  omega

/-- The claims of the opening of a layout word's variables, its one claim. -/
theorem claims_uCl (k : ℕ) (pt : List E) (v : E) (hl : pt.length = wv D k) :
    (uCl D k [⟨pt, v⟩]).claims = [(⟨pt, v⟩ : PcsQuotient.Claim)].map Bridge.claimTr :=
  mkStmt_claims _ _ _ (by simp) fun c hc => by
    rw [List.mem_singleton] at hc
    subst hc
    exact hl

theorem wellFormed_of_good (r : Reduced) (p1 : List E) (v1 : E) (p2 : List E) (v2 : E)
    (p3 : List E) (v3 : E) (mc : Flock.MatrixClaim)
    (ho : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none),
      (.setup, .point p3 v3 none)]) (hm : r.matrices = some mc)
    (l1 : p1.length = wv D 0) (l2 : p2.length = wv D 1) (l3 : p3.length = wv D 2)
    (l4 : mc.point.length = wv D 3) (l5 : mc.point.length = wv D 4) : WellFormed D r := by
  refine ⟨by rw [ho]; rfl, ?_, ?_, ?_, fun mc' hmc' => ?_⟩
  · simp [claimsOf, ho, l1]
  · simp [claimsOf, ho, l2]
  · simp [claimsOf, ho, l3]
  · rw [hm] at hmc'
    cases hmc'
    exact ⟨l4, l5⟩

end Bridge

/-- **THE VERIFIER BRIDGE**, from the walk (`UniWalk`, `UniWalkReject`) and the chain program's
roots (`UniOutRoots`). -/
theorem uniVerifierBridge_of_walk (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ)
    (C : UniCode D Fl nV V) (hs : UniShapes D) (hW : UniWalk D Fl nV V C)
    (hR : UniWalkReject D Fl nV V) (hO : UniOutRoots D Fl nV V C) :
    UniVerifierBridge D Fl nV V C hs := by
  intro π s
  rw [verifyWith_eq_rest]
  by_cases hlen : π.proof.stream.size = uLen Fl nV V
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
  obtain ⟨hfits, hlch⟩ := doneFits_of_mem_chain (uRounds Fl nV V) π ch _ hch
  dsimp only
  cases hacc : uAccB D Fl nV V C π ch
  · -- the walk's verdict rejects
    rw [ite_eq_left (show (!false) = true from rfl), Soundness.zero_pure _ false _ (by simp) s]
    exact zero_le
  rw [ite_eq_right (show ¬ ((!true) = true) by decide)]
  have hz : (C.prog (uSt Fl nV V π).1 (uSt Fl nV V π).2).ZerosVanish
      (uDone (uRounds Fl nV V) π ch) (uTail (uRounds Fl nV V) π) :=
    (@of_decide_eq_true _ (Classical.propDecidable _) hacc).2
  by_cases hg : GoodR D.shape (uOut D Fl nV V C π ch)
  swap
  · -- not the main line's result: the Statement rejects
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun b hb hbt => ?_) s)).trans zero_le
    exact hg (restR_good D.shape π.roots π.proof Common.queryPermutation _ b hb hbt)
  obtain ⟨p1, v1, p2, v2, p3, v3, mc, ho, hm, l1, l2, l3, l4, l5⟩ := hg
  rw [← wv_eq] at l1 l2 l3 l4 l5
  have hcheck : uniCheck D Fl nV V C π ch :=
    ⟨hfits, hz, wellFormed_of_good D _ p1 v1 p2 v2 p3 v3 mc ho hm l1 l2 l3 l4 l5⟩
  -- the claims
  have hx1 : (cl1 D Fl nV V C π ch).claims = [(⟨p1, v1⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl1, show claimsOf (uOut D Fl nV V C π ch) .c1 = [⟨p1, v1⟩] by simp [claimsOf, ho]]
    exact claims_uCl D 0 p1 v1 l1
  have hx2 : (cl2 D Fl nV V C π ch).claims = [(⟨p2, v2⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl2, show claimsOf (uOut D Fl nV V C π ch) .c2 = [⟨p2, v2⟩] by simp [claimsOf, ho]]
    exact claims_uCl D 1 p2 v2 l2
  have hx3 : (cl3 D Fl nV V C π ch).claims = [(⟨p3, v3⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl3, show claimsOf (uOut D Fl nV V C π ch) .setup = [⟨p3, v3⟩] by simp [claimsOf, ho]]
    exact claims_uCl D 2 p3 v3 l3
  have hx4 : (cl4 D Fl nV V C π ch).claims =
      [(⟨mc.point, mc.a⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl4, show matClaims (uOut D Fl nV V C π ch) true = [⟨mc.point, mc.a⟩] by
      simp [matClaims, hm]]
    exact claims_uCl D 3 _ _ l4
  have hx5 : (cl5 D Fl nV V C π ch).claims =
      [(⟨mc.point, mc.b⟩ : PcsQuotient.Claim)].map Bridge.claimTr := by
    rw [cl5, show matClaims (uOut D Fl nV V C π ch) false = [⟨mc.point, mc.b⟩] by
      simp [matClaims, hm]]
    exact claims_uCl D 4 _ _ l5
  -- the rounds' roots
  have hr1 : ofB (((msgK (uView (uRounds Fl nV V)) π 0).1).getD (Vector.replicate 32 0)) =
      rootOf (uOut D Fl nV V C π ch).roots.1 := by
    rw [hO π ch]
    exact root_at _ π ch 0 (by rw [length_uRounds]; omega) hlch (by
      rw [uniRounds_getD_zero])
  have hr2 : ofB (((msgK (uView (uRounds Fl nV V)) π (Fl.prog.rounds.length + 1)).1).getD
      (Vector.replicate 32 0)) = rootOf (uOut D Fl nV V C π ch).roots.2 := by
    rw [hO π ch]
    exact root_at _ π ch _ (by rw [length_uRounds]; omega) hlch (by
      rw [uniRounds_getD_c2])
  -- the Statement's five calls, F2's early-stop openings
  rw [restR_unroll D.shape π.roots π.proof Common.queryPermutation _ p1 v1 p2 v2 p3 v3 mc ho hm,
    ← wv_eq, ← wv_eq, ← wv_eq, ← wv_eq, ← wv_eq,
    pcsOpen_eq_early (wv D 0) (hs.lo 0 (by decide)) (hs.hi 0 (by decide)) _ _ _ hx1,
    pcsOpen_eq_early (wv D 1) (hs.lo 1 (by decide)) (hs.hi 1 (by decide)) _ _ _ hx2,
    pcsOpen_eq_early (wv D 2) (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _ _ _ hx3,
    pcsOpen_eq_early (wv D 3) (hs.lo 3 (by decide)) (hs.hi 3 (by decide)) _ _ _ hx4,
    pcsOpen_eq_early (wv D 4) (hs.lo 4 (by decide)) (hs.hi 4 (by decide)) _ _ _ hx5]
  -- the composed side's five openings
  unfold uOps uniOps
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
  -- A0
  rw [seqAnd_cons, sim_opsRun_cons]
  refine early_le_rpm _ _ _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · exact Prod.ext (Prod.ext (Soundness.ofB_toB_root _) rfl) rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- B0
  rw [seqAnd_cons, sim_opsRun_cons]
  refine early_le_rpm _ _ _ _ _ _ _ _ ?_ (fun s => ?_) (fun s => ?_) s
  · exact Prod.ext (Prod.ext (Soundness.ofB_toB_root _) rfl) rfl
  · refine Soundness.zero_of_support _ _ _ (fun x hx => ?_) s
    rw [seqAnd_false _ x hx]
    exact Bool.false_ne_true
  -- every opening accepted
  rw [seqAnd, sim_opsRun_nil, simulateQ_pure]
  refine Soundness.le_pure _ _ _ _ _ (fun _ => ⟨hcheck, fun k hk => ?_⟩) s
  have hk5 : k < 5 := hk
  interval_cases k <;> rfl


end UniSound

/-- info: 'UniSound.uniVerifierBridge_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniVerifierBridge_of_walk
