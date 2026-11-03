-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `formal/UniSound/UniSound/FsVerifier.lean`
-- (`uniVerifierBridge_of_walk`) to π2's contract (`formal/RecStatement/RecStatement/Security.lean`, `contractWith`).
import RecCompose.FsOps
import RecCompose.OpeningsAgree
import UniSound.FsVerifier
import UniSound.FsWalkProof

/-!
# π2's verifier bridge

**`pi2VerifierBridge`**: from any state of the lazily sampled permutation, π2's contract past its IV
(`contractRest`: π2's run on the stream, then the six `PCS_OPEN` calls) accepts at most as often as the composed
verifier (the chain `pi2Spec`, then the six openings `p2Ops`) passes `p2Check` with every opening accepting, from the
walk (`Pi2Walk`, `Pi2WalkReject`):

* a stream of another length is rejected (`Pi2WalkReject`);
* on a stream of `944` bytes the run is the chain (`Pi2Walk` at `F = π`), which both sides run first;
* per challenges: the run's verdict `all ≠ 0`; the six calls (`pcsCalls`) decode under the registry to the composed
  openings' inputs (π1's three on their plain layouts, `UniSound.pcsOpen_eq_early`; π2's three on `shW`, `shS`, `shQ`,
  `Bridge.openingWith_eq_ourVerifier'`), each F2's opening with the Statement's early stop, accepting at most as often
  as the composed one (`UniSound.early_le_rpm`); a call that does not decode rejects.

The contract's loop is the six calls one after the other, their verdicts and-ed (`forIn_seqAndK`); π1's three calls'
layout words are `Data.pi1Calls`' constants (byte `24`: `27`, `27`, `24` variables; first byte `0x15`, no π2 layout
word, `"pi2"`), so a π1 call that decodes is opened on π1's plain layout of its variables (`pi1Open`); π2's three are
`pcsCalls`' last three, their roots the stream's `W`, `Q` root words and the setup's root word (`pcsCalls_cc`,
`rootOfWord_streamWord`), their claims the run's (`decodeWith_mk`, `claimsOfWords_mk`).
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

section With

variable {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)

/-- **π2's contract past its IV** (`contractWith` after `ivWith`): π2's run at the IV, then the six calls. -/
def contractRest (D : RecDeployment) (roots : RecSetupRoots) (iv : List UInt8) (input : Vector UInt8 32)
    (proof : RecProof) : m (Bool × List (List (List UInt8))) := do
  let c := D.circuitAt roots.pi1
  let o ← runWith F (Spec.of c.circuit) iv input.toList proof.stream
  match o.result with
  | .error _ => return (false, [])
  | .ok r =>
    if !o.accepts then return (false, []) else
    let calls := pcsCalls c.circuit (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2)
      proof.stream r
    if calls.length ≠ 6 then return (false, calls) else
    let reg := registryOf D.pi1.shape c.circuit.logN
    let mut ok := true
    for (words, p) in calls.zip proof.openings do
      ok := ok && (← pcsOpenAt F reg words p)
    return (ok, calls)

theorem contractWith_eq (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    D.contractWith F roots input proof = D.ivWith F roots >>= fun iv => contractRest F D roots iv input proof := rfl

/-- **The contract past its run**, on what it reads of the run's outcome (its verdict and result), at the real
circuit. -/
def restC (D : RecDeployment) (roots : RecSetupRoots) (proof : RecProof)
    (p : Bool × Except UniStatement.UniError RecStatement.Reduced) : m (Bool × List (List (List UInt8))) :=
  match p.2 with
  | .error _ => pure (false, [])
  | .ok r =>
    if !p.1 then pure (false, []) else
    if (pcsCalls cc (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) proof.stream r).length ≠ 6
    then pure (false, pcsCalls cc (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) proof.stream r)
    else
      forIn ((pcsCalls cc (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) proof.stream r).zip
          proof.openings) true (fun x s => do
        let b ← pcsOpenAt F (registryOf D.pi1.shape cc.logN) x.1 x.2
        pure (ForInStep.yield (s && b))) >>= fun ok =>
      pure (ok, pcsCalls cc (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) proof.stream r)

end With

/-- **The contract past its IV reads the run's verdict and result only**, at the real circuit. -/
theorem contractRest_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (D : RecDeployment) (roots : RecSetupRoots) (iv : List UInt8) (input : Vector UInt8 32) (proof : RecProof)
    (hc : (D.circuitAt roots.pi1).circuit = cc) :
    contractRest F D roots iv input proof =
      ((fun o : RecStatement.Outcome => (o.accepts, o.result)) <$>
        runWith F (Spec.of cc) iv input.toList proof.stream) >>= restC F D roots proof := by
  rw [bind_map_left]
  simp only [contractRest, hc]
  rfl

/-- **VERIFIER**: from any state of the lazily sampled permutation, π2's contract past its IV on a proof (its IV,
roots, input and recursive proof) accepts at most as often as the composed verifier on it passes `p2Check` with every
opening accepting. -/
def Pi2VerifierBridge (D : RecDeployment) : Prop :=
  ∀ (π : P2Pf) (s : Common.PermutationEdges LeanVM.Semantics.KeccakState),
    Pr{let x ← (simulateQ Common.lazyRandomPermutationOracles
        (contractRest Common.queryPermutation D (p2Roots π) π.iv.toList π.input π.proof)).run' s}[x.1 = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (simulateQ keccakCallsOverQueryPermutation
          (verU pi2Spec p2View (opsRun p2View (p2Ops D)) π))).run' s}[
        p2Check π v.1 ∧ ∀ k < (p2Ops D).length, v.2.getD k false = true]

/-! ## The run rejects: the contract rejects -/

theorem restC_reject (D : RecDeployment) (roots : RecSetupRoots) (proof : RecProof)
    (p : Bool × Except UniStatement.UniError RecStatement.Reduced) (hp : p.1 = false) :
    ∀ x ∈ support (restC (m := OracleComp Common.RandomPermutationOracles) Common.queryPermutation D roots proof p),
      x.1 = false := by
  intro x hx
  obtain ⟨b, r⟩ := p
  simp only at hp
  subst hp
  cases r with
  | error e =>
    simp only [restC, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | ok r =>
    simp only [restC, Bool.not_false, ite_true, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]

/-! ## The composed verifier: the chain, then the openings -/

/-- **The composed verifier, its two calls answered over `π`**: the chain over Keccak-256 the sponge over `π`, then
the openings (`UniSound.simulateQ_verU` for π2). -/
theorem simulateQ_verU2 {β : Type} (post : P2Pf → List (List E) → OracleComp KeccakCalls β) (π : P2Pf) :
    simulateQ keccakCallsOverQueryPermutation (verU pi2Spec p2View post π) =
      pi2Spec.chain (fun x => toB <$> keccak256With Common.queryPermutation x) (p2View π).1 (p2View π).2 >>=
        fun ch => simulateQ keccakCallsOverQueryPermutation (post π ch >>= fun b => pure (ch, b)) := by
  rw [verU, simulateQ_bind]
  congr 1
  rw [ChainSpecU.chain, ChainSpecU.chain, simulateQ_map, UniSound.simulateQ_runM]
  simp only [UniSound.simulateQ_hash256]

theorem sim_opsRun_cons2 {γ : Type} (o : WhirOp P2Pf E Stk) (os : List (WhirOp P2Pf E Stk)) (π : P2Pf)
    (ch : List (List E)) (g : List Bool → OracleComp KeccakCalls γ) :
    simulateQ keccakCallsOverQueryPermutation (opsRun p2View (o :: os) π ch >>= g) =
      simulateQ keccakCallsOverQueryPermutation
          (WhirBridge.ourVerifier o.S.L o.S.R (WhirOp.input p2View o π ch)) >>= fun b =>
        simulateQ keccakCallsOverQueryPermutation (opsRun p2View os π ch >>= fun bs => g (b :: bs)) := by
  rw [opsRun, bind_assoc, simulateQ_bind]
  simp only [bind_map_left]

theorem sim_opsRun_nil2 {γ : Type} (π : P2Pf) (ch : List (List E)) (g : List Bool → OracleComp KeccakCalls γ) :
    simulateQ keccakCallsOverQueryPermutation (opsRun p2View ([] : List (WhirOp P2Pf E Stk)) π ch >>= g) =
      simulateQ keccakCallsOverQueryPermutation (g []) := by
  rw [opsRun, pure_bind]

/-- **The chain's possible challenges have the rounds' lengths** (`3`, `1`, `1`). -/
theorem chain_lengths {ι : Type} {spec : OracleSpec.{0, 0} ι} (π : P2Pf) (ch : List (List E))
    (H : List UInt8 → OracleComp spec Bytes32)
    (hch : ch ∈ support (pi2Spec.chain H (p2View π).1 (p2View π).2)) :
    ch.length = 3 ∧ (ch.getD 0 []).length = 3 ∧ (ch.getD 1 []).length = 1 ∧ (ch.getD 2 []).length = 1 := by
  rw [ChainSpecU.chain, support_map] at hch
  obtain ⟨sts, hsts, rfl⟩ := hch
  have hl := UniSound.length_of_mem_runM H _ _ sts hsts
  rw [ChainSpecU.absorbsS, length_absorbsI] at hl
  have h5 : (sts.tail.map (chalL pi2Spec.K.lim)).length = 5 := by
    rw [List.length_map, List.length_tail, hl]
    rfl
  have hc : pi2Spec.K.chalsOf sts = groupK (RecPiop.pi2Rounds 4) (sts.tail.map (chalL pi2Spec.K.lim)) := rfl
  rw [hc]
  generalize sts.tail.map (chalL pi2Spec.K.lim) = l at h5 ⊢
  simp [groupK, RecPiop.pi2Rounds, h5]

/-! ## The contract's loop, the calls and-ed -/

/-- The calls one after the other, their verdicts and-ed from `ok`, then `kf`. -/
def seqAndK {γ : Type} : List (OracleComp Common.RandomPermutationOracles Bool) → Bool →
    (Bool → OracleComp Common.RandomPermutationOracles γ) → OracleComp Common.RandomPermutationOracles γ
  | [], ok, kf => kf ok
  | P :: Ps, ok, kf => P >>= fun b => seqAndK Ps (ok && b) kf

theorem seqAndK_cons {γ : Type} (P : OracleComp Common.RandomPermutationOracles Bool)
    (Ps : List (OracleComp Common.RandomPermutationOracles Bool)) (ok : Bool)
    (kf : Bool → OracleComp Common.RandomPermutationOracles γ) :
    seqAndK (P :: Ps) ok kf = P >>= fun b => seqAndK Ps (ok && b) kf := rfl

theorem seqAndK_false {γ : Type} (kf : Bool → OracleComp Common.RandomPermutationOracles γ) :
    ∀ (Ps : List (OracleComp Common.RandomPermutationOracles Bool)), ∀ x ∈ support (seqAndK Ps false kf),
      x ∈ support (kf false)
  | [], x, hx => hx
  | P :: Ps, x, hx => by
    rw [seqAndK_cons, mem_support_bind_iff] at hx
    obtain ⟨b, -, hx⟩ := hx
    exact seqAndK_false kf Ps x (by simpa using hx)

/-- **The contract's loop is the calls one after the other, and-ed.** -/
theorem forIn_seqAndK {γ : Type} (reg : List (List UInt8 × Opener)) :
    ∀ (l : List (List (List UInt8) × Compile.Proof)) (ok : Bool)
      (kf : Bool → OracleComp Common.RandomPermutationOracles γ),
      (forIn l ok (fun x s => do
          let b ← pcsOpenAt Common.queryPermutation reg x.1 x.2
          pure (ForInStep.yield (s && b))) >>= kf) =
        seqAndK (l.map fun x => pcsOpenAt Common.queryPermutation reg x.1 x.2) ok kf
  | [], ok, kf => by simp [seqAndK]
  | x :: l, ok, kf => by
    simp only [List.forIn_cons, bind_assoc, pure_bind, List.map_cons, seqAndK_cons]
    congr 1
    funext b
    exact forIn_seqAndK reg l (ok && b) kf

/-- **One call against one composed opening**: a call that is `false` or the opening with the Statement's early stop
accepts at most as often as the composed opening, for continuations ordered as accepting implies accepting. -/
theorem step_le {β γ : Type} (P : OracleComp Common.RandomPermutationOracles Bool) (L : WhirBridge.Layout) (R : ℕ)
    (w : (Digest × Stmt L.stacking) × Compile.Proof)
    (k₁ : Bool → OracleComp Common.RandomPermutationOracles β)
    (k₂ : Bool → OracleComp Common.RandomPermutationOracles γ) (E₁ : β → Prop) (E₂ : γ → Prop)
    (hP : P = pure false ∨ P = simulateQ keccakCallsOverQueryPermutation (Soundness.ourVerifierEarly L R w))
    (h0 : ∀ s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ false)).run' s}[E₁ y] = 0)
    (h1 : ∀ s, Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₁ true)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (k₂ true)).run' s}[E₂ y])
    (s : Common.PermutationEdges LeanVM.Semantics.KeccakState) :
    Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles (P >>= k₁)).run' s}[E₁ y] ≤
      Pr{let y ← (simulateQ Common.lazyRandomPermutationOracles
        (simulateQ keccakCallsOverQueryPermutation (WhirBridge.ourVerifier L R w) >>= k₂)).run' s}[E₂ y] := by
  rcases hP with rfl | rfl
  · rw [pure_bind, h0 s]
    exact zero_le
  · exact UniSound.early_le_rpm L R w w k₁ k₂ E₁ E₂ rfl h0 h1 s

/-! ## Bytes -/

theorem streamWord_length (b : Array UInt8) (o : ℕ) (h : o + 32 ≤ b.size) : (streamWord b o).length = 32 := by
  simp [streamWord]
  omega

theorem revRoot_eq (r : Bytes32) : UniSound.revRoot r = rootWordOfBytes r.toList := by
  unfold UniSound.revRoot rootWordOfBytes
  rw [List.take_of_length_le (l := r.toList.drop 16) (by simp)]

/-- **A root word of the stream names the root the stream's halves name.** -/
theorem rootOfWord_streamWord (b : Array UInt8) (o : ℕ) (h : o + 32 ≤ b.size) :
    rootOfWord (streamWord b o) = UniStatement.rootOf (UniSound.halvesAt b o) := by
  have e1 : streamWord b o = UniSound.bytesAt b o 32 := by
    rw [streamWord, UniSound.toList_extract_eq]
    congr 1
    omega
  rw [e1, ← UniSound.revRoot_halvesAt b o h, revRoot_eq, Bridge.toB_toList,
    rootOfWord_rootWordOfBytes_digestBytes]

theorem rootWordOfBytes_length (d : Digest) : (rootWordOfBytes (digestBytes d)).length = 32 := by
  have := Pi1Decode.length_digestBytes d
  simp [rootWordOfBytes, this]

/-! ## Decoding a call -/

theorem getD_flatten_blocks {α : Type} (d : α) (n : ℕ) :
    ∀ (bs : List (List α)), (∀ b ∈ bs, b.length = n) → ∀ c j, c < bs.length → j < n →
      bs.flatten.getD (c * n + j) d = (bs.getD c []).getD j d
  | [], _, c, j, hc, _ => absurd hc (by simp)
  | b :: bs, h, 0, j, _, hj => by
    simp only [List.flatten_cons, zero_mul, zero_add, List.getD_cons_zero]
    exact Pi1Decode.getD_append_left' d (by rw [h b List.mem_cons_self]; exact hj)
  | b :: bs, h, c + 1, j, hc, hj => by
    simp only [List.flatten_cons, List.getD_cons_succ]
    have hb := h b List.mem_cons_self
    rw [show (c + 1) * n + j = b.length + (c * n + j) by rw [hb]; ring, Pi1Decode.getD_append_right']
    exact getD_flatten_blocks d n bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) c j
      (by simpa using hc) hj

theorem length_flatten_claimWords (v : ℕ) :
    ∀ (cs : List (List E × E)), (∀ c ∈ cs, c.1.length = v) →
      ((cs.map claimWords).flatten).length = cs.length * (v + 1)
  | [], _ => by simp
  | c :: cs, h => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    rw [length_flatten_claimWords v cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]
    simp only [claimWords, List.length_map, List.length_append, h c List.mem_cons_self, List.length_singleton]
    ring

/-- **A call's claims' words read back**, after its three header words. -/
theorem claimsOfWords_mk (hd : List (List UInt8)) (hh : hd.length = 3) (v : ℕ) (cs : List (List E × E))
    (hpts : ∀ c ∈ cs, c.1.length = v) :
    claimsOfWords (hd ++ (cs.map claimWords).flatten) cs.length v =
      some (cs.map fun c => (⟨c.1, c.2⟩ : PcsQuotient.Claim)) := by
  have hbl : ∀ b ∈ cs.map claimWords, b.length = v + 1 := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    simp [claimWords, hpts c hc]
  have hW : ∀ c j, c < cs.length → j < v + 1 →
      (hd ++ (cs.map claimWords).flatten).getD (3 + c * (v + 1) + j) [] =
        ((cs.map claimWords).getD c []).getD j [] := by
    intro c j hc hj
    rw [show 3 + c * (v + 1) + j = hd.length + (c * (v + 1) + j) by rw [hh]; ring,
      Pi1Decode.getD_append_right']
    exact getD_flatten_blocks [] (v + 1) _ hbl c j (by simpa using hc) hj
  have hcw : ∀ c (hc : c < cs.length) j, j < v + 1 →
      ((cs.map claimWords).getD c []).getD j [] = UniStatement.elementWord (((cs[c]'hc).1 ++ [(cs[c]'hc).2]).getD j 0) := by
    intro c hc j hj
    have hlen : j < ((cs[c]'hc).1 ++ [(cs[c]'hc).2]).length := by
      simp [hpts _ (List.getElem_mem hc)]
      omega
    have e1 : (cs.map claimWords).getD c [] = claimWords (cs[c]'hc) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hc), List.getElem_map]
    rw [e1, claimWords, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlen), List.getElem_map,
      List.getD_eq_getElem _ _ hlen]
  unfold claimsOfWords
  have key := Pi1Decode.mapM_range_eq_some (⟨[], 0⟩ : PcsQuotient.Claim) (cs.map fun c => (⟨c.1, c.2⟩ : PcsQuotient.Claim))
    (fun c ↦ do
      let point ← (List.range v).mapM fun j ↦
        elementOfWord ((hd ++ (cs.map claimWords).flatten).getD (3 + c * (v + 1) + j) [])
      let value ← elementOfWord ((hd ++ (cs.map claimWords).flatten).getD (3 + c * (v + 1) + v) [])
      pure (⟨point, value⟩ : PcsQuotient.Claim)) (fun c hc => by
        rw [List.length_map] at hc
        have hvc : (cs[c]'hc).1.length = v := hpts _ (List.getElem_mem hc)
        have hpt : (List.range v).mapM (fun j ↦
            elementOfWord ((hd ++ (cs.map claimWords).flatten).getD (3 + c * (v + 1) + j) [])) =
            some (cs[c]'hc).1 := by
          have := Pi1Decode.mapM_range_eq_some 0 (cs[c]'hc).1 (fun j ↦
            elementOfWord ((hd ++ (cs.map claimWords).flatten).getD (3 + c * (v + 1) + j) [])) fun j hj => by
              rw [hW c j hc (by omega), hcw c hc j (by omega), Pi1Decode.getD_append_left' _ hj,
                Pi1Decode.elementOfWord_elementWord]
          rwa [hvc] at this
        have hval : elementOfWord ((hd ++ (cs.map claimWords).flatten).getD (3 + c * (v + 1) + v) []) =
            some (cs[c]'hc).2 := by
          rw [hW c v hc (by omega), hcw c hc v (by omega), show v = (cs[c]'hc).1.length + 0 by omega,
            Pi1Decode.getD_append_right']
          exact Pi1Decode.elementOfWord_elementWord _
        rw [hpt, hval, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map]
        rfl)
  rwa [List.length_map] at key

/-- **A call's words decode**: its root word, a registered layout word, its claims' count and claims. -/
theorem decodeWith_mk (reg : List (List UInt8 × Opener)) (root lw : List UInt8) (op : Opener)
    (cs : List (List E × E)) (hroot : root.length = 32) (hlook : reg.lookup lw = some op)
    (hk : 1 ≤ cs.length) (hkc : countOfWord (UniStatement.numberWord cs.length) = some cs.length)
    (hpts : ∀ c ∈ cs, c.1.length = op.vars) :
    decodeWith reg ([root, lw, UniStatement.numberWord cs.length] ++ (cs.map claimWords).flatten) =
      some (rootOfWord root, op, cs.map fun c => (⟨c.1, c.2⟩ : PcsQuotient.Claim)) := by
  have hlen : ([root, lw, UniStatement.numberWord cs.length] ++ (cs.map claimWords).flatten).length =
      3 + cs.length * (op.vars + 1) := by
    rw [List.length_append, length_flatten_claimWords op.vars cs hpts]
    rfl
  have h0 : ([root, lw, UniStatement.numberWord cs.length] ++ (cs.map claimWords).flatten).head? = some root := rfl
  have h1 : ([root, lw, UniStatement.numberWord cs.length] ++ (cs.map claimWords).flatten)[1]? = some lw := rfl
  have h2 : ([root, lw, UniStatement.numberWord cs.length] ++ (cs.map claimWords).flatten)[2]? =
      some (UniStatement.numberWord cs.length) := rfl
  unfold decodeWith
  simp only [h0, h1, h2, hlook, hkc, Option.bind_eq_bind, Option.bind_some, hlen, hroot, hk, true_and,
    Bool.not_true, decide_true]
  rw [claimsOfWords_mk _ rfl op.vars cs hpts]
  rfl

theorem mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → List.Forall₂ (fun a b => f a = some b) l r
  | [], r, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact List.Forall₂.nil
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, rs, hrs, rfl⟩ := h
    exact List.Forall₂.cons hb (mapM_forall₂ f l rs hrs)

theorem forall₂_exists_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, b, hb => absurd hb (by simp)
  | _, _, .cons (a := a) h hs, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_exists_left hs b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem claimsOfWords_shape (ws : List (List UInt8)) (k v : ℕ) (cl : List PcsQuotient.Claim)
    (h : claimsOfWords ws k v = some cl) : cl.length = k ∧ ∀ c ∈ cl, c.point.length = v := by
  unfold claimsOfWords at h
  have hf := mapM_forall₂ _ _ _ h
  refine ⟨by rw [← hf.length_eq, List.length_range], fun c hc => ?_⟩
  obtain ⟨i, -, hi⟩ := forall₂_exists_left hf c hc
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hi
  obtain ⟨point, hp, value, -, rfl⟩ := hi
  have := (mapM_forall₂ _ _ _ hp).length_eq
  simpa using this.symm

/-- **What a call decodes to**: its claims, as many as its count word says, each of its opener's variables. -/
theorem decodeWith_shape (reg : List (List UInt8 × Opener)) (ws : List (List UInt8))
    (x : Digest × Opener × List PcsQuotient.Claim) (h : decodeWith reg ws = some x) :
    (∃ k, countOfWord (ws.getD 2 []) = some k ∧ x.2.2.length = k) ∧ ∀ c ∈ x.2.2, c.point.length = x.2.1.vars := by
  unfold decodeWith at h
  cases hw0 : ws.head? with
  | none => simp [hw0] at h
  | some root =>
    simp only [hw0, Option.bind_eq_bind, Option.bind_some] at h
    cases hw1 : ws[1]? with
    | none => simp [hw1] at h
    | some layout =>
      simp only [hw1, Option.bind_some] at h
      cases hl : reg.lookup layout with
      | none => simp [hl] at h
      | some op =>
        simp only [hl, Option.bind_some] at h
        cases hw2 : ws[2]? with
        | none => simp [hw2] at h
        | some cw =>
          simp only [hw2, Option.bind_some] at h
          cases hk : countOfWord cw with
          | none => simp [hk] at h
          | some k =>
            simp only [hk, Option.bind_some] at h
            split at h
            · exact absurd h (by simp)
            · cases hcl : claimsOfWords ws k op.vars with
              | none => simp [hcl] at h
              | some cl =>
                simp only [hcl, Option.bind_some, Option.pure_def, Option.some.injEq] at h
                subst h
                obtain ⟨h1, h2⟩ := claimsOfWords_shape ws k op.vars cl hcl
                have hg : ws.getD 2 [] = cw := by rw [List.getD_eq_getElem?_getD, hw2, Option.getD_some]
                exact ⟨⟨k, by rw [hg, hk], h1⟩, h2⟩

/-! ## The registry -/

theorem layoutWords_cc : RecStatement.layoutWords cc.logN =
    (layoutWord witnessCode cc.logN lW, layoutWord quotientCode cc.logN lQ, layoutWord setupCode cc.logN lS) := by
  unfold RecStatement.layoutWords
  rw [layoutsOf_cc]

theorem registry_eq (sh : UniStatement.Shape) :
    registryOf sh cc.logN =
      [((RecStatement.layoutWords cc.logN).1, .pi2 lW), ((RecStatement.layoutWords cc.logN).2.1, .pi2 lQ),
        ((RecStatement.layoutWords cc.logN).2.2, .pi2 lS)] ++
      ((UniStatement.layoutWords sh).take 3).map fun word ↦ (word, .pi1 (UniStatement.layoutWordVars word)) := by
  unfold registryOf
  rw [layoutsOf_cc]

theorem layoutWord_getD23 (code m : ℕ) (L : PcsQuotient.Layout) :
    (layoutWord code m L).getD 23 0 = code.toUInt8 := by
  have h : "pi2".toUTF8.toList = [112, 105, 50] := by decide +kernel
  unfold layoutWord
  rw [h]
  rfl

theorem ne_of_getD23 {a b : List UInt8} (h : a.getD 23 0 ≠ b.getD 23 0) : a ≠ b := fun e ↦ h (e ▸ rfl)

theorem lw_ne_lq : (RecStatement.layoutWords cc.logN).2.1 ≠ (RecStatement.layoutWords cc.logN).1 := by
  rw [layoutWords_cc]
  exact ne_of_getD23 (by rw [layoutWord_getD23, layoutWord_getD23]; decide)

theorem ls_ne_lw : (RecStatement.layoutWords cc.logN).2.2 ≠ (RecStatement.layoutWords cc.logN).1 := by
  rw [layoutWords_cc]
  exact ne_of_getD23 (by rw [layoutWord_getD23, layoutWord_getD23]; decide)

theorem ls_ne_lq : (RecStatement.layoutWords cc.logN).2.2 ≠ (RecStatement.layoutWords cc.logN).2.1 := by
  rw [layoutWords_cc]
  exact ne_of_getD23 (by rw [layoutWord_getD23, layoutWord_getD23]; decide)

theorem lookup_lw (sh : UniStatement.Shape) :
    (registryOf sh cc.logN).lookup (RecStatement.layoutWords cc.logN).1 = some (.pi2 lW) := by
  rw [registry_eq, List.cons_append, lookup_cons_self]

theorem lookup_lq (sh : UniStatement.Shape) :
    (registryOf sh cc.logN).lookup (RecStatement.layoutWords cc.logN).2.1 = some (.pi2 lQ) := by
  rw [registry_eq, List.cons_append, lookup_cons_ne _ _ _ _ lw_ne_lq, List.cons_append, lookup_cons_self]

theorem lookup_ls (sh : UniStatement.Shape) :
    (registryOf sh cc.logN).lookup (RecStatement.layoutWords cc.logN).2.2 = some (.pi2 lS) := by
  rw [registry_eq, List.cons_append, lookup_cons_ne _ _ _ _ ls_ne_lw, List.cons_append,
    lookup_cons_ne _ _ _ _ ls_ne_lq, List.cons_append, lookup_cons_self]

theorem lookup_map_self (f : List UInt8 → Opener) :
    ∀ (ws : List (List UInt8)) (a : List UInt8) (y : Opener), (ws.map fun w => (w, f w)).lookup a = some y → y = f a
  | [], a, y, h => by simp at h
  | w :: ws, a, y, h => by
    by_cases hw : a = w
    · subst hw
      rw [List.map_cons, lookup_cons_self] at h
      exact (Option.some.inj h).symm
    · rw [List.map_cons, lookup_cons_ne _ _ _ _ hw] at h
      exact lookup_map_self f ws a y h

/-- **A word of first byte `0x15` is registered, if at all, with π1's opener at its variables.** -/
theorem lookup_pi1 (sh : UniStatement.Shape) (a : List UInt8) (ha : a.head? = some 21) (y : Opener)
    (h : (registryOf sh cc.logN).lookup a = some y) : y = .pi1 (UniStatement.layoutWordVars a) := by
  have hp : ∀ (code m : ℕ) (L : PcsQuotient.Layout), a ≠ layoutWord code m L := fun code m L ↦
    ne_of_head (by rw [ha, pi2LayoutWord_head]; decide)
  rw [registry_eq, layoutWords_cc] at h
  simp only [List.cons_append] at h
  rw [lookup_cons_ne _ _ _ _ (hp _ _ _), lookup_cons_ne _ _ _ _ (hp _ _ _), lookup_cons_ne _ _ _ _ (hp _ _ _)] at h
  exact lookup_map_self _ _ a y h

/-! ## π2's six calls -/

theorem pcsCalls_cc (pi1 : List (List CallWord)) (sr : List UInt8) (stream : Array UInt8)
    (r : RecStatement.Reduced) :
    pcsCalls cc pi1 sr stream r = pi1.map (·.map (callWord cc.reads stream r)) ++
      [[streamWord stream 472, (RecStatement.layoutWords cc.logN).1, UniStatement.numberWord 1] ++
          claimWords r.witness,
        [rootWordOfBytes sr, (RecStatement.layoutWords cc.logN).2.2, UniStatement.numberWord 1] ++
          claimWords r.setup,
        [streamWord stream 504, (RecStatement.layoutWords cc.logN).2.1, UniStatement.numberWord 2] ++
          claimWords r.quotient ++ claimWords r.sum] := by
  have h1 : rootsAt cc.reads = [0, 32, 472, 504] := by decide
  have h2 : rootReads cc.reads = 2 := by decide
  unfold pcsCalls
  rw [h1, h2]
  rfl

/-- π1's calls' layout words (`Data.pi1Calls`' constants). -/
def pi1Lay (k : ℕ) : List UInt8 :=
  if k = 0 then hexBytes "1513121212121112000000000000000000000000000055011b00000006220000"
  else if k = 1 then hexBytes "1513121212121112000000000000000000000000000055021b00000006810003"
  else hexBytes "1513121212121112000000000000000000000000000055031800000000a00000"

/-- π1's calls' count word. -/
def hexOne : List UInt8 := hexBytes "0000000000000000000000000000000000000000000000000000000000000001"

theorem pi1Lay_head (k : ℕ) (hk : k < 3) : (pi1Lay k).head? = some 21 := by
  interval_cases k <;> decide

theorem pi1Lay_vars (k : ℕ) (hk : k < 3) : UniStatement.layoutWordVars (pi1Lay k) = pi1Vars k := by
  interval_cases k <;> decide

theorem hexOne_count : countOfWord hexOne = some 1 := by decide

theorem countOfWord_numberWord_two : countOfWord (UniStatement.numberWord 2) = some 2 := by decide

section Pi1

variable (D : RecDeployment) (hc : D.pi1Calls = Data.pi1Calls)
include hc

theorem pi1Words_length (π : P2Pf) (ch : List (List E)) : (pi1Words D π ch).length = 3 := by
  rw [pi1Words, hc]
  rfl

theorem pi1Words_lay (π : P2Pf) (ch : List (List E)) (k : ℕ) (hk : k < 3) :
    ((pi1Words D π ch).getD k []).getD 1 [] = pi1Lay k := by
  rw [pi1Words, hc]
  interval_cases k <;> rfl

theorem pi1Words_countWord (π : P2Pf) (ch : List (List E)) (k : ℕ) (hk : k < 3) :
    ((pi1Words D π ch).getD k []).getD 2 [] = hexOne := by
  rw [pi1Words, hc]
  interval_cases k <;> rfl

theorem pi1Words_head (π : P2Pf) (ch : List (List E)) (k : ℕ) (hk : k < 3) :
    ((pi1Words D π ch).getD k []).head? = ((pi1Words D π []).getD k []).head? := by
  rw [pi1Words, pi1Words, hc]
  interval_cases k <;> rfl

end Pi1

theorem headD_of_head? {α : Type} {l : List α} {a d : α} (h : l.head? = some a) : l.headD d = a := by
  cases l with
  | nil => simp at h
  | cons b l => simpa using h

/-- **π1's call `k`**: it does not decode (and rejects), or it is F2's opening with the Statement's early stop on π1's
plain layout of its variables, on the composed opening's input. -/
theorem pi1Open (D : RecDeployment) (hD : RecDeployment.Real D) (π : P2Pf) (ch : List (List E)) (k : ℕ)
    (hk : k < 3) (p : Compile.Proof) :
    pcsOpenAt Common.queryPermutation (registryOf D.pi1.shape cc.logN) ((pi1Words D π ch).getD k []) p =
        pure false ∨
      pcsOpenAt Common.queryPermutation (registryOf D.pi1.shape cc.logN) ((pi1Words D π ch).getD k []) p =
        simulateQ keccakCallsOverQueryPermutation
          (Soundness.ourVerifierEarly (sh1 k).L (sh1 k).R ((ofB (pi1Root D π k), cl1 D k π ch), p)) := by
  cases hd : decodeWith (registryOf D.pi1.shape cc.logN) ((pi1Words D π ch).getD k []) with
  | none =>
    left
    unfold pcsOpenAt
    rw [hd]
  | some x =>
    right
    obtain ⟨root, op, cs⟩ := x
    have hl := lookup_of_decodeWith _ _ _ hd
    rw [pi1Words_lay D hD.2.1 π ch k hk] at hl
    have hop : op = .pi1 (pi1Vars k) := by
      have := lookup_pi1 _ _ (pi1Lay_head k hk) _ hl
      rw [pi1Lay_vars k hk] at this
      exact this
    subst hop
    obtain ⟨r0, hr0, hroot⟩ := root_of_decodeWith _ _ _ hd
    obtain ⟨⟨kk, hkk, hlen⟩, hpts⟩ := decodeWith_shape _ _ _ hd
    rw [pi1Words_countWord D hD.2.1 π ch k hk, hexOne_count] at hkk
    cases hkk
    have hcl : (cl1 D k π ch).claims = cs.map Bridge.claimTr := by
      unfold cl1 pi1Claims pi1Dec
      rw [hd]
      refine Bridge.toStmt_claims_of (by simp at hlen ⊢; omega) fun c hc => ?_
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact hpts c' hc'
    have hroot' : ofB (pi1Root D π k) = root := by
      unfold pi1Root
      rw [Bridge.ofB_toB, headD_of_head? (by rw [← pi1Words_head D hD.2.1 π ch k hk]; exact hr0), ← hroot]
    unfold pcsOpenAt
    rw [hd]
    show UniStatement.pcsOpenWith Common.queryPermutation (pi1Vars k) root cs p = _
    rw [hroot', UniSound.pcsOpen_eq_early (pi1Vars k) (pi1Vars_lo k) (pi1Vars_hi k) root (cl1 D k π ch) cs hcl p]

/-! ## π2's three calls -/

theorem msgK_p2View_0 (π : P2Pf) :
    msgK p2View π 0 = (some (toB (UniStatement.rootOf (UniSound.halvesAt π.proof.stream 472))), []) := rfl

theorem msgK_p2View_1 (π : P2Pf) :
    msgK p2View π 1 = (some (toB (UniStatement.rootOf (UniSound.halvesAt π.proof.stream 504))), []) := rfl

/-- **`W`'s call** is F2's opening with the Statement's early stop on `W`'s layout, on the composed opening's input. -/
theorem wOpen (D : RecDeployment) (π : P2Pf) (ch : List (List E)) (hlen : π.proof.stream.size = sLen) :
    pcsOpenAt Common.queryPermutation (registryOf D.pi1.shape cc.logN)
        ([streamWord π.proof.stream 472, (RecStatement.layoutWords cc.logN).1, UniStatement.numberWord 1] ++
          claimWords (p2Reduced π ch).witness) π.proof.w =
      simulateQ keccakCallsOverQueryPermutation (Soundness.ourVerifierEarly shW.L shW.R
        (WhirOp.input p2View (⟨shW, clW, fun π => π.proof.w, .round 0 stackOf⟩ : WhirOp P2Pf E Stk) π ch)) := by
  have hdec := decodeWith_mk (registryOf D.pi1.shape cc.logN) (streamWord π.proof.stream 472)
    (RecStatement.layoutWords cc.logN).1 (.pi2 lW) [(p2Reduced π ch).witness]
    (streamWord_length _ _ (by rw [hlen]; decide)) (lookup_lw _) (by simp) Pi1Decode.countOfWord_numberWord_one
    (fun c hc => by
      rw [List.mem_singleton] at hc
      subst hc
      exact p2Out_witnessPoint_length π ch)
  have e : [streamWord π.proof.stream 472, (RecStatement.layoutWords cc.logN).1, UniStatement.numberWord 1] ++
      claimWords (p2Reduced π ch).witness =
      [streamWord π.proof.stream 472, (RecStatement.layoutWords cc.logN).1,
        UniStatement.numberWord [(p2Reduced π ch).witness].length] ++
        ([(p2Reduced π ch).witness].map claimWords).flatten := by simp
  have hin : WhirOp.input p2View (⟨shW, clW, fun π => π.proof.w, .round 0 stackOf⟩ : WhirOp P2Pf E Stk) π ch =
      ((rootOfWord (streamWord π.proof.stream 472), clW π ch), π.proof.w) := by
    show ((ofB (((msgK p2View π 0).1).getD (Vector.replicate 32 0)), clW π ch), π.proof.w) = _
    rw [msgK_p2View_0]
    simp only [Option.getD_some, Bridge.ofB_toB]
    rw [rootOfWord_streamWord _ _ (by rw [hlen]; decide)]
  rw [e, hin]
  unfold pcsOpenAt
  rw [hdec]
  show PcsQuotient.openingWith Common.queryPermutation lW _ _ π.proof.w = _
  rw [Bridge.openingWith_eq_ourVerifier' Common.queryPermutation lW shW.L layoutTr_W (Or.inl rfl) shW.adm _
    (clW π ch) _ (by rw [clW_claims]; rfl) π.proof.w, Bridge.keccakCallsWith_queryPermutation]

/-- **The setup's call**, on the setup's layout. -/
theorem sOpen (D : RecDeployment) (π : P2Pf) (ch : List (List E)) :
    pcsOpenAt Common.queryPermutation (registryOf D.pi1.shape cc.logN)
        ([rootWordOfBytes (digestBytes (p2Roots π).pi2), (RecStatement.layoutWords cc.logN).2.2,
          UniStatement.numberWord 1] ++ claimWords (p2Reduced π ch).setup) π.proof.setup =
      simulateQ keccakCallsOverQueryPermutation (Soundness.ourVerifierEarly shS.L shS.R
        (WhirOp.input p2View (⟨shS, clS, fun π => π.proof.setup, .setup (fun π => π.roots.2) (col0 _)⟩ :
          WhirOp P2Pf E Stk) π ch)) := by
  have hdec := decodeWith_mk (registryOf D.pi1.shape cc.logN) (rootWordOfBytes (digestBytes (p2Roots π).pi2))
    (RecStatement.layoutWords cc.logN).2.2 (.pi2 lS) [(p2Reduced π ch).setup]
    (rootWordOfBytes_length _) (lookup_ls _) (by simp) Pi1Decode.countOfWord_numberWord_one
    (fun c hc => by
      rw [List.mem_singleton] at hc
      subst hc
      exact p2Out_setupPoint_length π ch)
  have e : [rootWordOfBytes (digestBytes (p2Roots π).pi2), (RecStatement.layoutWords cc.logN).2.2,
        UniStatement.numberWord 1] ++ claimWords (p2Reduced π ch).setup =
      [rootWordOfBytes (digestBytes (p2Roots π).pi2), (RecStatement.layoutWords cc.logN).2.2,
        UniStatement.numberWord [(p2Reduced π ch).setup].length] ++
        ([(p2Reduced π ch).setup].map claimWords).flatten := by simp
  rw [e]
  unfold pcsOpenAt
  rw [hdec, rootOfWord_rootWordOfBytes_digestBytes]
  show PcsQuotient.openingWith Common.queryPermutation lS _ _ π.proof.setup = _
  rw [Bridge.openingWith_eq_ourVerifier' Common.queryPermutation lS shS.L layoutTr_S (Or.inl rfl) shS.adm _
    (clS π ch) _ (by rw [clS_claims]; rfl) π.proof.setup, Bridge.keccakCallsWith_queryPermutation]
  rfl

/-- **`Q`'s call** (its two claims), on `Q`'s layout. -/
theorem qOpen (D : RecDeployment) (π : P2Pf) (ch : List (List E)) (hlen : π.proof.stream.size = sLen) :
    pcsOpenAt Common.queryPermutation (registryOf D.pi1.shape cc.logN)
        ([streamWord π.proof.stream 504, (RecStatement.layoutWords cc.logN).2.1, UniStatement.numberWord 2] ++
          claimWords (p2Reduced π ch).quotient ++ claimWords (p2Reduced π ch).sum) π.proof.q =
      simulateQ keccakCallsOverQueryPermutation (Soundness.ourVerifierEarly shQ.L shQ.R
        (WhirOp.input p2View (⟨shQ, clQ, fun π => π.proof.q, .round 1 stackOf⟩ : WhirOp P2Pf E Stk) π ch)) := by
  have hdec := decodeWith_mk (registryOf D.pi1.shape cc.logN) (streamWord π.proof.stream 504)
    (RecStatement.layoutWords cc.logN).2.1 (.pi2 lQ) [(p2Reduced π ch).quotient, (p2Reduced π ch).sum]
    (streamWord_length _ _ (by rw [hlen]; decide)) (lookup_lq _) (by simp) countOfWord_numberWord_two
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact p2Out_quotientPoint_length π ch
      · exact p2Out_sumPoint_length π ch)
  have e : [streamWord π.proof.stream 504, (RecStatement.layoutWords cc.logN).2.1, UniStatement.numberWord 2] ++
      claimWords (p2Reduced π ch).quotient ++ claimWords (p2Reduced π ch).sum =
      [streamWord π.proof.stream 504, (RecStatement.layoutWords cc.logN).2.1,
        UniStatement.numberWord [(p2Reduced π ch).quotient, (p2Reduced π ch).sum].length] ++
        ([(p2Reduced π ch).quotient, (p2Reduced π ch).sum].map claimWords).flatten := by simp
  have hin : WhirOp.input p2View (⟨shQ, clQ, fun π => π.proof.q, .round 1 stackOf⟩ : WhirOp P2Pf E Stk) π ch =
      ((rootOfWord (streamWord π.proof.stream 504), clQ π ch), π.proof.q) := by
    show ((ofB (((msgK p2View π 1).1).getD (Vector.replicate 32 0)), clQ π ch), π.proof.q) = _
    rw [msgK_p2View_1]
    simp only [Option.getD_some, Bridge.ofB_toB]
    rw [rootOfWord_streamWord _ _ (by rw [hlen]; decide)]
  rw [e, hin]
  unfold pcsOpenAt
  rw [hdec]
  show PcsQuotient.openingWith Common.queryPermutation lQ _ _ π.proof.q = _
  rw [Bridge.openingWith_eq_ourVerifier' Common.queryPermutation lQ shQ.L layoutTr_Q (Or.inl rfl) shQ.adm _
    (clQ π ch) _ (by rw [clQ_claims]; rfl) π.proof.q, Bridge.keccakCallsWith_queryPermutation]

/-! ## The bridge -/

theorem restC_ok (D : RecDeployment) (roots : RecSetupRoots) (proof : RecProof) (r : RecStatement.Reduced)
    (h6 : (pcsCalls cc (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) proof.stream
      r).length = 6) :
    restC Common.queryPermutation D roots proof (true, .ok r) =
      forIn ((pcsCalls cc (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) proof.stream r).zip
          proof.openings) true (fun x s => do
        let b ← pcsOpenAt Common.queryPermutation (registryOf D.pi1.shape cc.logN) x.1 x.2
        pure (ForInStep.yield (s && b))) >>= fun ok =>
      pure (ok, pcsCalls cc (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) proof.stream r) := by
  simp only [restC, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h6, ne_eq, not_true_eq_false]

theorem list3_eq {α : Type} (l : List α) (h : l.length = 3) (d : α) : l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [_, _, _], _ => rfl

theorem seqAndK_nil {γ : Type} (ok : Bool) (kf : Bool → OracleComp Common.RandomPermutationOracles γ) :
    seqAndK [] ok kf = kf ok := rfl

theorem seqAndK_false_zero (Ps : List (OracleComp Common.RandomPermutationOracles Bool))
    (calls : List (List (List UInt8))) (s : Common.PermutationEdges LeanVM.Semantics.KeccakState) :
    Pr{let x ← (simulateQ Common.lazyRandomPermutationOracles
      (seqAndK Ps false fun ok => pure (ok, calls))).run' s}[x.1 = true] = 0 :=
  Soundness.zero_of_support _ _ _ (fun x hx hx1 => by
    have h := seqAndK_false _ Ps x hx
    rw [support_pure, Set.mem_singleton_iff] at h
    rw [h] at hx1
    exact Bool.false_ne_true hx1) s

/-- **Per challenges**: the contract past the run accepts at most as often as the six composed openings all do, with
the check. -/
theorem step_ch (D : RecDeployment) (hD : RecDeployment.Real D) (π : P2Pf) (hlen : π.proof.stream.size = sLen)
    (ch : List (List E))
    (hch : ch.length = 3 ∧ (ch.getD 0 []).length = 3 ∧ (ch.getD 1 []).length = 1 ∧ (ch.getD 2 []).length = 1)
    (s : Common.PermutationEdges LeanVM.Semantics.KeccakState) :
    Pr{let x ← (simulateQ Common.lazyRandomPermutationOracles (restC Common.queryPermutation D (p2Roots π) π.proof
        ((p2Reduced π ch).out.all != 0,
          (Except.ok (p2Reduced π ch) : Except UniStatement.UniError RecStatement.Reduced)))).run' s}[x.1 = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles (simulateQ keccakCallsOverQueryPermutation
          (opsRun p2View (p2Ops D) π ch >>= fun b => pure (ch, b)))).run' s}[
        p2Check π v.1 ∧ ∀ k < (p2Ops D).length, v.2.getD k false = true] := by
  by_cases hall : (p2Reduced π ch).out.all = 0
  · have hf : ((p2Reduced π ch).out.all != 0) = false := by simp [hall]
    rw [hf]
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun x hx hx1 => ?_) s)).trans zero_le
    rw [restC_reject D (p2Roots π) π.proof _ rfl x hx] at hx1
    exact Bool.false_ne_true hx1
  have ht : ((p2Reduced π ch).out.all != 0) = true := by simp [hall]
  have hcheck : p2Check π ch := ⟨hlen, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2, hall⟩
  have hcalls : pcsCalls cc (pi1CallsWith D.pi1Calls (p2Roots π).pi1.bytecode) (digestBytes (p2Roots π).pi2)
      π.proof.stream (p2Reduced π ch) =
      [(pi1Words D π ch).getD 0 [], (pi1Words D π ch).getD 1 [], (pi1Words D π ch).getD 2 [],
        [streamWord π.proof.stream 472, (RecStatement.layoutWords cc.logN).1, UniStatement.numberWord 1] ++
          claimWords (p2Reduced π ch).witness,
        [rootWordOfBytes (digestBytes (p2Roots π).pi2), (RecStatement.layoutWords cc.logN).2.2,
          UniStatement.numberWord 1] ++ claimWords (p2Reduced π ch).setup,
        [streamWord π.proof.stream 504, (RecStatement.layoutWords cc.logN).2.1, UniStatement.numberWord 2] ++
          claimWords (p2Reduced π ch).quotient ++ claimWords (p2Reduced π ch).sum] := by
    rw [pcsCalls_cc]
    rw [show (pi1CallsWith D.pi1Calls (p2Roots π).pi1.bytecode).map
        (·.map (callWord cc.reads π.proof.stream (p2Reduced π ch))) = pi1Words D π ch from rfl]
    rw [list3_eq (pi1Words D π ch) (pi1Words_length D hD.2.1 π ch) []]
    rfl
  have h6 : (pcsCalls cc (pi1CallsWith D.pi1Calls (p2Roots π).pi1.bytecode) (digestBytes (p2Roots π).pi2)
      π.proof.stream (p2Reduced π ch)).length = 6 := by
    rw [hcalls]
    rfl
  rw [ht, restC_ok D (p2Roots π) π.proof _ h6, forIn_seqAndK, hcalls]
  simp only [RecProof.openings, List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil]
  simp only [p2Ops]
  -- π1's `C1`
  rw [seqAndK_cons, sim_opsRun_cons2]
  refine step_le _ _ _ _ _ _ _ _ (pi1Open D hD π ch 0 (by decide) π.proof.c1)
    (fun s => seqAndK_false_zero _ _ s) (fun s => ?_) s
  -- π1's `C2`
  rw [seqAndK_cons, sim_opsRun_cons2]
  refine step_le _ _ _ _ _ _ _ _ (pi1Open D hD π ch 1 (by decide) π.proof.c2)
    (fun s => seqAndK_false_zero _ _ s) (fun s => ?_) s
  -- π1's `F`
  rw [seqAndK_cons, sim_opsRun_cons2]
  refine step_le _ _ _ _ _ _ _ _ (pi1Open D hD π ch 2 (by decide) π.proof.f)
    (fun s => seqAndK_false_zero _ _ s) (fun s => ?_) s
  -- `W`
  rw [seqAndK_cons, sim_opsRun_cons2]
  refine step_le _ _ _ _ _ _ _ _ (Or.inr (wOpen D π ch hlen))
    (fun s => seqAndK_false_zero _ _ s) (fun s => ?_) s
  -- the setup
  rw [seqAndK_cons, sim_opsRun_cons2]
  refine step_le _ _ _ _ _ _ _ _ (Or.inr (sOpen D π ch))
    (fun s => seqAndK_false_zero _ _ s) (fun s => ?_) s
  -- `Q`
  rw [seqAndK_cons, sim_opsRun_cons2]
  refine step_le _ _ _ _ _ _ _ _ (Or.inr (qOpen D π ch hlen))
    (fun s => seqAndK_false_zero _ _ s) (fun s => ?_) s
  -- every opening accepted
  rw [seqAndK_nil, sim_opsRun_nil2, simulateQ_pure]
  refine Soundness.le_pure _ _ _ _ _ (fun _ => ⟨hcheck, fun k hk => ?_⟩) s
  have hk6 : k < 6 := hk
  interval_cases k <;> rfl

/-- **THE VERIFIER BRIDGE** at the real deployment, from the walk. -/
theorem pi2VerifierBridge (D : RecDeployment) (hD : RecDeployment.Real D) (hW : Pi2Walk) (hR : Pi2WalkReject) :
    Pi2VerifierBridge D := by
  intro π s
  rw [contractRest_eq Common.queryPermutation D (p2Roots π) π.iv.toList π.input π.proof (hD.1 _)]
  by_cases hlen : π.proof.stream.size = sLen
  swap
  · -- a stream of another length: the run rejects
    refine (le_of_eq (Soundness.zero_of_support _ _ _ (fun x hx hx1 => ?_) s)).trans zero_le
    rw [mem_support_bind_iff] at hx
    obtain ⟨p, hp, hx⟩ := hx
    rw [support_map] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    rw [restC_reject D (p2Roots π) π.proof _ (hR π hlen o ho) x hx] at hx1
    exact Bool.false_ne_true hx1
  -- the run is the chain; both sides run it first
  rw [hW Common.queryPermutation π hlen, bind_map_left, simulateQ_verU2]
  exact UniSound.mono_bind_supp _ _ _ _ _ _
    (fun ch hch s => step_ch D hD π hlen ch (chain_lengths π ch _ hch) s) s

end RecCompose

/-- info: 'RecCompose.pi2VerifierBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2VerifierBridge
