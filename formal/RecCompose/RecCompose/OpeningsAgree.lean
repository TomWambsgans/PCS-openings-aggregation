-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Couplings
import RecCompose.CallsPure
import RecCompose.CompleteCouplings

/-!
# π1-rec3's verifier's openings are the contract's: `Pi1OpeningsAgree`, proved

`pi1OpeningsAgree`: on a stream π1-rec3's graph accepts with the contract's π1 openings `ops`, off the merge hazard (the
graph being π1-rec3's verifier there, `Pi1GraphIsVerifier`), π1-rec3's verifier at Keccak-f[1600] with the recursive
proof's three π1 opening proofs is, as a computation, the contract's three π1 openings `openSeq` of `ops`.

* the graph's outputs are the verifier's (`Pi1GraphIsVerifier`): the run accepts (its zeros vanish), and its calls are
  `UniStatement.pcsCalls`' words of its openings (no matrices', `Pi1RunShape`), three point claims in `commitments`
  order (**`Pi1RunOpenings`**, named), which decode (`Pi1Decode.decodePi1Call_point`) to the verifier's openings, so the
  claims have their layout words' variables; `Pi1GraphAccepts` makes `ops`' layouts and claims these, and `C1`'s and
  `C2`'s roots theirs (`Pi1Decode.rootOfWord_rootWord`, the halves' top limbs zero by `Pi1RunShape`);
* the setup's root in `ops` is the contract's decoding of the setup's root word `rootWordOfBytes (digestBytes F)`, which
  is `F` (`rootOfWord_rootWordOfBytes_digestBytes`), when π1's third call names its root as a constant
  (**`Pi1CallsShape`**, named; `Data.pi1Calls`' `pi1CallsShape_data`);
* each layout word is registered with π1's opener at its variables (`registryAt_lookup`: π2's layout words begin with
  `"pi2"`, π1's with the shape's bytes, and π1's three differ by their codes).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## The named facts -/

/-- **π1-rec3's run's openings** (a fact of `UniStatement.reduceWithFs`'s code, named here, not proved): a run of π1-rec3's
verifier at the reference shape that returns a result has three point claims, without a bit-slice claim, in
`commitments` order (`batchFs` at the point-claim ABI, one opening per commitment; the walked terminal sends no
bit-slice combination). -/
def Pi1RunOpenings : Prop :=
  ∀ (iv publicInput : List UInt8) (stream : Array UInt8) (r : UniStatement.Reduced),
    (UniStatement.runFs UniStatement.reference iv publicInput stream (.flock UniStatement.flockMain) .point .rec3
      true).result = .ok r →
      ∃ pt1 v1 pt2 v2 pt3 v3, r.openings = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none),
        (.setup, .point pt3 v3 none)]

/-- **π1's calls' shape**: three calls, the third (the setup's) naming its root as a constant (which the contract replaces
by the setup's root word, `pi1CallsWith`). -/
def Pi1CallsShape (D : RecDeployment) : Prop :=
  D.pi1Calls.length = 3 ∧ ∃ w rest, D.pi1Calls.getD 2 [] = CallWord.const w :: rest

/-- The real deployment's calls have that shape. -/
theorem pi1CallsShape_data (D : RecDeployment) (h : D.pi1Calls = Data.pi1Calls) : Pi1CallsShape D := by
  rw [Pi1CallsShape, h]
  exact ⟨rfl, _, _, rfl⟩

/-! ## Bytes -/

/-- A digest's bytes read back. -/
theorem digestOfBytes32_digestBytes (d : Digest) : UniStatement.digestOfBytes32 (digestBytes d) = d := by
  have l8 : ∀ u : UInt64, (wordBytes u).length = 8 := fun u ↦ by simp [wordBytes]
  have hw : ∀ (u : UInt64) {k : ℕ}, k < 8 → (wordBytes u).getD k 0 = (u >>> (8 * k).toUInt64).toUInt8 := by
    intro u k hk
    simp [wordBytes, List.getD_eq_getElem?_getD, hk]
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [a, b, c, e], _ =>
    have hb : digestBytes ⟨⟨[a, b, c, e]⟩, rfl⟩ = wordBytes a ++ (wordBytes b ++ (wordBytes c ++ wordBytes e)) := by
      simp [digestBytes]
    unfold UniStatement.digestOfBytes32
    rw [hb]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn]
    interval_cases j
    · refine Pi1Decode.le_fold a _ fun k hk ↦ ?_
      rw [show 8 * 0 + k = k by ring, Pi1Decode.getD_append_left (by rw [l8]; exact hk), hw a hk]
    · refine Pi1Decode.le_fold b _ fun k hk ↦ ?_
      rw [show 8 * 1 + k = (wordBytes a).length + k by rw [l8], Pi1Decode.getD_append_right,
        Pi1Decode.getD_append_left (by rw [l8]; exact hk), hw b hk]
    · refine Pi1Decode.le_fold c _ fun k hk ↦ ?_
      rw [show 8 * 2 + k = (wordBytes a).length + ((wordBytes b).length + k) by rw [l8, l8]; ring,
        Pi1Decode.getD_append_right, Pi1Decode.getD_append_right, Pi1Decode.getD_append_left (by rw [l8]; exact hk),
        hw c hk]
    · refine Pi1Decode.le_fold e _ fun k hk ↦ ?_
      rw [show 8 * 3 + k = (wordBytes a).length + ((wordBytes b).length + ((wordBytes c).length + k)) by
          rw [l8, l8, l8]; ring,
        Pi1Decode.getD_append_right, Pi1Decode.getD_append_right, Pi1Decode.getD_append_right, hw e hk]

/-- `root_word` is an involution on 32 bytes. -/
theorem rootWordOfBytes_rootWordOfBytes (b : List UInt8) (hb : b.length = 32) :
    rootWordOfBytes (rootWordOfBytes b) = b := by
  have hA : (b.take 16).reverse.length = 16 := by simp [hb]
  have hB : (b.drop 16).take 16 = b.drop 16 := List.take_of_length_le (by simp [hb])
  have hB' : ((b.drop 16).take 16).reverse.length ≤ 16 := by simp
  unfold rootWordOfBytes
  rw [List.take_left' hA, List.drop_left' hA, List.take_of_length_le hB', List.reverse_reverse, List.reverse_reverse,
    hB, List.take_append_drop]

/-- **The contract's setup root word names the setup's root.** -/
theorem rootOfWord_rootWordOfBytes_digestBytes (f : Digest) : rootOfWord (rootWordOfBytes (digestBytes f)) = f := by
  unfold rootOfWord
  rw [rootWordOfBytes_rootWordOfBytes _ (Pi1Decode.length_digestBytes f), digestOfBytes32_digestBytes]

/-! ## The registry -/

/-- π2's layout words begin with `"pi2"`. -/
theorem pi2LayoutWord_head (code m : ℕ) (L : PcsQuotient.Layout) :
    (RecStatement.layoutWord code m L).head? = some 112 := by
  have h : "pi2".toUTF8.toList = [112, 105, 50] := by decide +kernel
  unfold RecStatement.layoutWord
  rw [h]
  rfl

/-- π1's layout words begin with the shape's first byte. -/
theorem pi1LayoutWord_head (s : UniStatement.Shape) (code vars placed : ℕ) :
    (UniStatement.layoutWord s code vars placed).head? = some s.logMemory.toUInt8 := rfl

/-- π1's three layout words at the reference shape. -/
abbrev w1 (i : ℕ) : List UInt8 := (UniStatement.layoutWords UniStatement.reference).getD i []

theorem w1_head (i : ℕ) (hi : i < 3) : (w1 i).head? = some 21 := by
  obtain ⟨⟨a0, b0, hw0⟩, ⟨a1, b1, hw1⟩, ⟨a2, b2, hw2⟩⟩ := Pi1Decode.layoutWords_getD UniStatement.reference
  interval_cases i
  · rw [w1, hw0, pi1LayoutWord_head]; rfl
  · rw [w1, hw1, pi1LayoutWord_head]; rfl
  · rw [w1, hw2, pi1LayoutWord_head]; rfl

theorem w1_codes : Pi1Decode.codeOf (w1 0) = 0x5501 ∧ Pi1Decode.codeOf (w1 1) = 0x5502 ∧
    Pi1Decode.codeOf (w1 2) = 0x5503 := by
  obtain ⟨⟨a0, b0, hw0⟩, ⟨a1, b1, hw1⟩, ⟨a2, b2, hw2⟩⟩ := Pi1Decode.layoutWords_getD UniStatement.reference
  refine ⟨?_, ?_, ?_⟩
  · rw [w1, hw0, Pi1Decode.codeOf_layoutWord]; decide
  · rw [w1, hw1, Pi1Decode.codeOf_layoutWord]; decide
  · rw [w1, hw2, Pi1Decode.codeOf_layoutWord]; decide

theorem w1_length (i : ℕ) (hi : i < 3) : (w1 i).length = 32 := by
  obtain ⟨⟨a0, b0, hw0⟩, ⟨a1, b1, hw1⟩, ⟨a2, b2, hw2⟩⟩ := Pi1Decode.layoutWords_getD UniStatement.reference
  interval_cases i
  · rw [w1, hw0]; exact Pi1Decode.length_layoutWord _ _ _ _
  · rw [w1, hw1]; exact Pi1Decode.length_layoutWord _ _ _ _
  · rw [w1, hw2]; exact Pi1Decode.length_layoutWord _ _ _ _

theorem lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α] (a k : α) (v : β) (l : List (α × β)) (h : a ≠ k) :
    ((k, v) :: l).lookup a = l.lookup a := by
  simp [List.lookup, beq_eq_false_iff_ne.mpr h]

theorem lookup_cons_self {α β : Type} [BEq α] [LawfulBEq α] (a : α) (v : β) (l : List (α × β)) :
    ((a, v) :: l).lookup a = some v := by
  simp [List.lookup]

theorem ne_of_head {a b : List UInt8} (h : a.head? ≠ b.head?) : a ≠ b := fun e ↦ h (e ▸ rfl)

theorem ne_of_codeOf {a b : List UInt8} (h : Pi1Decode.codeOf a ≠ Pi1Decode.codeOf b) : a ≠ b := fun e ↦ h (e ▸ rfl)

/-- **π1's layout words are registered with π1's opener, at their variables**, at the reference shape. -/
theorem registryAt_lookup (D : RecDeployment) (roots : RecSetupRoots) (hD : D.pi1.shape = UniStatement.reference)
    (i : ℕ) (hi : i < 3) :
    (registryAt D roots).lookup (w1 i) = some (.pi1 (UniStatement.layoutWordVars (w1 i))) := by
  have hp : ∀ (code m : ℕ) (L : PcsQuotient.Layout), w1 i ≠ RecStatement.layoutWord code m L := fun code m L ↦
    ne_of_head (by rw [w1_head i hi, pi2LayoutWord_head]; decide)
  have htake : (UniStatement.layoutWords UniStatement.reference).take 3 = [w1 0, w1 1, w1 2] := rfl
  unfold registryAt registryOf
  rw [hD]
  simp only [RecStatement.layoutWords, List.cons_append, List.nil_append]
  rw [lookup_cons_ne _ _ _ _ (hp _ _ _), lookup_cons_ne _ _ _ _ (hp _ _ _), lookup_cons_ne _ _ _ _ (hp _ _ _), htake]
  obtain ⟨c0, c1, c2⟩ := w1_codes
  simp only [List.map_cons, List.map_nil]
  interval_cases i
  · rw [lookup_cons_self]
  · rw [lookup_cons_ne _ _ _ _ (ne_of_codeOf (by rw [c0, c1]; decide)), lookup_cons_self]
  · rw [lookup_cons_ne _ _ _ _ (ne_of_codeOf (by rw [c0, c2]; decide)),
      lookup_cons_ne _ _ _ _ (ne_of_codeOf (by rw [c1, c2]; decide)), lookup_cons_self]

/-! ## Decoding -/

/-- **A point claim whose point has another number of coordinates than its layout word's variables does not decode.** -/
theorem decodePi1Call_point_none (root word : List UInt8) (pt : List E) (v : E) (hr : root.length = 32)
    (hw : word.length = 32) (hpt : pt.length ≠ UniStatement.layoutWordVars word) :
    decodePi1Call (UniStatement.openingWords root word (.point pt v none)) = none := by
  set W : List (List UInt8) := [root, word, UniStatement.numberWord 1] ++
    (pt.map UniStatement.elementWord ++ [UniStatement.elementWord v]) with hW
  have hcall : UniStatement.openingWords root word (.point pt v none) = W.flatten := by
    simp [UniStatement.openingWords, hW, List.flatten_append, List.flatMap, List.append_assoc]
  have hlen : ∀ w ∈ W, w.length = 32 := by
    intro w hw'
    simp only [hW, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hw'
    rcases hw' with (rfl | rfl | rfl) | ⟨x, -, rfl⟩ | rfl <;> simp [hr, hw]
  have hWl : W.length = 3 + (pt.length + 1) := by simp [hW]; omega
  have hflen : W.flatten.length = 32 * W.length := Pi1Decode.length_flatten_32 W hlen
  unfold decodePi1Call
  rw [hcall, ite_eq_right (by rw [hflen]; omega), Pi1Decode.chunks_flatten W hlen]
  have h0 : W.head? = some root := rfl
  have h1 : W[1]? = some word := rfl
  have h2 : W[2]? = some (UniStatement.numberWord 1) := rfl
  simp only [h0, h1, h2, Option.bind_eq_bind, Option.bind_some, Pi1Decode.countOfWord_numberWord_one, hWl]
  simp [hpt]

/-- A decoded point claim has its layout word's variables. -/
theorem decodePi1Call_point_length (root word : List UInt8) (pt : List E) (v : E) (hr : root.length = 32)
    (hw : word.length = 32) (x : Pi1Opening)
    (h : decodePi1Call (UniStatement.openingWords root word (.point pt v none)) = some x) :
    pt.length = UniStatement.layoutWordVars word := by
  by_contra hne
  rw [decodePi1Call_point_none root word pt v hr hw hne] at h
  exact absurd h (by simp)

/-- `mapM` in `Option` of three. -/
theorem mapM_three {α β : Type} (f : α → Option β) (a b c : α) (ys : List β)
    (h : [a, b, c].mapM f = some ys) : ∃ x y z, ys = [x, y, z] ∧ f a = some x ∧ f b = some y ∧ f c = some z := by
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.pure_def] at h
  cases ha : f a with
  | none => simp [ha] at h
  | some x =>
    cases hb : f b with
    | none => simp [ha, hb] at h
    | some y =>
      cases hc : f c with
      | none => simp [ha, hb, hc] at h
      | some z =>
        simp only [ha, hb, hc, Option.bind_some, Option.some.injEq] at h
        exact ⟨x, y, z, h.symm, rfl, rfl, rfl⟩

/-- `decodeWith`'s root is its first word read back. -/
theorem root_of_decodeWith (reg : List (List UInt8 × Opener)) (w : List (List UInt8))
    (x : Digest × Opener × List PcsQuotient.Claim) (h : decodeWith reg w = some x) :
    ∃ root, w.head? = some root ∧ x.1 = rootOfWord root := by
  unfold decodeWith at h
  cases hw0 : w.head? with
  | none => simp [hw0] at h
  | some root =>
    refine ⟨root, rfl, ?_⟩
    simp only [hw0, Option.bind_eq_bind, Option.bind_some] at h
    cases hw1 : w[1]? with
    | none => simp [hw1] at h
    | some layout =>
      simp only [hw1, Option.bind_some] at h
      cases hl : reg.lookup layout with
      | none => simp [hl] at h
      | some op =>
        simp only [hl, Option.bind_some] at h
        cases hw2 : w[2]? with
        | none => simp [hw2] at h
        | some cw =>
          simp only [hw2, Option.bind_some] at h
          cases hk : countOfWord cw with
          | none => simp [hk] at h
          | some k =>
            simp only [hk, Option.bind_some] at h
            split at h
            · exact absurd h (by simp)
            · cases hcl : claimsOfWords w k op.vars with
              | none => simp [hcl] at h
              | some cl =>
                simp only [hcl, Option.bind_some, Option.pure_def, Option.some.injEq] at h
                rw [← h]

/-! ## The theorem -/

/-- **`Pi1OpeningsAgree`**, at the reference shape, from π1-rec3's run's shape and openings and π1's calls' shape. -/
theorem pi1OpeningsAgree (D : RecDeployment) (hD : D.pi1.shape = UniStatement.reference) (hS : Pi1RunShape)
    (hO : Pi1RunOpenings) (hC : Pi1CallsShape D) : Pi1OpeningsAgree D := by
  intro hgv roots input proof s ops hops hga hz
  obtain ⟨out, gops, hout, hzs, -, hg, hlay, hroot⟩ := hga
  have hge := hgv LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots.pi1) input s hz
  have hiv : D.pi1IvAt roots.pi1 = pi1Iv UniStatement.reference D.pi1.programIv roots.pi1 := by
    unfold RecDeployment.pi1IvAt; rw [hD]
  rw [hiv] at hge hout
  set iv := pi1Iv UniStatement.reference D.pi1.programIv roots.pi1 with hivd
  set o := UniStatement.runFs UniStatement.reference iv input.toList s (.flock UniStatement.flockMain) .point
    .rec3 true with ho
  have hgo : RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph iv input.toList s =
      match o.result with
      | .ok r => some ⟨UniStatement.pcsCalls UniStatement.reference UniStatement.referenceRoots r,
          o.chan.zeros.toList, []⟩
      | .error _ => none := hge
  rw [hgo] at hout
  cases hres : o.result with
  | error e =>
    rw [hres] at hout
    exact absurd hout (by simp)
  | ok r =>
    rw [hres] at hout
    have hout' := (Option.some.inj hout).symm
    subst hout'
    obtain ⟨hmat, h11, h12, h21, h22⟩ := hS iv input.toList s r hres
    obtain ⟨pt1, v1, pt2, v2, pt3, v3, hro⟩ := hO iv input.toList s r hres
    -- The graph's calls, decoded.
    have hcalls : UniStatement.pcsCalls UniStatement.reference UniStatement.referenceRoots r =
        [UniStatement.openingWords (UniStatement.rootWord r.roots.1) (w1 0) (.point pt1 v1 none),
          UniStatement.openingWords (UniStatement.rootWord r.roots.2) (w1 1) (.point pt2 v2 none),
          UniStatement.openingWords (digestBytes UniStatement.referenceRoots.bytecode) (w1 2) (.point pt3 v3 none)] := by
      unfold UniStatement.pcsCalls
      rw [hro, hmat]
      simp only [List.map_cons, List.map_nil, List.append_nil]
    rw [hcalls] at hg
    obtain ⟨g0, g1, g2, hgops, hd0, hd1, hd2⟩ := mapM_three _ _ _ _ _ hg
    have hl1 := decodePi1Call_point_length _ _ _ _ (UniComplete.length_rootWord _) (w1_length 0 (by decide)) _ hd0
    have hl2 := decodePi1Call_point_length _ _ _ _ (UniComplete.length_rootWord _) (w1_length 1 (by decide)) _ hd1
    have hl3 := decodePi1Call_point_length _ _ _ _ (Pi1Decode.length_digestBytes _) (w1_length 2 (by decide)) _ hd2
    obtain ⟨c0, c1, c2⟩ := w1_codes
    rw [Pi1Decode.decodePi1Call_point _ _ _ _ (UniComplete.length_rootWord _) (w1_length 0 (by decide)) hl1, c0,
      Pi1Decode.rootOfWord_rootWord _ h11 h12] at hd0
    rw [Pi1Decode.decodePi1Call_point _ _ _ _ (UniComplete.length_rootWord _) (w1_length 1 (by decide)) hl2, c1,
      Pi1Decode.rootOfWord_rootWord _ h21 h22] at hd1
    simp only [show (0x5501 : ℕ) ≠ 0x5503 by decide, show (0x5502 : ℕ) ≠ 0x5503 by decide, ite_false,
      Option.some.injEq] at hd0 hd1
    -- The contract's openings.
    have hlen3 : ops.length = 3 := by
      have := congrArg List.length hlay
      simpa [hgops] using this.symm
    obtain ⟨o0, o1, o2, rfl⟩ : ∃ o0 o1 o2, ops = [o0, o1, o2] := by
      match ops, hlen3 with
      | [o0, o1, o2], _ => exact ⟨o0, o1, o2, rfl⟩
    rw [hgops] at hlay hroot
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlay
    obtain ⟨e0, e1, e2⟩ := hlay
    obtain ⟨r0, r1⟩ : g0.1 = o0.1 ∧ g1.1 = o1.1 := by simpa using hroot
    -- The contract's setup root: the setup's.
    have ho2 : o2.1 = roots.pi1.bytecode := by
      obtain ⟨hl, w, rest, hw⟩ := hC
      obtain ⟨a, b, c, hcl⟩ : ∃ a b c, D.pi1Calls = [a, b, c] := by
        match D.pi1Calls, hl with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      rw [hcl] at hw
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hw
      subst hw
      unfold pi1OpsOf at hops
      simp only at hops
      split at hops
      · exact absurd hops (by simp)
      · rename_i r2 _
        unfold contractPi1Openings at hops
        rw [pcsCalls_take _ _ _ _ _ (by simp [pi1CallsWith, hcl]), hcl] at hops
        simp only [pi1CallsWith, List.map_cons, List.map_nil] at hops
        obtain ⟨x, y, z, hxyz, -, -, hz3⟩ := mapM_three _ _ _ _ _ hops
        simp only [List.cons.injEq, and_true] at hxyz
        obtain ⟨-, -, rfl⟩ := hxyz
        obtain ⟨xd, hxd, rfl⟩ := Option.map_eq_some_iff.mp hz3
        obtain ⟨root, hrt, hx1⟩ := root_of_decodeWith _ _ _ hxd
        simp only [List.head?_cons, Option.some.injEq, callWord] at hrt
        rw [hx1, ← hrt, rootOfWord_rootWordOfBytes_digestBytes]
    -- The run accepts.
    have hacc : o.accepts = true := by
      unfold UniStatement.Outcome.accepts
      rw [hres, ← Array.all_toList]
      simp only [Bool.true_and, List.all_eq_true, beq_iff_eq]
      exact fun z hz ↦ hzs z hz
    rw [Pi1Decode.decodePi1Call_point _ _ _ _ (Pi1Decode.length_digestBytes _) (w1_length 2 (by decide)) hl3] at hd2
    simp only [Option.some.injEq] at hd2
    subst hd0 hd1 hd2
    rcases o0 with ⟨a0, q0⟩
    rcases o1 with ⟨a1, q1⟩
    rcases o2 with ⟨a2, q2⟩
    simp only at ho2 r0 r1 e0 e1 e2
    subst ho2 r0 r1 e0 e1 e2
    unfold pi1KeccakVerifierWith openSeq openAt
    simp only [RecProof.pi1Proof]
    have hres' : (UniStatement.runFs UniStatement.reference (pi1Iv UniStatement.reference D.pi1.programIv roots.pi1)
        input.toList s (.flock UniStatement.flockMain) .point .rec3 true).result = .ok r := hres
    have hacc' : (UniStatement.runFs UniStatement.reference (pi1Iv UniStatement.reference D.pi1.programIv roots.pi1)
        input.toList s (.flock UniStatement.flockMain) .point .rec3 true).accepts = true := hacc
    simp only [hD, hacc', hres', Bool.not_true, Bool.false_eq_true, ite_false, hro]
    have hcm : (List.map (fun x ↦ x.1) [(UniStatement.Commitment.c1, UniStatement.Opening.point pt1 v1 none),
        (UniStatement.Commitment.c2, UniStatement.Opening.point pt2 v2 none),
        (UniStatement.Commitment.setup, UniStatement.Opening.point pt3 v3 none)] == UniStatement.commitments) = true :=
      rfl
    simp only [hcm, List.forIn_cons, List.forIn_nil, bind_assoc,
      pure_bind, Bool.true_and, List.getD_cons_zero, List.getD_cons_succ,
      registryAt_lookup D roots hD 0 (by decide), registryAt_lookup D roots hD 1 (by decide),
      registryAt_lookup D roots hD 2 (by decide)]

end RecCompose

/-- info: 'RecCompose.registryAt_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.registryAt_lookup

/-- info: 'RecCompose.pi1OpeningsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1OpeningsAgree
