-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The pending reduction's identity is
-- `formal/UniSound/UniSound/FlockInterface.lean`'s `PendingHolds`; the walk's lemma's converse is
-- `Rec3FlockDefs.lean`'s `WalkLemmaConverse` (`formal/FlockSound/FlockSoundUni/Rec3Walk.lean`'s `WalkLemma`, `←`).
import UniComplete.Rec3FlockSum
import UniComplete.Rec3FlockSync
import UniSound.PendingLink

/-!
# The walk's zero vanishes on π1-rec3's honest transcript

**`walkZero3_eq_zero`**: given the walk's lemma's converse (`WalkLemmaConverse`, a named hypothesis until
`walk_zero_iff` lands), for `q_flock` satisfying Flock's relation (`FlockP.FlockHolds κ q`), at `log_n = 14 + κ`,
`flockMain`, every writer (any challenges), the value π1-rec3's walked verifier collects on the honest front
(`walkZero3`, `requireZero (walkedTerminal … + r_lc)`) is `0`. So `flockSyncs3`'s one collected value vanishes.

The route: the honest pending reduction `Pending.new fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc
fr.slices` of `frontW3`'s front `fr` satisfies `UniSound.PendingHolds` (`pendingHolds_front3`: `p.claim =
Σ_{u < 2^rounds} G p u · L p u`), and the converse of the walk's lemma turns it into the zero. `PendingHolds` is the
main line's `FlockP.PendingSumHolds` (`Σ_i G'_i L̂_i ŝ_i = p.claim`, `pendingSum_front3`) entry by entry
(`pending_entry`):

* `G p u` is `Â0 + α B̂0` (`UniSound.mleArr`, `cubeEq` sums) at `(bits(u mod 2^k), row_low, chi_in, bits(u / 2^k),
  chi_in')`; the stacks' `mleArr` is `multilinearEval` (`mleArr_eq_multilinearEval`, both the multilinear extension
  of `2^28` words: `UniSound.multilinearEval_eq_sum`), so `G p u` is `Ĝ'` at the Boolean point `bits u`
  (`FlockP.mle_sliced`, `bitsE_append`), i.e. the table's entry `G'_u` (`multilinearEval_bitsE`: at a Boolean point
  the extension is the entry, `UniSound.cubeEq_bitsE`);
* `L p u` is `L̂_u ŝ_u` (`FlockP.skipTable`, `FlockP.sliceTable`; without a skip the weights are `[1]`).

Decisions (recorded): the conversion is stated over variables (`pendingHolds_of_sum`, `pendingHolds_assemble`) and
instantiated at the prover's front only at the end, so that no kernel check reduces the prover's run; the main line's
`PendingTerminalHolds` is not needed (the Boolean points are evaluated through `FlockP.mle_sliced` directly), nor is
`Core.flock_pending` (π1-rec3's batch has no pending term).
-/

namespace UniComplete.Rec3

open UniStatement UniStatement.Flock LeanVM.Parameters Finset

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## Boolean points -/

/-- A Boolean point's low `k` and next `n` coordinates: `bits(u mod 2^k) ++ bits(u / 2^k) = bits u`. -/
theorem bitsE_append (u k n : ℕ) :
    UniSound.bitsE (u % 2 ^ k) k ++ UniSound.bitsE (u / 2 ^ k) n = UniSound.bitsE u (k + n) := by
  unfold UniSound.bitsE
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi ↦ ?_
    rw [Nat.testBit_mod_two_pow, decide_eq_true (List.mem_range.mp hi), Bool.true_and]
  · refine List.map_congr_left fun j _ ↦ ?_
    simp only [Function.comp, Nat.testBit_div_two_pow, Nat.add_comm j k]

/-- **At a Boolean point the extension is the entry**: `multilinearEval l (bits u) = l[u]`, `l` of `2^n` entries. -/
theorem multilinearEval_bitsE (l : List E) (n u : ℕ) (hl : l.length = 2 ^ n) (hu : u < 2 ^ n) :
    multilinearEval l (UniSound.bitsE u n) = l.getD u 0 := by
  have hlen : (UniSound.bitsE u n).length = n := UniSound.length_bitsE u n
  rw [UniSound.multilinearEval_eq_sum l _ (Or.inl (by rw [hlen]; exact hl)), hlen, Finset.sum_eq_single u]
  · rw [UniSound.cubeEq_bitsE n u u hu hu, if_pos rfl, one_mul]
  · intro x hx hne
    rw [UniSound.cubeEq_bitsE n u x hu (mem_range.mp hx), if_neg (Ne.symm hne), zero_mul]
  · intro h
    exact absurd (mem_range.mpr hu) h

/-- **A stack's `mleArr` is its `multilinearEval`** (`2^n` words, a point of `n` coordinates). -/
theorem mleArr_eq_multilinearEval (a : Array K) (n : ℕ) (p : List E) (ha : a.size = 2 ^ n) (hp : p.length = n) :
    UniSound.mleArr a n p = multilinearEval (a.toList.map ofK) p := by
  have hl : (a.toList.map ofK).length = 2 ^ p.length := by rw [List.length_map, Array.length_toList, ha, hp]
  rw [UniSound.multilinearEval_eq_sum _ _ (Or.inl hl), hp]
  unfold UniSound.mleArr
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ UniSound.cubeEq p n x * ofK (a.getD x 0)) (2 ^ n)]
  refine sum_congr rfl fun x hx ↦ ?_
  have hx' : x < a.size := by rw [ha]; exact mem_range.mp hx
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hx',
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx']
  rfl

/-! ## The pending reduction's summand, entry by entry -/

/-- **The summand at a cube point is the tables' product there**: `G p u · L p u = G'_u L̂_u ŝ_u` for the pending
reduction `p = Pending.new …` of a front of the prover's shape (`k ≤ 6`, `row_low` of `6 − k`, `chi_in`, `chi_in'`
of `8`, the slices sent, the weights `[1]` without a skip). -/
theorem pending_entry (zSkip : Option E) (low chiIn chiInPrime : List E) (alpha rLc : E) (s : List E) (k : ℕ)
    (hk : k ≤ 6) (hlow : low.length = 6 - k) (hin : chiIn.length = 8) (hinp : chiInPrime.length = 8)
    (hskip0 : k = 0 → (rowLowWeights zSkip low).1 = [1]) {u : ℕ} (hu : u < 2 ^ (k + 6)) :
    UniSound.Pending.G (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)) u *
        UniSound.Pending.L (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)) u =
      (FlockP.sliced k low chiIn chiInPrime alpha).getD u 0 *
        (FlockP.skipTable k (rowLowWeights zSkip low).1).getD u 0 * (FlockP.sliceTable k s).getD u 0 := by
  have hpk : (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k = k := by
    show packing - low.length = k
    rw [hlow]; unfold packing; omega
  have hρ : (UniSound.bitsE (u % 2 ^ k) k).length = k := UniSound.length_bitsE _ _
  have hσ : (UniSound.bitsE (u / 2 ^ k) 6).length = 6 := UniSound.length_bitsE _ _
  have hpt : (UniSound.bitsE (u % 2 ^ k) k ++ low ++ chiIn ++ UniSound.bitsE (u / 2 ^ k) 6 ++ chiInPrime).length =
      matrixVars := by
    simp only [List.length_append, hρ, hσ, hlow, hin, hinp]
    unfold matrixVars blake2sR1csLogSize
    omega
  have hA := mleArr_eq_multilinearEval (flockMatrixStack true) matrixVars _ (FlockP.flockMatrixStack_size true) hpt
  have hB := mleArr_eq_multilinearEval (flockMatrixStack false) matrixVars _ (FlockP.flockMatrixStack_size false) hpt
  have hsl := FlockP.mle_sliced k hk _ _ low chiIn chiInPrime alpha hρ hσ hlow hin hinp
  have hglen : (FlockP.sliced k low chiIn chiInPrime alpha).toList.length = 2 ^ (k + 6) := by
    simp [FlockP.sliced, kBits, pow_add]
  have hbool : multilinearEval (FlockP.sliced k low chiIn chiInPrime alpha).toList
      (UniSound.bitsE (u % 2 ^ k) k ++ UniSound.bitsE (u / 2 ^ k) 6) =
        (FlockP.sliced k low chiIn chiInPrime alpha).getD u 0 := by
    rw [bitsE_append, multilinearEval_bitsE _ _ _ hglen hu, FlockP.toList_getD]
  have hG : UniSound.Pending.G (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)) u =
      (FlockP.sliced k low chiIn chiInPrime alpha).getD u 0 := by
    show UniSound.mleArr (flockMatrixStack true) matrixVars
        (UniSound.bitsE (u % 2 ^ (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k)
            (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k ++ low ++ chiIn ++
          UniSound.bitsE (u / 2 ^ (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k) 6 ++ chiInPrime) +
      alpha * UniSound.mleArr (flockMatrixStack false) matrixVars
        (UniSound.bitsE (u % 2 ^ (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k)
            (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k ++ low ++ chiIn ++
          UniSound.bitsE (u / 2 ^ (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k) 6 ++ chiInPrime) = _
    rw [hpk, hA, hB, ← hsl, hbool]
  have hi : u < 2 ^ k * kBits := by
    unfold kBits; rw [show (64 : ℕ) = 2 ^ 6 from rfl, ← pow_add]; exact hu
  have hL : UniSound.Pending.L (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)) u =
      (FlockP.skipTable k (rowLowWeights zSkip low).1).getD u 0 * (FlockP.sliceTable k s).getD u 0 := by
    show (if (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k > 0 then
          (rowLowWeights zSkip low).1.getD (u % 2 ^ (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k) 0
        else 1) * s.getD (u / 2 ^ (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).k) 0 = _
    have e1 : (FlockP.skipTable k (rowLowWeights zSkip low).1).getD u 0 =
        (rowLowWeights zSkip low).1.getD (u % 2 ^ k) 0 :=
      E2ECompleteness.getD_ofFn' _ hi 0
    have e2 : (FlockP.sliceTable k s).getD u 0 = s.getD (u / 2 ^ k) 0 := E2ECompleteness.getD_ofFn' _ hi 0
    rw [hpk, e1, e2]
    by_cases h0 : 0 < k
    · rw [if_pos h0]
    · have hk0 : k = 0 := by omega
      rw [if_neg h0, hskip0 hk0, hk0, pow_zero, Nat.mod_one, List.getD_cons_zero]
  rw [hG, hL, mul_assoc]

/-! ## `PendingHolds` from the product sum -/

/-- **`PendingHolds` from the tables' product sum**, over variables (the front's fields). -/
theorem pendingHolds_of_sum (zSkip : Option E) (low chiIn chiInPrime : List E) (alpha rLc : E) (s : List E) (k : ℕ)
    (hk : k ≤ 6) (hlow : low.length = 6 - k) (hin : chiIn.length = 8) (hinp : chiInPrime.length = 8)
    (hskip0 : k = 0 → (rowLowWeights zSkip low).1 = [1])
    (hsum : ∑ i ∈ range (2 ^ (k + 6)), (FlockP.sliced k low chiIn chiInPrime alpha).getD i 0 *
        (FlockP.skipTable k (rowLowWeights zSkip low).1).getD i 0 * (FlockP.sliceTable k s).getD i 0 =
      (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).claim) :
    UniSound.PendingHolds (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)) := by
  have hr : (Pending.new zSkip low chiIn chiInPrime alpha rLc (some s)).rounds = k + 6 := by
    show (packing - low.length) + packing = k + 6
    rw [hlow]; unfold packing; omega
  unfold UniSound.PendingHolds
  rw [hr, ← hsum]
  exact (sum_congr rfl fun u hu ↦
    pending_entry zSkip low chiIn chiInPrime alpha rLc s k hk hlow hin hinp hskip0 (mem_range.mp hu)).symm

/-- **`PendingHolds` of `assemble`'s pending reduction** from `FlockP.PendingSumHolds`, for any front of the prover's
shape (`FlockP.assemble_terminal`'s hypotheses). -/
theorem pendingHolds_assemble (fr : Front) (s : List E) (e : End) (k : ℕ) (hk : k ≤ 6)
    (hlow : fr.rowLow.length = 6 - k) (hin : fr.chiIn.length = 8) (hinp : fr.chiInPrime.length = 8)
    (hsl : fr.slices = some s) (hskip0 : k = 0 → (rowLowWeights fr.zSkip fr.rowLow).1 = [1])
    (hsum : FlockP.PendingSumHolds (FlockP.assemble fr s e)) :
    UniSound.PendingHolds (Pending.new fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices) := by
  have hk' : packing - fr.rowLow.length = k := by rw [hlow]; unfold packing; omega
  have hsum' : ∑ i ∈ range (2 ^ (k + 6)), (FlockP.sliced k fr.rowLow fr.chiIn fr.chiInPrime fr.alpha).getD i 0 *
        (FlockP.skipTable k (rowLowWeights fr.zSkip fr.rowLow).1).getD i 0 * (FlockP.sliceTable k s).getD i 0 =
      (Pending.new fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc fr.slices).claim := by
    unfold FlockP.PendingSumHolds FlockP.assemble at hsum
    simp only [hk'] at hsum
    exact hsum
  rw [hsl] at hsum' ⊢
  exact pendingHolds_of_sum fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.alpha fr.rLc s k hk hlow hin hinp hskip0
    hsum'

/-! ## At the honest front -/

/-- **The honest pending reduction at π1-rec3 is its sum** (`UniSound.PendingHolds`): the pending reduction of
`frontW3`'s front, at a pure Keccak-256, `log_n = 14 + κ`, any skip `k ≤ 6`, the slices sent, every writer, given
Flock's relation on `q_flock`. -/
theorem pendingHolds_front3 (H : List UInt8 → LeanVM.Protocol.Digest) (κ : ℕ) (variant : Variant) (q : Array K)
    (w : Wr) (hk : variant.skip ≤ 6) (hc : variant.slices ≠ .claim) (hF : FlockP.FlockHolds κ q) :
    UniSound.PendingHolds (Pending.new
      ((frontW3 (m := Id) (Pure.pure ∘ H) (14 + κ) variant q).run w).1.1.zSkip
      ((frontW3 (m := Id) (Pure.pure ∘ H) (14 + κ) variant q).run w).1.1.rowLow
      ((frontW3 (m := Id) (Pure.pure ∘ H) (14 + κ) variant q).run w).1.1.chiIn
      ((frontW3 (m := Id) (Pure.pure ∘ H) (14 + κ) variant q).run w).1.1.chiInPrime
      ((frontW3 (m := Id) (Pure.pure ∘ H) (14 + κ) variant q).run w).1.1.alpha
      ((frontW3 (m := Id) (Pure.pure ∘ H) (14 + κ) variant q).run w).1.1.rLc
      ((frontW3 (m := Id) (Pure.pure ∘ H) (14 + κ) variant q).run w).1.1.slices) := by
  obtain ⟨h1, h2, h3, -, h5, -, -, -⟩ := frontW3_shape (Pure.pure ∘ H) (14 + κ) variant q w hk (by omega)
  obtain ⟨-, hs0⟩ := frontW3_skipWeights (Pure.pure ∘ H) (14 + κ) variant q w hk (by omega)
  exact pendingHolds_assemble _ _ (.combination [] 0) variant.skip hk h1 h2 h3 (h5 hc) hs0
    (pendingSum_front3 (Pure.pure ∘ H) κ variant q w hk hc hF (fun _ ↦ FlockP.Skip.skipComplete _ hk) _)

/-- **The walk's zero vanishes on π1-rec3's honest transcript**: given the walk's lemma's converse, for `q_flock`
satisfying Flock's relation, at `log_n = 14 + κ` (`blake2sR1csLogSize + κ`), `flockMain`, every writer. -/
theorem walkZero3_eq_zero (H : List UInt8 → LeanVM.Protocol.Digest) (hW : WalkLemmaConverse) (κ : ℕ) (q : Array K)
    (hF : FlockP.FlockHolds κ q) (w : Wr) : walkZero3 H (14 + κ) flockMain q w = 0 := by
  have hP := pendingHolds_front3 H κ flockMain q w (by decide) (by decide) hF
  obtain ⟨h1, h2, h3, h4, h5, -, h7, -⟩ :=
    frontW3_shape (Pure.pure ∘ H) (14 + κ) flockMain q w (by decide) (by omega)
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (h7 (by decide))
  have hsl := h5 (by decide)
  rw [walkZero3_eq' H (14 + κ) flockMain q w, hz, hsl, Option.getD_some]
  rw [hz, hsl] at hP
  exact hW z _ _ _ _ _ _ (by rw [h1]; rfl) h2 h3 h4 hP

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.pendingHolds_front3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.pendingHolds_front3

/-- info: 'UniComplete.Rec3.walkZero3_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.walkZero3_eq_zero
