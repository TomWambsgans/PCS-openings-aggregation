-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `FlockProverSum.lean`'s
-- `zc_values`/`pendingSumHolds`, `FlockProverTerminal.lean`'s `pendingTerminalHolds`/`tables_shape` and
-- `FlockProverMain.lean`'s `pendingSumHolds_honest` to π1-rec3's honest Flock prover (`Rec3Prover.lean`'s `flockProve3`).
import UniComplete.Rec3FlockShape
import UniComplete.FlockProverMain

/-!
# π1-rec3's pending matrices' identities, in the batch's forms

The main line's identities of Flock's pending matrices (`FlockProver.lean`'s `PendingSumHolds`,
`PendingTerminalHolds`, the tables' shape), for `flockProve3`, at a pure Keccak-256, every writer (any challenges).
π1-rec3's stream does not run the matrices' reduction (its verifier walks the lincheck's terminal), but the walk's
zero is the pending reduction's identity (`Rec3FlockHonest.lean`), proved from these.

* **`zc_values3`**: the zerocheck's values `v_a`, `v_b`, `v_c` are `A z`, `B z`, `z` at its point, given Flock's
  relation on `q_flock` and the univariate skip's completeness (`FlockP.zc_values`'s statement for `zerocheckW3`);
* **`pendingSum_front3`**: `FlockP.PendingSumHolds` of `FlockP.assemble` of `frontW3`'s front, for **any** end;
  **`pendingSumHolds3`**: of the prover's output (`FlockP.pendingSumHolds_honest`'s statement), the skip's
  completeness discharged (`FlockP.Skip.skipComplete`);
* **`pendingTerminalHolds3`**, **`tables_shape3`**: `FlockP.pendingTerminalHolds`, `FlockP.tables_shape` for
  `flockProve3`.

The proofs are the main line's, through `zerocheckW3_eq`, `frontW3_eq`, `flockProve3_eq`, `frontW3_shape`
(`Rec3FlockShape.lean`): only the zerocheck's draw differs, and the main line's lemmas on the rounds
(`FlockP.zcRounds_complete`, `FlockP.lcRounds_complete`) and on the skip's start (`FlockP.skip_start`) hold at any eq
coordinates and challenges.
-/

namespace UniComplete.Rec3

open UniStatement UniStatement.Flock LeanVM.Parameters Finset

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

variable (H : List UInt8 → Id LeanVM.Protocol.Digest)

/-! ## The zerocheck's values -/

/-- **The zerocheck's values at π1-rec3** (`v_a`, `v_b`, `v_c`) are `A z`, `B z`, `z` at its point, through the rows'
weights: given Flock's relation and, with a skip, `SkipComplete`. Stated for the zerocheck's point split as the front
splits it. -/
theorem zc_values3 (κ k : ℕ) (hk : k ≤ 6) (q : Array K) (hF : FlockP.FlockHolds κ q)
    (hskipC : 0 < k → FlockP.SkipComplete k) (w : Wr) :
    ∃ (zSkip : Option E) (low chiIn chiRest : List E) (va vb vc : E),
      ((zerocheckW3 H (14 + κ) k (FlockP.witOf (14 + κ) q)).run w).1 = (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) ∧
      low.length = 6 - k ∧ chiIn.length = 8 ∧ chiRest.length = κ ∧
      (rowLowWeights zSkip low).1.length = 2 ^ k ∧
      va = ∑ t ∈ range (2 ^ chiRest.length), FlockP.eqB chiRest t *
        ∑ row ∈ range (2 ^ 14), FlockP.rowW (rowLowWeights zSkip low).2 chiIn row * FlockP.aZ q t row ∧
      vb = ∑ t ∈ range (2 ^ chiRest.length), FlockP.eqB chiRest t *
        ∑ row ∈ range (2 ^ 14), FlockP.rowW (rowLowWeights zSkip low).2 chiIn row * FlockP.bZ q t row ∧
      vc = ∑ t ∈ range (2 ^ chiRest.length), FlockP.eqB chiRest t *
        ∑ row ∈ range (2 ^ 14), FlockP.rowW (rowLowWeights zSkip low).2 chiIn row * FlockP.zAt q t row := by
  obtain ⟨sampled, st, zo, hlen, ⟨w1, hst⟩, ⟨w2, hzo⟩, heq⟩ :=
    zerocheckW3_eq H (14 + κ) k (FlockP.witOf (14 + κ) q) w
  generalize hr : fixedChallenges ++ sampled = r at hst hzo
  have hrlen : r.length = 14 + κ - k := by
    rw [← hr, List.length_append, FlockP.fixedChallenges_length, hlen]; unfold nFixed; omega
  have hkr : k + r.length = 14 + κ := by omega
  have hchilen : zo.chi.length = 14 + κ - k := by rw [hzo, FlockP.zcRounds_chi_length, hrlen]
  have hlow : (zo.chi.take (packing - k)).length = 6 - k := by
    rw [List.length_take, hchilen]; unfold packing; omega
  have hin : ((zo.chi.drop (packing - k)).take lincheckRounds).length = 8 := by
    rw [List.length_take, List.length_drop, hchilen]; unfold packing lincheckRounds blake2sR1csLogSize; omega
  have hcr : ((zo.chi.drop (packing - k)).drop lincheckRounds).length = κ := by
    rw [List.length_drop, List.length_drop, hchilen]; unfold packing lincheckRounds blake2sR1csLogSize; omega
  have hchi : zo.chi.take (packing - k) ++ (zo.chi.drop (packing - k)).take lincheckRounds ++
      (zo.chi.drop (packing - k)).drop lincheckRounds = zo.chi := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  generalize hlowdef : zo.chi.take (packing - k) = low at hlow hchi
  generalize hindef : (zo.chi.drop (packing - k)).take lincheckRounds = chiIn at hin hchi
  generalize hcrdef : (zo.chi.drop (packing - k)).drop lincheckRounds = chiRest at hcr hchi
  have hstart := FlockP.skip_start H κ k hk q hF hskipC r hkr low hlow w1 st hst
  have hsk := hstart.1
  have hsa := hstart.2.1
  have hsb := hstart.2.2.1
  have hsc := hstart.2.2.2.1
  have hea := hstart.2.2.2.2.1
  have heb := hstart.2.2.2.2.2.1
  have hec := hstart.2.2.2.2.2.2.1
  have hclaim := hstart.2.2.2.2.2.2.2
  have hzc3 := FlockP.zcRounds_complete H r st.claim st.a st.b st.c w2 hsa hsb hsc hclaim
  rw [← hzo] at hzc3
  have hptlen : (low ++ chiIn ++ chiRest).length = r.length := by rw [hchi, hchilen, hrlen]
  have hTz : ∀ (Tz : Array E), Tz.size = 2 ^ r.length → Tz.size = 2 ^ (low ++ chiIn ++ chiRest).length :=
    fun Tz h ↦ by rw [hptlen]; exact h
  have hE : ∀ (Tz T : Array E), (∀ b < 2 ^ r.length, Tz.getD b 0 = ∑ x ∈ range (2 ^ k),
      (rowLowWeights st.zSkip low).1.getD x 0 * T.getD (x + 2 ^ k * b) 0) →
      ∀ b < 2 ^ (low ++ chiIn ++ chiRest).length, Tz.getD b 0 = ∑ x ∈ range (2 ^ k),
        (rowLowWeights st.zSkip low).1.getD x 0 * T.getD (x + 2 ^ k * b) 0 :=
    fun Tz T h b hb ↦ h b (by rw [← hptlen]; exact hb)
  have va := FlockP.zc_table_value st.zSkip low chiIn chiRest k κ hk hsk hlow hin hcr _ st.a (hTz _ hsa)
    (hE _ _ hea) (FlockP.aZ q) (fun row hrow t ht ↦ (FlockP.witOf_getD κ q hrow ht).1)
  have vb := FlockP.zc_table_value st.zSkip low chiIn chiRest k κ hk hsk hlow hin hcr _ st.b (hTz _ hsb)
    (hE _ _ heb) (FlockP.bZ q) (fun row hrow t ht ↦ (FlockP.witOf_getD κ q hrow ht).2.1)
  have vc := FlockP.zc_table_value st.zSkip low chiIn chiRest k κ hk hsk hlow hin hcr _ st.c (hTz _ hsc)
    (hE _ _ hec) (FlockP.zAt q) (fun row hrow t ht ↦ (FlockP.witOf_getD κ q hrow ht).2.2)
  rw [hchi] at va vb vc
  refine ⟨st.zSkip, low, chiIn, chiRest, zo.va, zo.vb, zo.running + zo.va * zo.vb, ?_, hlow, hin, hcr, hsk,
    ?_, ?_, ?_⟩
  · rw [heq, hchi]
  · rw [hzc3.1, va]
  · rw [hzc3.2.1, vb]
  · rw [hzc3.2.2, ← vc, add_comm, ← add_assoc, FlockP.add_self_E, zero_add]

/-! ## The pending sum -/

/-- **`PendingSumHolds` of `assemble` of π1-rec3's front**, for any end: at a pure Keccak-256, `log_n = 14 + κ`, any
skip `k ≤ 6`, the slices sent, every writer, given Flock's relation on `q_flock` and, for `k > 0`, the univariate
skip's completeness (`FlockP.pendingSumHolds`'s proof, at `frontW3`). -/
theorem pendingSum_front3 (κ : ℕ) (variant : Variant) (q : Array K) (w : Wr) (hk : variant.skip ≤ 6)
    (hc : variant.slices ≠ .claim) (hF : FlockP.FlockHolds κ q)
    (hskipC : 0 < variant.skip → FlockP.SkipComplete variant.skip) (e : End) :
    FlockP.PendingSumHolds (FlockP.assemble ((frontW3 H (14 + κ) variant q).run w).1.1
      ((frontW3 H (14 + κ) variant q).run w).1.2 e) := by
  obtain ⟨zc, alpha, lc, hzc, ⟨w2, hlc⟩, hfr⟩ := frontW3_eq H (14 + κ) variant q w
  obtain ⟨zSkip, low, chiIn, chiRest, va, vb, vc, hzeq, hlow, hin, hcr, hsk, hva, hvb, hvc⟩ :=
    zc_values3 H κ variant.skip hk q hF hskipC w
  rw [← hzc] at hzeq
  subst hzeq
  rw [hfr]
  have hχ : lc.challenges.length = 8 := by rw [hlc, FlockP.lcRounds_length]; rfl
  have hpk : packing - variant.skip = low.length := by rw [hlow]; unfold packing; rfl
  have h1 : (low ++ chiIn ++ chiRest).take (packing - variant.skip) = low := by
    rw [hpk, List.append_assoc, List.take_left' rfl]
  have h2 : ((low ++ chiIn ++ chiRest).drop (packing - variant.skip)).take lincheckRounds = chiIn := by
    rw [hpk, List.append_assoc, List.drop_left' rfl, List.take_left' (by rw [hin]; rfl)]
  have h3 : ((low ++ chiIn ++ chiRest).drop (packing - variant.skip)).drop lincheckRounds = chiRest := by
    rw [hpk, List.append_assoc, List.drop_left' rfl, List.drop_left' (by rw [hin]; rfl)]
  have hW : FlockP.lcWeightsOf variant.skip (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) alpha =
      FlockP.lincheckWeights (FlockP.rowWeightsOf (rowLowWeights zSkip low).2 chiIn) alpha := by
    unfold FlockP.lcWeightsOf; rw [h1, h2]
  have hZ : FlockP.lcWitnessOf variant.skip q (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) =
      FlockP.lincheckWitness q chiRest := by
    unfold FlockP.lcWitnessOf; rw [h3]
  rw [hW, hZ] at hlc
  have hWs : (FlockP.lincheckWeights (FlockP.rowWeightsOf (rowLowWeights zSkip low).2 chiIn) alpha).size =
      2 ^ (lincheckRounds + 6) := by simp [FlockP.lincheckWeights, lincheckRounds, blake2sR1csLogSize]
  have hZs : (FlockP.lincheckWitness q chiRest).size = 2 ^ (lincheckRounds + 6) := by
    simp [FlockP.lincheckWitness, lincheckRounds, blake2sR1csLogSize]
  have hinit : FlockP.lcClaim (zSkip, low ++ chiIn ++ chiRest, va, vb, vc) alpha =
      ∑ i ∈ range (2 ^ (lincheckRounds + 6)),
        (FlockP.lincheckWeights (FlockP.rowWeightsOf (rowLowWeights zSkip low).2 chiIn) alpha).getD i 0 *
          (FlockP.lincheckWitness q chiRest).getD i 0 := by
    rw [show (2 : ℕ) ^ (lincheckRounds + 6) = 2 ^ 14 from rfl, FlockP.lincheck_init,
      FlockP.lincheckWitness_pin κ q hF chiRest hcr, mul_one, ← hva, ← hvb, ← hvc]
    rfl
  have hcomp := FlockP.lcRounds_complete H lincheckRounds 6 _ _ _ w2 hWs hZs hinit
  rw [← hlc] at hcomp
  have hz : lc.z = lc.challenges.foldl FlockP.foldHigh (FlockP.lincheckWitness q chiRest) := by
    rw [hlc, FlockP.lcRounds_z]
  have hs : lc.z.toList.length = 64 := by
    rw [Array.length_toList, hz]
    exact FlockP.foldl_foldHigh_size _ 6 _ (by rw [hχ]; simp [FlockP.lincheckWitness, blake2sR1csLogSize])
  refine FlockP.pendingSum_assemble variant hk zSkip low chiIn chiRest va vb vc alpha lc e hsk hlow hin hχ hs hc ?_
  rw [hcomp, show (2 : ℕ) ^ 6 = 64 from rfl]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [FlockP.toList_getD, hz]

/-- **`PendingSumHolds` of π1-rec3's honest prover** (`FlockP.pendingSumHolds_honest`'s statement for `flockProve3`):
unconditionally but for Flock's relation on `q_flock`. -/
theorem pendingSumHolds3 (κ : ℕ) (variant : Variant) (q : Array K) (w : Wr) (hk : variant.skip ≤ 6)
    (hc : variant.slices ≠ .claim) (hF : FlockP.FlockHolds κ q) :
    FlockP.PendingSumHolds ((flockProve3 H (14 + κ) variant q).run w).1 := by
  obtain ⟨frs, e, hfrs, hout⟩ := flockProve3_eq H (14 + κ) variant q w
  rw [hout, hfrs]
  exact pendingSum_front3 H κ variant q w hk hc hF (fun _ ↦ FlockP.Skip.skipComplete _ hk) e

/-! ## The pending terminal, the tables' shape -/

/-- **The skip's weights of π1-rec3's front**: `2^k` of them, `[1]` without a skip. -/
theorem frontW3_skipWeights (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (hk : variant.skip ≤ 6)
    (hN : 14 ≤ logN) :
    (rowLowWeights ((frontW3 H logN variant q).run w).1.1.zSkip ((frontW3 H logN variant q).run w).1.1.rowLow).1.length =
        2 ^ variant.skip ∧
      (variant.skip = 0 → (rowLowWeights ((frontW3 H logN variant q).run w).1.1.zSkip
        ((frontW3 H logN variant q).run w).1.1.rowLow).1 = [1]) := by
  obtain ⟨frs, hfrs⟩ : ∃ frs, frs = ((frontW3 H logN variant q).run w).1 := ⟨_, rfl⟩
  obtain ⟨h1, -, -, -, -, h6, h7, -⟩ := frontW3_shape H logN variant q w hk hN
  rw [← hfrs] at h1 h6 h7 ⊢
  refine ⟨?_, fun h0 ↦ ?_⟩
  · by_cases h0 : 0 < variant.skip
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (h7 h0)
      rw [hz, rowLowWeights, h1]
      simp [lagrangeWeights, packing]
      omega
    · rw [h6 (by omega)]
      simp [rowLowWeights, h0, show variant.skip = 0 by omega]
  · rw [h6 h0]
    rfl

/-- **`PendingTerminalHolds` of π1-rec3's honest prover** (`FlockP.pendingTerminalHolds`'s statement for
`flockProve3`), any skip `k ≤ 6`, `log_n ≥ 14`, the slices sent, every writer. -/
theorem pendingTerminalHolds3 (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (hk : variant.skip ≤ 6)
    (hN : 14 ≤ logN) (hc : variant.slices ≠ .claim) :
    FlockP.PendingTerminalHolds ((flockProve3 H logN variant q).run w).1 := by
  obtain ⟨frs, e, hfrs, hout⟩ := flockProve3_eq H logN variant q w
  obtain ⟨h1, h2, h3, h4, h5, -, -, -⟩ := frontW3_shape H logN variant q w hk hN
  obtain ⟨hs1, hs0⟩ := frontW3_skipWeights H logN variant q w hk hN
  rw [← hfrs] at h1 h2 h3 h4 h5 hs1 hs0
  rw [hout]
  exact FlockP.assemble_terminal frs.1 frs.2 e variant.skip hk h1 h2 h3 h4 (h5 hc) hs1 hs0

/-- **The tables' shape of π1-rec3's honest prover** (`FlockP.tables_shape`'s statement for `flockProve3`). -/
theorem tables_shape3 (logN : ℕ) (variant : Variant) (q : Array K) (w : Wr) (hk : variant.skip ≤ 6)
    (hN : 14 ≤ logN) :
    let t := ((flockProve3 H logN variant q).run w).1.tables
    t.rounds = variant.skip + 6 ∧ t.g.size = 2 ^ (variant.skip + 6) ∧ t.l.size = 2 ^ (variant.skip + 6) ∧
      t.s.size = 2 ^ (variant.skip + 6) ∧
      (∀ i < 2 ^ (variant.skip + 6), t.l.getD i 0 = t.l.getD (i % 2 ^ variant.skip) 0) ∧
      (∀ i < 2 ^ (variant.skip + 6), t.s.getD i 0 = t.s.getD (2 ^ variant.skip * (i / 2 ^ variant.skip)) 0) := by
  intro t
  obtain ⟨frs, e, hfrs, hout⟩ := flockProve3_eq H logN variant q w
  obtain ⟨h1, -⟩ := frontW3_shape H logN variant q w hk hN
  rw [← hfrs] at h1
  simp only [t, hout]
  exact FlockP.assemble_tables_shape frs.1 frs.2 e variant.skip h1 hk

end UniComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniComplete.Rec3.pendingSum_front3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.pendingSum_front3

/-- info: 'UniComplete.Rec3.pendingSumHolds3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.pendingSumHolds3

/-- info: 'UniComplete.Rec3.pendingTerminalHolds3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.pendingTerminalHolds3

/-- info: 'UniComplete.Rec3.tables_shape3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Rec3.tables_shape3
