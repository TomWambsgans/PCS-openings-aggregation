-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit.Loops
import Circuit.Wiring

/-!
# Keccak-f[1600] on wires: the two transcriptions build the same rows

`PcsQuotient.Build.round` (one `do` block of `for` loops, filling arrays by `set!`; ρ and π by the
forward assignment) is cut into its loops (`Q.round`, equal by definition, `round_eq`), and each
loop is simulated by F0b's `mapM` (`sim_theta`, `sim_rhoPi`, `sim_chi`, `sim_iota`), so
`sim_round`, `sim_keccakF`, `sim_keccak256Block`: for every message, the statement's Keccak-256 on
wires and F0b's make the same rows, in the same order, and return the same wires (read by `srcTr`).
-/

namespace Bridge.Circuit

open PcsQuotient.Build (WireState)

/-! ## The statement's round, cut into its loops -/

namespace Q

open PcsQuotient PcsQuotient.Build

/-- θ's column parity of lane `x`, bit `z`: a chain of four XORs. -/
def thetaCBody (a : WireState) (x z : ℕ) (_ : Array Src) : BuildM Src :=
  forIn [1:5] (a.at x z) fun y acc => do
    let acc ← xor acc (a.at (x + 5 * y) z)
    pure (ForInStep.yield acc)

/-- θ's column parities. -/
def thetaC (a : WireState) : BuildM (Array Src) :=
  forIn [:5] (Array.replicate (5 * 64) Src.zero) fun x s => do
    let s ← forIn [:64] s fun z s => do
      let v ← thetaCBody a x z s
      pure (ForInStep.yield (s.set! (64 * x + z) v))
    pure (ForInStep.yield s)

/-- θ's mix of column `x`, bit `z`. -/
def thetaDBody (c : Array Src) (x z : ℕ) (_ : Array Src) : BuildM Src :=
  xor (c.getD (64 * ((x + 4) % 5) + z) .zero) (c.getD (64 * ((x + 1) % 5) + (z + 63) % 64) .zero)

/-- θ's mixes. -/
def thetaD (c : Array Src) : BuildM (Array Src) :=
  forIn [:5] (Array.replicate (5 * 64) Src.zero) fun x s => do
    let s ← forIn [:64] s fun z s => do
      let v ← thetaDBody c x z s
      pure (ForInStep.yield (s.set! (64 * x + z) v))
    pure (ForInStep.yield s)

/-- θ on lane `i`, bit `z`, reading the array so far. -/
def thetaABody (d : Array Src) (i z : ℕ) (s : WireState) : BuildM Src :=
  xor (s.at i z) (d.getD (64 * (i % 5) + z) .zero)

/-- θ's last step: each lane XORed with its column's mix, in place. -/
def thetaA (a d : Array Src) : BuildM (Array Src) :=
  forIn [:25] a fun i s => do
    let s ← forIn [:64] s fun z s => do
      let v ← thetaABody d i z s
      pure (ForInStep.yield (s.set! (64 * i + z) v))
    pure (ForInStep.yield s)

/-- ρ and π, the forward assignment. -/
def rhoPiB (a : WireState) : BuildM WireState :=
  forIn [:25] (Array.replicate 1600 Src.zero) fun i b =>
    have r := LeanVM.Parameters.keccakRho.getD i 0
    do
    let b ← forIn [:64] b fun z b =>
      have b := Array.set! b (64 * LeanVM.Parameters.keccakPi i + (z + r) % 64) (a.at i z)
      pure (ForInStep.yield b)
    pure (ForInStep.yield b)

/-- χ of lane `x + 5 y`, bit `z`. -/
def chiBody (b : WireState) (y x z : ℕ) (_ : Array Src) : BuildM Src :=
  chi (b.at (x + 5 * y) z) (b.at ((x + 1) % 5 + 5 * y) z) (b.at ((x + 2) % 5 + 5 * y) z)

/-- χ, one row a bit, written over the state. -/
def chiA (a b : WireState) : BuildM WireState :=
  forIn [:5] a fun y s => do
    let s ← forIn [:5] s fun x s => do
      let s ← forIn [:64] s fun z s => do
        let v ← chiBody b y x z s
        pure (ForInStep.yield (s.set! (64 * (x + 5 * y) + z) v))
      pure (ForInStep.yield s)
    pure (ForInStep.yield s)

/-- ι. -/
def iotaA (a : WireState) (rc : UInt64) : BuildM WireState :=
  forIn [:64] a fun z s =>
    if rc >>> z.toUInt64 &&& 1 = 1 then do
      let v ← not (s.at 0 z)
      pure (ForInStep.yield (Array.set! s z v))
    else pure (ForInStep.yield s)

/-- θ. -/
def theta (a : WireState) : BuildM WireState := do
  let c ← thetaC a
  let d ← thetaD c
  thetaA a d

/-- The round, its loops named. -/
def round (a : WireState) (rc : UInt64) : BuildM WireState := do
  let t ← theta a
  let b ← rhoPiB t
  let s ← chiA t b
  iotaA s rc

end Q

theorem round_eq (a : WireState) (rc : UInt64) : PcsQuotient.Build.round a rc = Q.round a rc := by
  simp only [PcsQuotient.Build.round, Q.round, Q.theta, Q.thetaC, Q.thetaCBody, Q.thetaD,
    Q.thetaDBody, Q.thetaA, Q.thetaABody, Q.rhoPiB, Q.chiA, Q.chiBody, Q.iotaA, bind_assoc, bind_pure]

/-! ## Reading wires -/

theorem getD_map_srcTr (a : Array PcsQuotient.Src) (k : ℕ) :
    (a.map srcTr).getD k .zero = srcTr (a.getD k .zero) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[k]? <;> rfl

theorem get_map (a : WireState) (i z : ℕ) :
    PcsCircuit.Builder.State.get (a.map srcTr) i z = srcTr (a.at i z) :=
  getD_map_srcTr a _

theorem mapM_range_320 {α : Type} (g : ℕ → PcsCircuit.BuildM α) :
    (List.range 320).mapM g =
      List.flatten <$> (List.range 5).mapM fun x => (List.range 64).mapM fun z => g (64 * x + z) :=
  mapM_range_mul 64 g 5

theorem mapM_range_1600 {α : Type} (g : ℕ → PcsCircuit.BuildM α) :
    (List.range 1600).mapM g =
      List.flatten <$> (List.range 25).mapM fun x => (List.range 64).mapM fun z => g (64 * x + z) :=
  mapM_range_mul 64 g 25

theorem mapM_range_1600' {α : Type} (g : ℕ → PcsCircuit.BuildM α) :
    (List.range 1600).mapM g =
      List.flatten <$> (List.range 5).mapM fun y => (List.range 320).mapM fun w => g (320 * y + w) :=
  mapM_range_mul 320 g 5

/-- The end of a fill: the whole array overwritten. -/
theorem ow_end {c₀ s : Array PcsQuotient.Src} {acc : List PcsCircuit.Src} (h : Ow c₀ acc s)
    (hl : acc.length = c₀.size) : s.map srcTr = acc.toArray ∧ s.size = c₀.size :=
  ⟨h.full hl, h.size hl.le⟩

/-! ## θ -/

theorem forIn_range_1_5 {β : Type} (init : β) (f : ℕ → β → PcsQuotient.BuildM (ForInStep β)) :
    forIn [1:5] init f = forIn [1, 2, 3, 4] init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem sim_thetaC (a : WireState) :
    SimR (Q.thetaC a) ((List.range 320).mapM fun k =>
        [1, 2, 3, 4].foldlM
          (fun acc y => PcsCircuit.Builder.xorG acc (PcsCircuit.Builder.State.get (a.map srcTr) (k / 64 + 5 * y) (k % 64)))
          (PcsCircuit.Builder.State.get (a.map srcTr) (k / 64) (k % 64)))
      (fun c cs => cs.toArray = c.map srcTr ∧ c.size = 320) := by
  rw [mapM_range_320]
  refine SimR.pure_map List.flatten (sim_fill2 5 (Array.replicate (5 * 64) .zero) 0 (by simp)
    (fun x z => 64 * x + z) (fun x z => by omega) (Q.thetaCBody a) _ ?_ [] rfl _ (ow_init _))
    fun c vss h => ?_
  · intro x hx z hz acc s _ _
    have e1 : (64 * x + z) / 64 = x := by omega
    have e2 : (64 * x + z) % 64 = z := by omega
    simp only [e1, e2]
    unfold Q.thetaCBody
    rw [forIn_range_1_5]
    refine simR_forIn_foldlM [1, 2, 3, 4] _ _ (fun s t => t = srcTr s) _ _ (get_map a x z)
      fun y _ s t hst => ?_
    subst hst
    rw [get_map]
    exact (sim_xor _ _).bind_left fun v c hvc => SimR.pure ⟨v, rfl, hvc⟩
  · obtain ⟨h1, h2⟩ := ow_end h.1 (by simpa using h.2)
    exact ⟨h1.symm, by simpa using h2⟩

theorem sim_thetaD (c : Array PcsQuotient.Src) :
    SimR (Q.thetaD c) ((List.range 320).mapM fun k =>
        PcsCircuit.Builder.xorG (PcsCircuit.Builder.State.get (c.map srcTr) ((k / 64 + 4) % 5) (k % 64))
          (PcsCircuit.Builder.State.get (c.map srcTr) ((k / 64 + 1) % 5) ((k % 64 + 63) % 64)))
      (fun d ds => ds.toArray = d.map srcTr ∧ d.size = 320) := by
  rw [mapM_range_320]
  refine SimR.pure_map List.flatten (sim_fill2 5 (Array.replicate (5 * 64) .zero) 0 (by simp)
    (fun x z => 64 * x + z) (fun x z => by omega) (Q.thetaDBody c) _ ?_ [] rfl _ (ow_init _))
    fun d vss h => ?_
  · intro x hx z hz acc s _ _
    have e1 : (64 * x + z) / 64 = x := by omega
    have e2 : (64 * x + z) % 64 = z := by omega
    simp only [e1, e2]
    unfold Q.thetaDBody
    rw [PcsCircuit.Builder.State.get, PcsCircuit.Builder.State.get, getD_map_srcTr, getD_map_srcTr]
    exact sim_xor _ _
  · obtain ⟨h1, h2⟩ := ow_end h.1 (by simpa using h.2)
    exact ⟨h1.symm, by simpa using h2⟩

theorem sim_thetaA (a d : Array PcsQuotient.Src) (ha : a.size = 1600) :
    SimR (Q.thetaA a d) ((List.range 1600).mapM fun k =>
        PcsCircuit.Builder.xorG (PcsCircuit.Builder.State.get (a.map srcTr) (k / 64) (k % 64))
          (PcsCircuit.Builder.State.get (d.map srcTr) (k / 64 % 5) (k % 64)))
      (fun t ts => ts.toArray = t.map srcTr ∧ t.size = 1600) := by
  rw [mapM_range_1600]
  refine SimR.pure_map List.flatten (sim_fill2 25 a 0 (by omega)
    (fun x z => 64 * x + z) (fun x z => by omega) (Q.thetaABody d) _ ?_ [] rfl _ (ow_init _))
    fun t vss h => ?_
  · intro i hi z hz acc s hlen hs
    have e1 : (64 * i + z) / 64 = i := by omega
    have e2 : (64 * i + z) % 64 = z := by omega
    simp only [e1, e2]
    unfold Q.thetaABody
    have hsa : PcsQuotient.Build.WireState.at s i z = PcsQuotient.Build.WireState.at a i z :=
      hs.getD (by omega)
    rw [hsa, get_map, PcsCircuit.Builder.State.get, getD_map_srcTr]
    exact sim_xor _ _
  · obtain ⟨h1, h2⟩ := ow_end h.1 (by simpa [ha] using h.2)
    exact ⟨h1.symm, by simpa [ha] using h2⟩

theorem sim_theta (a : WireState) (ha : a.size = 1600) :
    SimR (Q.theta a) (PcsCircuit.Builder.theta (a.map srcTr))
      (fun t t' => t' = t.map srcTr ∧ t.size = 1600) := by
  unfold Q.theta PcsCircuit.Builder.theta
  refine (sim_thetaC a).bind fun c cs hc => ?_
  simp only [hc.1]
  refine (sim_thetaD c).bind fun d ds hd => ?_
  simp only [hd.1]
  rw [← bind_pure (Q.thetaA a d)]
  exact (sim_thetaA a d ha).bind fun t ts ht => SimR.pure ⟨ht.1, ht.2⟩

/-! ## ρ and π -/

/-- The forward assignment as one fold over the writes. -/
def rhoPiWrites (a : WireState) : List (ℕ × PcsQuotient.Src) :=
  (List.range 25).flatMap fun i => (List.range 64).map fun z =>
    (64 * LeanVM.Parameters.keccakPi i + (z + LeanVM.Parameters.keccakRho.getD i 0) % 64, a.at i z)

theorem foldl_flatMap' {α β γ : Type} (f : α → List β) (g : γ → β → γ) :
    ∀ (l : List α) (init : γ),
      (l.flatMap f).foldl g init = l.foldl (fun acc x => (f x).foldl g acc) init
  | [], _ => rfl
  | x :: l, init => by rw [List.flatMap_cons, List.foldl_append, List.foldl_cons, foldl_flatMap']

theorem rhoPiB_eq (a : WireState) :
    Q.rhoPiB a = pure ((rhoPiWrites a).foldl (fun b p => b.set! p.1 p.2)
      (Array.replicate 1600 PcsQuotient.Src.zero)) := by
  unfold Q.rhoPiB rhoPiWrites
  simp only [forIn_range, List.forIn_pure_yield_eq_foldl, pure_bind]
  rw [foldl_flatMap']
  simp only [List.foldl_map]

theorem size_foldl_set {α : Type} : ∀ (ps : List (ℕ × α)) (b : Array α),
    (ps.foldl (fun b p => b.set! p.1 p.2) b).size = b.size
  | [], _ => rfl
  | p :: ps, b => by rw [List.foldl_cons, size_foldl_set ps, PcsCircuit.size_set!]

theorem getD_foldl_set_of_not_mem {α : Type} (k : ℕ) (d : α) : ∀ (ps : List (ℕ × α)) (b : Array α),
    k ∉ ps.map Prod.fst → (ps.foldl (fun b p => b.set! p.1 p.2) b).getD k d = b.getD k d
  | [], _, _ => rfl
  | p :: ps, b, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, getD_foldl_set_of_not_mem k d ps _ h.2, PcsCircuit.getD_set!_ne _ _ _
      (Ne.symm h.1)]

theorem getD_foldl_set_of_mem {α : Type} (k : ℕ) (v d : α) : ∀ (ps : List (ℕ × α)) (b : Array α),
    (ps.map Prod.fst).Nodup → (k, v) ∈ ps → k < b.size →
      (ps.foldl (fun b p => b.set! p.1 p.2) b).getD k d = v
  | [], _, _, h, _ => absurd h (List.not_mem_nil)
  | p :: ps, b, hn, hm, hk => by
    rw [List.foldl_cons]
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [getD_foldl_set_of_not_mem k d ps _ hn.1, PcsCircuit.getD_set!_eq _ _ _ hk]
    · exact getD_foldl_set_of_mem k v d ps _ hn.2 hm (by rw [PcsCircuit.size_set!]; exact hk)

theorem rho_lt : ∀ i < 25, PcsCircuit.Builder.rho i < 64 := by decide

theorem keccakPi_lt : ∀ i < 25, LeanVM.Parameters.keccakPi i < 25 := by decide

theorem rhoPiWrites_nodup (a : WireState) : ((rhoPiWrites a).map Prod.fst).Nodup := by
  simp only [rhoPiWrites, List.map_flatMap, List.map_map]
  rw [List.nodup_flatMap]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [List.nodup_map_iff_inj_on (List.nodup_range)]
    intro z hz z' hz' h
    simp only [List.mem_range, Function.comp] at hz hz' h
    omega
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
    intro i j hi hj hij
    simp only [List.mem_range] at hi hj
    show List.Disjoint _ _
    rw [List.disjoint_left]
    intro k hk hk'
    simp only [List.mem_map, List.mem_range, Function.comp] at hk hk'
    obtain ⟨z, hz, rfl⟩ := hk
    obtain ⟨z', hz', he⟩ := hk'
    have h1 : LeanVM.Parameters.keccakPi i = LeanVM.Parameters.keccakPi j := by
      have := Nat.mod_lt (z + LeanVM.Parameters.keccakRho.getD i 0) (by norm_num : 0 < 64)
      have := Nat.mod_lt (z' + LeanVM.Parameters.keccakRho.getD j 0) (by norm_num : 0 < 64)
      omega
    apply hij
    rw [← PcsCircuit.piInv_keccakPi i hi, ← PcsCircuit.piInv_keccakPi j hj, h1]

theorem rhoPiWrites_mem (a : WireState) (k : ℕ) (hk : k < 1600) :
    (k, a.at (PcsCircuit.Builder.piInv (k / 64)) ((k % 64 + 64 - PcsCircuit.Builder.rho (PcsCircuit.Builder.piInv (k / 64))) % 64))
      ∈ rhoPiWrites a := by
  have hk64 : k / 64 < 25 := by omega
  have hi := PcsCircuit.piInv_lt (k / 64) hk64
  have hr := rho_lt _ hi
  simp only [rhoPiWrites, List.mem_flatMap, List.mem_range, List.mem_map]
  refine ⟨PcsCircuit.Builder.piInv (k / 64), hi,
    (k % 64 + 64 - PcsCircuit.Builder.rho (PcsCircuit.Builder.piInv (k / 64))) % 64,
    Nat.mod_lt _ (by norm_num), ?_⟩
  rw [PcsCircuit.rho_eq _ hi, PcsCircuit.keccakPi_piInv _ hk64]
  refine Prod.ext ?_ rfl
  simp only
  omega

theorem sim_rhoPi (a : WireState) :
    SimR (Q.rhoPiB a) (pure (PcsCircuit.Builder.rhoPi (a.map srcTr)))
      (fun b b' => b' = b.map srcTr ∧ b.size = 1600) := by
  rw [rhoPiB_eq]
  refine SimR.pure ⟨?_, by rw [size_foldl_set]; simp⟩
  apply Array.ext
  · simp only [Array.size_map, size_foldl_set]
    simp [PcsCircuit.Builder.rhoPi]
  · intro k h1 h2
    simp only [PcsCircuit.Builder.rhoPi, List.getElem_toArray, List.getElem_map, List.getElem_range,
      Array.getElem_map]
    simp only [PcsCircuit.Builder.rhoPi, List.size_toArray, List.length_map, List.length_range] at h1
    rw [get_map]
    have hsz : k < ((rhoPiWrites a).foldl (fun b p => b.set! p.1 p.2)
        (Array.replicate 1600 PcsQuotient.Src.zero)).size := by
      rw [size_foldl_set]; simpa using h1
    have := getD_foldl_set_of_mem k _ PcsQuotient.Src.zero (rhoPiWrites a)
      (Array.replicate 1600 PcsQuotient.Src.zero) (rhoPiWrites_nodup a) (rhoPiWrites_mem a k h1)
      (by simpa using h1)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz, Option.getD_some] at this
    rw [this]

/-! ## χ -/

theorem sim_chiA (t b : WireState) (ht : t.size = 1600) :
    SimR (Q.chiA t b) ((List.range 1600).mapM fun k =>
        PcsCircuit.Builder.chiG (PcsCircuit.Builder.State.get (b.map srcTr) (k / 64) (k % 64))
          (PcsCircuit.Builder.State.get (b.map srcTr) ((k / 64 % 5 + 1) % 5 + 5 * (k / 64 / 5)) (k % 64))
          (PcsCircuit.Builder.State.get (b.map srcTr) ((k / 64 % 5 + 2) % 5 + 5 * (k / 64 / 5)) (k % 64)))
      (fun s ss => ss.toArray = s.map srcTr ∧ s.size = 1600) := by
  rw [mapM_range_1600']
  simp only [mapM_range_320]
  unfold Q.chiA
  rw [forIn_range]
  refine SimR.pure_map List.flatten (simR_forIn (List.range 5) _ _
    (fun yss s => Ow t yss.flatten s ∧ yss.flatten.length = 320 * yss.length) [] t
    ⟨ow_init t, by simp⟩ fun i hi acc s hlen hs => ?_) fun s yss h => ?_
  · simp only [List.length_range] at hi
    simp only [List.length_nil, Nat.zero_add] at hlen
    simp only [List.getElem_range]
    rw [map_eq_pure_bind]
    refine (sim_fill2 5 t (320 * i) (by omega) (fun x z => 64 * (x + 5 * i) + z)
      (fun x z => by ring) (Q.chiBody b i) _ ?_ acc.flatten (by rw [hs.2, hlen]) s hs.1).bind
      fun s' vss h => SimR.pure ⟨s', rfl, ?_, ?_⟩
    · intro x hx z hz acc' s'' _ _
      have e1 : (320 * i + (64 * x + z)) / 64 = x + 5 * i := by omega
      have e2 : (320 * i + (64 * x + z)) % 64 = z := by omega
      have e3 : (x + 5 * i) % 5 = x := by omega
      have e4 : (x + 5 * i) / 5 = i := by omega
      simp only [e1, e2, e3, e4]
      unfold Q.chiBody
      rw [get_map, get_map, get_map]
      exact sim_chi _ _ _
    · simpa using h.1
    · simp [hs.2, h.2, hlen]
      ring
  · simp only [List.nil_append, List.length_range] at h
    have hl : yss.flatten.length = t.size := by rw [h.1.2, h.2, ht]
    obtain ⟨h1, h2⟩ := ow_end h.1.1 hl
    exact ⟨h1.symm, by rw [h2, ht]⟩

/-! ## ι -/

theorem shift_and_one (rc : UInt64) (z : ℕ) (hz : z < 64) :
    (rc >>> z.toUInt64 &&& 1 = 1) ↔ rc.toNat.testBit z = true := by
  rw [← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight]
  have hz' : z.toUInt64.toNat % 64 = z := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [hz', UInt64.toNat_one, Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (rc.toNat >>> z) with h | h <;> simp [h]

theorem sim_iotaA (a : WireState) (ha : a.size = 1600) (rc : UInt64) :
    SimR (Q.iotaA a rc) (PcsCircuit.Builder.iota (a.map srcTr) rc)
      (fun s s' => s' = s.map srcTr ∧ s.size = 1600) := by
  unfold Q.iotaA PcsCircuit.Builder.iota
  rw [forIn_range, ← bind_pure (forIn (List.range 64) a _)]
  refine (simR_forIn (List.range 64) _ _ (Ow a) [] a (ow_init a)
    fun i hi acc s hlen hs => ?_).bind fun s lane h => SimR.pure ?_
  · simp only [List.length_range] at hi
    simp only [List.length_nil, Nat.zero_add] at hlen
    simp only [List.getElem_range]
    have hsa : PcsQuotient.Build.WireState.at s 0 i = PcsQuotient.Build.WireState.at a 0 i :=
      hs.getD (by omega)
    by_cases hb : rc.toNat.testBit i = true
    · rw [if_pos ((shift_and_one rc i hi).mpr hb), if_pos hb, hsa, get_map]
      refine (sim_not _).bind_left fun v c hvc => SimR.pure ⟨_, rfl, ?_⟩
      subst hvc
      rw [← hlen]
      exact hs.set (by omega) v
    · rw [if_neg (fun h => hb ((shift_and_one rc i hi).mp h)), if_neg hb, get_map]
      refine SimR.pure ⟨s, rfl, ?_⟩
      have := hs.keep (by omega)
      rwa [hlen, show PcsQuotient.Build.WireState.at a 0 i = a.getD i .zero by
        simp [PcsQuotient.Build.WireState.at]] at *
  · simp only [List.nil_append, List.length_range] at h
    obtain ⟨hs, hl⟩ := h
    have hsz := hs.size (by omega)
    refine ⟨?_, by rw [hsz, ha]⟩
    unfold Ow at hs
    apply Array.toList_inj.mp
    rw [Array.toList_map, hs]
    apply List.ext_getElem (by simp [hl, ha])
    intro k h1 h2
    have hk : k < 1600 := by simp at h1 h2; omega
    simp only [List.getElem_map, List.getElem_range]
    by_cases hk64 : k < 64
    · rw [if_pos hk64, List.getElem_append_left (by omega)]
      simp [Array.getD_eq_getD_getElem?, hl, hk64]
    · rw [if_neg hk64, List.getElem_append_right (by omega), List.getElem_map, List.getElem_drop,
        getD_map_srcTr, Array.getElem_toList]
      congr 1
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
      congr 1
      omega

/-! ## A round, Keccak-f[1600], Keccak-256 of a block -/

theorem sim_round (a : WireState) (ha : a.size = 1600) (rc : UInt64) :
    SimR (PcsQuotient.Build.round a rc) (PcsCircuit.Builder.round (a.map srcTr) rc)
      (fun s s' => s' = s.map srcTr ∧ s.size = 1600) := by
  rw [round_eq]
  unfold Q.round PcsCircuit.Builder.round
  refine (sim_theta a ha).bind fun t t' ht => ?_
  obtain ⟨rfl, hts⟩ := ht
  refine (sim_rhoPi t).bind_pure_left fun b hb => ?_
  simp only [hb.1, PcsCircuit.Builder.chiStep, bind_assoc, pure_bind]
  exact (sim_chiA t b hts).bind fun s ss hs => by
    rw [hs.1]
    exact sim_iotaA s hs.2 rc

theorem sim_keccakF (a : WireState) (ha : a.size = 1600) :
    SimR (PcsQuotient.Build.keccakF a) (PcsCircuit.Builder.keccakF (a.map srcTr))
      (fun s s' => s' = s.map srcTr ∧ s.size = 1600) := by
  unfold PcsQuotient.Build.keccakF PcsCircuit.Builder.keccakF
  refine simR_foldlM _ _ _ (fun s s' => s' = s.map srcTr ∧ s.size = 1600) a _ ⟨rfl, ha⟩
    fun rc _ s t hst => ?_
  obtain ⟨rfl, hs⟩ := hst
  exact sim_round s hs rc

/-- **Keccak-256 of a 64-byte block on wires**: the same rows, the same digest wires. -/
theorem sim_keccak256Block (m : List PcsQuotient.Src) :
    SimR (PcsQuotient.Build.keccak256Block m) (PcsCircuit.Builder.keccak256Block (m.map srcTr).toArray)
      (fun o c => c = (o.map srcTr).toArray) := by
  unfold PcsQuotient.Build.keccak256Block PcsCircuit.Builder.keccak256Block
  have hst : (Array.ofFn (n := 1600) fun i : Fin 1600 =>
      if i.val < 512 then m.getD i.val PcsQuotient.Src.zero
      else if i.val = 64 * 8 ∨ i.val = 64 * 16 + 63 then PcsQuotient.Src.one
      else PcsQuotient.Src.zero).map srcTr =
      ((List.range 1600).map fun k =>
        if k < 512 then (m.map srcTr).toArray.getD k .zero
        else if k = 64 * 8 then .one
        else if k = 64 * 16 + 63 then .one
        else .zero).toArray := by
    apply Array.ext (by simp)
    intro k h1 h2
    simp only [Array.size_map, Array.size_ofFn] at h1
    simp only [Array.getElem_map, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map,
      List.getElem_range]
    by_cases hk : k < 512
    · simp only [hk, if_true]
      simp only [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_map]
      cases m[k]? <;> rfl
    · simp only [hk, if_false]
      by_cases h8 : k = 64 * 8
      · simp [h8]
      · by_cases h16 : k = 64 * 16 + 63
        · simp [h16]
        · simp [h8, h16]
  rw [← hst]
  refine (sim_keccakF _ (by simp)).bind fun out out' h => SimR.pure ?_
  rw [h.1]
  apply Array.ext (by simp)
  intro k h1 h2
  simp only [List.size_toArray, List.length_map, List.length_range] at h1
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, getD_map_srcTr]

end Bridge.Circuit
