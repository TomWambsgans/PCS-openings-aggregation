/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

The opening with leanVM's transcript shape against an adversary that chooses the claims. The
construction (one program for every statement, reading the statement as unabsorbed scalars; the
seedings naming the statement; the certificate of every statement) is adapted from leanerVM
`mumbai`'s for leanVM (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR
Apache-2.0: `lean_vm/LeanVM/Protocol/EndToEnd/Sound/Statements.lean`), whose general lemmas it uses.
-/
import WhirBridge.Gaps
import LeanVM.Protocol.EndToEnd.Sound.Statements

/-!
# Claims chosen by the adversary

A statement is a list of claims on a fixed layout (`Stmt L`: every point of `vars` coordinates,
at most `2^46 + 1` claims). Its seeding hashes `pre ‖ claims` (a fixed prefix of the verifier,
`LABEL` and whatever else it binds, then the claims' bytes as `seed` writes them,
`statementBytes` without the root) into the IV, the public digest being zero (`famSeeds`); the
root is read from the proof (`variantProg`). One program serves every
statement (`famProgram`): it reads the claims' count and scalars, never absorbed, then runs
`variantProg` on them; a statement's root history is those reads (`famHistory`), as mumbai's
`anyProgram` does for leanVM.

`family_sound`: an adversary of at most `QA` queries outputs claims and a proof; the verifier
accepts while every candidate table of the extracted root word violates one of **its** claims with
probability at most `(QA + QV) · (2^-128 + 5 (QA + QV) / 2^256)`, `QV = 10122`.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound (reachable_drop after_drop esc_drop boundary_drop
  boundary_append_of wordE kNat kNat_ofBits limb_wordE wordE_injective ofBits_injective
  commits_map_read grindBits_map_read boundary_map_read reachable_of_after_reads extractedFrom_eq
  commitStack_after_ret)
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## Statements -/

/-- A statement: claims on the layout `L`, every point of `vars` coordinates. -/
structure Stmt (L : Layout) where
  claims : List Claim
  short : claims.length ≤ 2 ^ 46 + 1
  wide : ∀ c ∈ claims, c.point.length = L.vars

theorem Stmt.ext' {L : Layout} {x x' : Stmt L} (h : x.claims = x'.claims) : x = x' := by
  cases x; cases x'; cases h; rfl

/-- The claims' scalars: each point, then its value. -/
def flat (cs : List Claim) : List E := cs.flatMap fun c ↦ c.point ++ [c.value]

/-- `J` claims of `w` coordinates from their scalars. -/
def chunkClaims (w : ℕ) : ℕ → List E → List Claim
  | 0, _ => []
  | J + 1, xs => ⟨xs.take w, xs.getD w 0⟩ :: chunkClaims w J (xs.drop (w + 1))

theorem chunkClaims_flat (w : ℕ) :
    ∀ cs : List Claim, (∀ c ∈ cs, c.point.length = w) → chunkClaims w cs.length (flat cs) = cs
  | [], _ => rfl
  | c :: cs, h => by
    have hc := h c (List.mem_cons_self ..)
    have hcs := chunkClaims_flat w cs fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    have hf : flat (c :: cs) = (c.point ++ [c.value]) ++ flat cs := by simp [flat]
    have h1 : ((c.point ++ [c.value]) ++ flat cs).take w = c.point := by
      rw [List.append_assoc, List.take_left' hc]
    have h2 : ((c.point ++ [c.value]) ++ flat cs).getD w 0 = c.value := by
      rw [List.append_assoc, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), hc, Nat.sub_self]
      simp
    have h3 : ((c.point ++ [c.value]) ++ flat cs).drop (w + 1) = flat cs := by
      rw [show w + 1 = (c.point ++ [c.value]).length by simp [hc], List.drop_left]
    show chunkClaims w (cs.length + 1) (flat (c :: cs)) = c :: cs
    rw [hf, chunkClaims, h1, h2, h3, hcs]

theorem length_flat (w : ℕ) :
    ∀ cs : List Claim, (∀ c ∈ cs, c.point.length = w) → (flat cs).length = cs.length * (w + 1)
  | [], _ => by simp [flat]
  | c :: cs, h => by
    have hc := h c (List.mem_cons_self ..)
    have := length_flat w cs fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    simp only [flat, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      hc] at this ⊢
    rw [this]
    ring

/-! ## The program of every statement -/

/-- Read `n` scalars, then continue with them. -/
def readScalarsK : ℕ → (List E → Prog Bool) → Prog Bool
  | 0, k => k []
  | n + 1, k => .read fun e ↦ readScalarsK n fun es ↦ k (e :: es)

theorem after_readScalarsK (k : List E → Prog Bool) :
    ∀ (xs : List E) (rest : List Ev),
      (readScalarsK xs.length k).after (xs.map Ev.read ++ rest) = (k xs).after rest
  | [], rest => rfl
  | x :: xs, rest => by
    simp only [List.length_cons, readScalarsK, List.map_cons, List.cons_append, Prog.after]
    exact after_readScalarsK (fun xs' ↦ k (x :: xs')) xs rest

/-- **The program of every statement**: the claims' count and scalars, read, then `variantProg`
on the claims. -/
def famProgram (L : Layout) (R : ℕ) : Prog Bool :=
  .read fun n ↦ readScalarsK (kNat (n.limb 0) * (L.vars + 1)) fun xs ↦
    variantProg L R (chunkClaims L.vars (kNat (n.limb 0)) xs)

variable {L : Layout} {R : ℕ}

/-- A statement's scalars: the count, then the claims'. -/
def famScalars (x : Stmt L) : List E := wordE (K.ofBits x.claims.length) :: flat x.claims

/-- **A statement's root**: the history of its reads. -/
def famHistory (x : Stmt L) : List Ev := (famScalars x).map Ev.read

theorem claims_lt (x : Stmt L) : x.claims.length < 2 ^ 64 :=
  lt_of_le_of_lt x.short (by norm_num)

theorem after_famHistory (x : Stmt L) :
    (famProgram L R).after (famHistory x) = some (variantProg L R x.claims) := by
  have hlen := length_flat L.vars x.claims x.wide
  simp only [famHistory, famScalars, List.map_cons, famProgram, Prog.after, limb_wordE,
    kNat_ofBits (claims_lt x)]
  rw [← hlen, ← List.append_nil ((flat x.claims).map Ev.read), after_readScalarsK,
    chunkClaims_flat L.vars x.claims x.wide, after_nil']

theorem nodeAt_famHistory (x : Stmt L) :
    nodeAt (famProgram L R) (famHistory x) = variantProg L R x.claims := by
  simp [nodeAt, after_famHistory]

theorem commits_famHistory (x : Stmt L) : commits (famHistory x) = [] := commits_map_read _

theorem length_famHistory (x : Stmt L) :
    (famHistory x).length = x.claims.length * (L.vars + 1) + 1 := by
  simp only [famHistory, famScalars, List.length_map, List.length_cons,
    length_flat L.vars x.claims x.wide]

/-- A statement's root is a root of `famProgram`. -/
theorem rootOk_famHistory (x : Stmt L) : RootOk (famProgram L R) (famHistory x) := by
  have ha := after_famHistory (R := R) x
  exact ⟨reachable_of_after_reads _ ha, boundary_map_read (by simp [famScalars]),
    grindBits_map_read _, commits_map_read _, by simp [ha]⟩

/-- **Roots are prefix-free**: two roots on one history are one statement's. -/
theorem fam_eq_of_prefix {x x' : Stmt L} {h : List Ev} (hx : famHistory x <+: h)
    (hx' : famHistory x' <+: h) : x = x' := by
  have hhead : ∀ {y y' : Stmt L}, famHistory y <+: famHistory y' →
      y.claims.length = y'.claims.length := by
    intro y y' hp
    have h0 := hp.getElem (i := 0) (by simp [famHistory, famScalars])
    simp only [famHistory, famScalars, List.map_cons, List.getElem_cons_zero,
      Ev.read.injEq] at h0
    exact ofBits_injective (claims_lt _) (claims_lt _) (wordE_injective h0)
  have heq : famHistory x = famHistory x' := by
    rcases List.prefix_or_prefix_of_prefix hx hx' with hp | hp
    · exact hp.eq_of_length (by rw [length_famHistory, length_famHistory, hhead hp])
    · exact (hp.eq_of_length (by rw [length_famHistory, length_famHistory, hhead hp])).symm
  have hs : famScalars x = famScalars x' :=
    List.map_injective_iff.mpr (fun a b h ↦ Ev.read.inj h) heq
  simp only [famScalars, List.cons.injEq] at hs
  obtain ⟨hl, hs⟩ := hs
  have hlen : x.claims.length = x'.claims.length :=
    ofBits_injective (claims_lt _) (claims_lt _) (wordE_injective hl)
  apply Stmt.ext'
  rw [← chunkClaims_flat L.vars x.claims x.wide, ← chunkClaims_flat L.vars x'.claims x'.wide,
    hs, hlen]

/-! ## The seedings -/

/-- The claims' bytes, as `seed` writes them after the root. -/
def claimsBytes (cs : List Claim) : Bytes := (flat cs).flatMap scalarBytes

theorem scalarBytes_length (x : E) : (scalarBytes x).length = 24 := by
  simp [scalarBytes, kBytes_length]

theorem scalarBytes_injective : Function.Injective scalarBytes := by
  intro x y h
  unfold scalarBytes at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp [kBytes_length])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [kBytes_length])
  apply E.ext
  intro i
  fin_cases i
  · exact LeanVM.Protocol.Compile.Rom.kBytes_injective h1
  · exact LeanVM.Protocol.Compile.Rom.kBytes_injective h2
  · exact LeanVM.Protocol.Compile.Rom.kBytes_injective h3

theorem length_flatMap_scalarBytes : ∀ l : List E, (l.flatMap scalarBytes).length = 24 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, scalarBytes_length, length_flatMap_scalarBytes l,
      List.length_cons]
    ring

/-- The claims' bytes name the statement. -/
theorem stmt_eq_of_bytes {x x' : Stmt L} (h : claimsBytes x.claims = claimsBytes x'.claims) :
    x = x' := by
  have hl : (flat x.claims).length = (flat x'.claims).length := by
    have := congrArg List.length h
    simp only [claimsBytes, length_flatMap_scalarBytes] at this
    omega
  have hf := LeanVM.Protocol.Compile.Rom.flatMap_inj_of_length scalarBytes_length
    scalarBytes_injective hl h
  have hJ : x.claims.length = x'.claims.length := by
    rw [length_flat L.vars _ x.wide, length_flat L.vars _ x'.wide] at hl
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) hl
  apply Stmt.ext'
  rw [← chunkClaims_flat L.vars x.claims x.wide, ← chunkClaims_flat L.vars x'.claims x'.wide, hf,
    hJ]

/-- A statement's seeding: the IV `H(pre ‖ claims)`, then the permutation of the IV and zero.
`pre` is any fixed prefix of the verifier: `LABEL`, and whatever else it binds (a version, the
layout's id, `log_n`, the rate) in a form fixed for the verifier. -/
def famSeed (pre : Bytes) (x : Stmt L) : Seed where
  hs := [fun _ ↦ pre ++ claimsBytes x.claims]
  fin ds := seedInput (ds.getD 0 default) default

variable (L) in
/-- **The seedings of the statements.** -/
def famSeeds (pre : Bytes) : Seeds (Stmt L) where
  seed := famSeed pre
  root := famHistory
  offs := []
  refs x ds hds i hi := by
    have hl : (famSeed pre x).hs.length = 1 := rfl
    rw [hl] at hds
    have hd0 : ds.getD 0 default = ds[0] := by simp [List.getD_eq_getElem?_getD, hds]
    rw [hds] at hi
    interval_cases i
    left
    show laneDigest (seedInput (ds.getD 0 default) default) = ds[0]
    rw [laneDigest_seedInput, hd0]
  cap0 x ds := capOf_seedInput _ _
  inj H hH x x' ds ds' ha ha' he := by
    have hl : ds.length = 1 := ha.1
    have hl' : ds'.length = 1 := ha'.1
    have hiv : ds.getD 0 default = ds'.getD 0 default := by
      have := congrArg laneDigest he
      simpa [famSeed, laneDigest_seedInput] using this
    obtain ⟨f0, hf0, hH0⟩ := ha.2 0 (by omega)
    obtain ⟨f0', hf0', hH0'⟩ := ha'.2 0 (by omega)
    simp only [famSeed, List.getElem?_cons_zero, Option.some.injEq] at hf0 hf0'
    subst hf0 hf0'
    have e0 : ds[0] = ds'[0] := by
      simpa [List.getD_eq_getElem?_getD, hl, hl'] using hiv
    rw [e0] at hH0
    exact stmt_eq_of_bytes (List.append_cancel_left (hH _ _ _ hH0 hH0'))

/-! ## The certificate of every statement -/

section Cert

variable (L R) (hw : Whir.Admissible L.logN R)

/-- A statement's certificate. -/
noncomputable def stmtCert (x : Stmt L) : Cert (variantProg L R x.claims) :=
  variantCert L R hw x.claims x.short

/-- Doom for every statement: past a statement's root, its certificate's doom on the rest. -/
def famD (h : List Ev) : Prop :=
  ∃ x : Stmt L, famHistory x <+: h ∧
    (stmtCert L R hw x).D (h.drop (famHistory x).length)

open Classical in
/-- The escape bound for every statement: its certificate's past its root, `0` elsewhere. -/
noncomputable def famε (h : List Ev) : ℝ≥0∞ :=
  if hx : ∃ x : Stmt L, famHistory x <+: h then
    (stmtCert L R hw hx.choose).ε (h.drop (famHistory hx.choose).length)
  else 0

theorem famD_iff (x : Stmt L) (h' : List Ev) :
    famD L R hw (famHistory x ++ h') ↔ (stmtCert L R hw x).D h' := by
  constructor
  · rintro ⟨x', hx', hD⟩
    obtain rfl := fam_eq_of_prefix hx' (List.prefix_append _ _)
    simpa using hD
  · intro hD
    exact ⟨x, List.prefix_append _ _, by simpa using hD⟩

theorem famε_eq (x : Stmt L) (h' : List Ev) :
    famε L R hw (famHistory x ++ h') = (stmtCert L R hw x).ε h' := by
  unfold famε
  split
  · rename_i hx
    rw [fam_eq_of_prefix hx.choose_spec (List.prefix_append _ _)]
    simp
  · rename_i hx
    exact absurd ⟨x, List.prefix_append _ _⟩ hx

theorem famD_split {h : List Ev} (hD : famD L R hw h) :
    ∃ (x : Stmt L) (h' : List Ev), h = famHistory x ++ h' ∧ (stmtCert L R hw x).D h' := by
  obtain ⟨x, ⟨h', rfl⟩, hD⟩ := hD
  exact ⟨x, h', rfl, by simpa using hD⟩

/-- **The certificate of every statement.** -/
noncomputable def famCert : Cert (famProgram L R) where
  D := famD L R hw
  ε := famε L R hw
  read := by
    intro h k e hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := famD_split L R hw hD
    have hax := after_famHistory (R := R) x
    rw [List.append_assoc, famD_iff]
    exact (stmtCert L R hw x).read e
      (reachable_drop hax (commits_famHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx
  grind := by
    intro h b k hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := famD_split L R hw hD
    have hax := after_famHistory (R := R) x
    rw [List.append_assoc, famD_iff]
    exact (stmtCert L R hw x).grind
      (reachable_drop hax (commits_famHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx
  commit := by
    intro h ht w k word hr ha hws hD
    obtain ⟨x, h', rfl, hDx⟩ := famD_split L R hw hD
    have hax := after_famHistory (R := R) x
    rw [List.append_assoc, famD_iff]
    exact (stmtCert L R hw x).commit word
      (reachable_drop hax (commits_famHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hws hDx
  group := by
    intro h p hr hb ha hp hD
    obtain ⟨x, h', rfl, hDx⟩ := famD_split L R hw hD
    have hax := after_famHistory (R := R) x
    rw [esc_drop (h₀ := famHistory x) (commits_famHistory x) (famD_iff L R hw x), famε_eq]
    exact (stmtCert L R hw x).group
      (reachable_drop hax (commits_famHistory x) hr h' rfl)
      (boundary_drop hb) (by rwa [after_drop hax] at ha) hp hDx
  final := by
    intro h hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := famD_split L R hw hD
    have hax := after_famHistory (R := R) x
    exact (stmtCert L R hw x).final
      (reachable_drop hax (commits_famHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx

theorem grindBits_fam (x : Stmt L) (h' : List Ev) :
    grindBits (famHistory x ++ h') = grindBits h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · rw [List.append_nil]; exact grindBits_map_read _
  · rw [List.concat_eq_append, ← List.append_assoc]
    simp [grindBits]

/-- **The certificate's bound**: `2^-128` per group. -/
theorem famCert_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (famCert L R hw).ε h ≤ εWhir := by
  by_cases hx : ∃ x : Stmt L, famHistory x <+: h
  · obtain ⟨x, h', rfl⟩ : ∃ x h', h = famHistory x ++ h' := by
      obtain ⟨x, h', he⟩ := hx
      exact ⟨x, h', he.symm⟩
    show _ * famε L R hw _ ≤ _
    rw [famε_eq, grindBits_fam]
    exact variantCert_bound L R hw x.claims x.short h'
  · show _ * famε L R hw _ ≤ _
    simp only [famε, hx, ↓reduceDIte, mul_zero, zero_le]

end Cert

/-! ## The theorem -/

theorem verifierFam_fam (pre : Bytes) (z : Stmt L × Proof) :
    verifierFam (famSeeds L pre) (famProgram L R) z =
      verifierComp (famSeed pre z.1) (variantProg L R z.1.claims) z.2 := by
  simp only [verifierFam, famSeeds, nodeAt_famHistory]

theorem isTotalQueryBound_fam (pre : Bytes) (z : Stmt L × Proof) :
    IsTotalQueryBound (verifierFam (famSeeds L pre) (famProgram L R) z) variantQueries := by
  rw [verifierFam_fam pre]
  exact isTotalQueryBound_verifierComp (costLE_variant L R z.1.claims) (famSeed pre z.1) z.2

/-- The event: every candidate table of the extracted root word violates one of the statement's
claims. -/
def FamTableDoomed (pre : Bytes) (z : Stmt L × Proof) (c : KeccakCalls.QueryCache) : Prop :=
  ∀ q ∈ Candidates L.logN R (code₀ L.logN R).thr
      (LeanVM.Protocol.Whir.Sound.wordOf (commits (rootEvents (extractedHistory
        (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) (famSeed pre z.1) (variantProg L R z.1.claims)
          z.2))) 0),
    ∃ cl ∈ z.1.claims, L.tableEval q cl.point ≠ cl.value

/-- **Fiat-Shamir soundness of the opening with leanVM's transcript shape, for claims the
adversary chooses**: an adversary of at most `QA` queries outputs claims on the layout `L` and a
proof; the verifier accepts while every candidate table of the extracted root word violates one
of its claims with probability at most `(QA + QV) · (2^-128 + 5 (QA + QV) / 2^256)`. -/
theorem family_sound (hw : Whir.Admissible L.logN R) (hL : L.Valid) (pre : Bytes)
    (A : OracleComp KeccakCalls (Stmt L × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam (famSeeds L pre) (famProgram L R))}[
        z.1.2 = true ∧ FamTableDoomed (R := R) pre z.1.1 z.2] ≤
      (QA + variantQueries : ℕ) * (εWhir + failBound (famSeeds L pre) (QA + variantQueries)) := by
  refine romSound_of_imp (famProgram L R) (famCert L R hw) (famSeeds L pre)
    (fun x ↦ rootOk_famHistory x) εWhir (famCert_bound L R hw) A QA hA variantQueries
    (isTotalQueryBound_fam pre) (FamTableDoomed pre) fun z c hv hbad ↦ ?_
  have hseed : (famSeeds L pre).seed z.1 = famSeed pre z.1 := rfl
  have hroot : (famSeeds L pre).root z.1 = famHistory z.1 := rfl
  rw [hseed, hroot, nodeAt_famHistory] at hv
  obtain ⟨e, rest, hhist, hce⟩ := extracted_root (L := L) (R := R) (claims := z.1.claims) hv
  have hws := (Sound.after_extractedHistory _ _ hv).2
  rw [hhist] at hws
  unfold Doomed
  rw [hseed, hroot, nodeAt_famHistory]
  refine ⟨famHistory z.1 ++ [e], ?_, by rw [List.length_append]; omega, ?_, ?_⟩
  · rw [extractedFrom_eq _ _ _ _ _ _ hv, hhist]
    exact (List.prefix_append_right_inj _).mpr ⟨rest, rfl⟩
  · obtain ⟨level, rest', W, -, he⟩ := commitStack_after_ret hce
    rw [List.singleton_inj.1 he]
    exact boundary_append_of (h := []) trivial
  · refine (famD_iff L R hw z.1 [e]).2 (variantCert_D_root L R hw z.1.claims z.1.short hce
      ((openingDoom_iff L hL R z.1.claims z.1.wide _).2
        ⟨shapeOK_root L R hw hce fun ht w W he ↦ hws ht w W (he ▸ List.mem_cons_self ..), ?_⟩))
    have h := hbad
    unfold FamTableDoomed rootEvents at h
    rw [hhist] at h
    simpa using h

/-- **The numbers**: against `2^64` queries, the bound of `family_sound` is at most `2^-63`. -/
theorem family_bound_le (L : Layout) (pre : Bytes) {QA : ℕ} (hQ : QA ≤ 2 ^ 64) :
    ((QA + variantQueries : ℕ) : ℝ≥0∞) * (εWhir + failBound (famSeeds L pre) (QA + variantQueries)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 63 :=
  bound_le _ rfl hQ

end WhirBridge
