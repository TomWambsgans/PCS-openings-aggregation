-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields, `y`, and through `Completeness.Opening` its WHIR completeness.
import Completeness.Wiring
import Completeness.Circuit

/-!
# End-to-end completeness

**The deployed verifier** (`deployedVerify`): `protocol::verify` then `verify_openings`, on a
statement `(y, root)`, against the circuit's commitment `indexRoot`: the transcript's challenges
from the proof's roots and values (`Transcript`: any function of what was sent before each
challenge, `transcript.rs`'s Keccak-256 chain being one), `reduce`'s own check (`RustCheck`: every
`1 + w_k(t)`, the copy denominator and the rows' polynomial nonzero, else `VerifyError::Degenerate`),
then the four claims (`witnessClaim`, `wiringClaim`, `quotientClaim`, `sumClaim`, at the points and
with the values `claims_iff_accepts` gives, the coordinate-by-coordinate comparison with `reduce`
being F1's review) opened by three openings, the quotient table's two claims in one.

**The honest prover** (`honestRun`, `honestProve`): from a secret (`x`, the path), the
assignment F0b's circuit computes (`MembershipCircuit.assign`), masks `m` and paddings `padW`,
`padQ` (the prover's randomness, any values): the witness table (cells, masks), its stack and root,
the challenges, F1's honest second message (`Params.honest`), the quotient table (its limbs), its
stack and root, `t`, the four values `opened g t` and the wiring polynomial at `t`, `ρ`, and the
three honest openings; `none` only if an opening's proof of work found no nonce.

**`completeness_deployed`**: for every hash function `H` and permutation `F` (the deployed Keccak
included), every transcript, every secret, every randomness, if the honest prover returns a proof
and its challenges are not degenerate (`¬ BadAB`, `¬ Degenerate`, at most `(17 · 2^24 + 8)` of every
`2^192 · 2^192 · 2^192` triples `(α, β, t)`, `Reduction.bad_fraction_le`), **the deployed verifier
accepts it**, given:

* `M : MembershipCircuit` (F0b: the deployed circuit, its assignment, Keccak correctness forward)
  on an instance whose wiring keeps what its cells carry (`hw`, `WiringKeeps`: `wiringOf M.C`, or
  the deployed σ), the bit weights `coordinate_weight`'s (`hc`);
* the instance's Cantor basis in `K` (`hB`: `beta()` is `F64`'s);
* the witness and quotient openings `Wi`, `Qo` (`OpeningSystem`s holding their tables' chunks): for
  the redesigned hidden layouts, `HiddenOpening.toSystem` of what F2's update is to give
  (`completeness_hidden`); the wiring opening is `wiringOpening`, proven.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Semantics

namespace Completeness

open QuotientSecurity

/-! ## `E`'s extension coordinate -/

theorem one_add_y_ne : (1 + y : E) ≠ 0 := by
  intro h
  have h3 := y_pow_three
  have hy : y = 1 := by linear_combination h - LeanVM.Protocol.Whir.Complete.two_eq_zero_E
  rw [hy] at h3
  exact one_ne_zero (by linear_combination -h3 : (1 : E) = 0)

theorem one_add_y_sq_ne : (1 + y ^ 2 : E) ≠ 0 := by
  intro h
  have h3 := y_pow_three
  have hy2 : y ^ 2 = 1 := by linear_combination h - LeanVM.Protocol.Whir.Complete.two_eq_zero_E
  exact one_ne_zero (by linear_combination -h3 + y * hy2 : (1 : E) = 0)

/-! ## The deployed verifier -/

/-- **The reduction's Fiat–Shamir transcript**: each challenge a function of what the proof sent
before it (`transcript.rs`: `(α, β, γ)` after the witness root, `t` after the quotient root, `ρ`
after the five values). -/
structure Transcript where
  abc : Statement → Digest → E × E × E
  t : Statement → Digest → Digest → E
  ρ : Statement → Digest → Digest → (Fin 4 → E) → E → E

/-- The witness claim (`reduce`'s `witness`): at `[ρ, ρ^2, u_2, …, u_24]`, the opened values. -/
noncomputable def witnessClaim (t ρ : E) (a : Fin 4 → E) : WhirBridge.Claim :=
  ⟨List.ofFn (Fin.cons ρ (Fin.cons (ρ ^ 2) (claimPoint 2 (22 + 1) t)) : Fin (22 + 1 + 1 + 1) → E),
    (∑ j, Params.opening ρ j * a j) / claimScale 2 (22 + 1) t⟩

/-- The wiring claim (`reduce`'s `wiring`): at `u_0, …, u_23`, the fifth value. -/
noncomputable def wiringClaim (t s : E) : WhirBridge.Claim :=
  ⟨List.ofFn (claimPoint 0 (22 + 2) t), s / claimScale 0 (22 + 2) t⟩

/-- The quotient claim (`reduce`'s `quotient`). -/
noncomputable def quotientClaim (I : Instance E) (α β γ t ρ : E) (a : Fin 4 → E) (s : E) :
    WhirBridge.Claim :=
  ⟨List.ofFn (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) t)
      (I.params.vCells.eval t / I.params.claimDen α β t a s)) ρ) (y / (1 + y)))
      (y ^ 2 / (1 + y ^ 2)) : Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → E),
    I.params.claimValue α β γ t ρ a s / ((1 + y) * (1 + y ^ 2)) / claimScale 0 (22 + 2 + 1 + 1) t⟩

/-- The sum claim (`sum_point`, `scale · target`). -/
noncomputable def sumClaim (I : Instance E) (stmt : Fin 8 → E) (γ : E) : WhirBridge.Claim :=
  ⟨List.ofFn (sumPoint (22 + 2) y), I.params.target stmt γ / ((1 + y) * (1 + y ^ 2))⟩

/-- **A proof**: the two roots, the five values, the three openings. -/
structure DeployedProof where
  r₁ : Digest
  r₂ : Digest
  a : Fin 4 → E
  s : E
  πW : Proof
  πσ : Proof
  πQ : Proof

/-- **The deployed verifier** (`protocol::verify`, then `verify_openings`), the statement's words
those of `(y, root)` (`statementWords`, `Statement::halves`). -/
def deployedVerify (I : Instance E) (x Y : E) (tr : Transcript) (W Wi Qo : OpeningSystem)
    (H : Bytes → Digest) (F : KeccakState → KeccakState) (indexRoot : Digest) (st : Statement)
    (π : DeployedProof) : Prop :=
  let abc := tr.abc st π.r₁
  let t := tr.t st π.r₁ π.r₂
  let ρ := tr.ρ st π.r₁ π.r₂ π.a π.s
  Reduction.RustCheck I abc.1 abc.2.1 t π.a π.s ∧
    Wi.verify H F π.r₁ [witnessClaim t ρ π.a] π.πW = true ∧
    W.verify H F indexRoot [wiringClaim t π.s] π.πσ = true ∧
    Qo.verify H F π.r₂ [quotientClaim I abc.1 abc.2.1 abc.2.2 t ρ π.a π.s,
      sumClaim I (statementWords x Y st.y st.root) abc.2.2] π.πQ = true

/-! ## The honest prover -/

/-- The cells' bits in `K`: what each cell carries in the circuit's computation. -/
noncomputable def cellBitsK (M : MembershipCircuit) (s : Secret) : (Fin (22 + 2) → Bool) → K :=
  fun z => bitF ((M.C.cellSrc z).bval (M.assign s))

open Classical in
/-- The gate quotient's polynomial over `K` (the honest one is over `K`, `qGate_mem_lifts`). -/
noncomputable def qGateKOf (R : Params.Quotients E) : K[X] :=
  if h : R.qGate ∈ lifts (algebraMap K E) then Classical.choose ((lifts_iff_set_range _).mp h)
  else 0

/-- What the honest prover computes before its openings. -/
structure HonestRun (Wi Qo : OpeningSystem) where
  cW : (Fin (22 + 2 + 1) → Bool) → K
  g : Fin 4 → E[X]
  qW : Column Wi.logN
  r₁ : Digest
  α : E
  β : E
  γ : E
  R : Params.Quotients E
  cQ : (Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → K
  qQ : Column Qo.logN
  r₂ : Digest
  t : E
  a : Fin 4 → E
  sv : E
  ρ : E

/-- **The honest prover's run** (`prove_with_randomness`). -/
noncomputable def honestRun (I : Instance E) (BK : CantorBasis K (22 + 2)) (M : MembershipCircuit)
    (tr : Transcript) (Wi Qo : OpeningSystem) (H : Bytes → Digest) (s : Secret)
    (m : Fin 4 → Fin 3 → K) (padW padQ : ℕ → ℕ → K) : HonestRun Wi Qo :=
  let cW := witnessTable BK (cellBitsK M s) m
  let g := witnessOfTable fun b => algebraMap K E (cW b)
  let qW := Wi.stack (natTable cW) padW
  let r₁ := Wi.root H qW
  let abc := tr.abc s.statement r₁
  let R := Params.honest I.params g abc.1 abc.2.1 abc.2.2
  let cQ := quotientTable limbE (22 + 2 + 1 + 1) R (qGateKOf R)
  let qQ := Qo.stack (natTable cQ) padQ
  let r₂ := Qo.root H qQ
  let t := tr.t s.statement r₁ r₂
  let a := Params.opened g t
  let sv := I.params.sigmaPoly.eval t
  ⟨cW, g, qW, r₁, abc.1, abc.2.1, abc.2.2, R, cQ, qQ, r₂, t, a, sv, tr.ρ s.statement r₁ r₂ a sv⟩

/-- The setup's wiring stack (`Index::new`). -/
noncomputable def wiringStack (I : Instance E) (BK : CantorBasis K (22 + 2)) : Column wL.logN :=
  wiringOpening.stack (natTable (wiringTableK BK I.wiring)) fun _ _ => 0

/-- **The honest prover** (`prove`, then `open`): the run, then the three openings. -/
noncomputable def honestProve (I : Instance E) (x Y : E) (BK : CantorBasis K (22 + 2)) (M : MembershipCircuit)
    (tr : Transcript) (Wi Qo : OpeningSystem) (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (fuel : ℕ) (s : Secret) (m : Fin 4 → Fin 3 → K) (padW padQ : ℕ → ℕ → K) :
    Option DeployedProof :=
  let run := honestRun I BK M tr Wi Qo H s m padW padQ
  (Wi.prove H F run.qW [witnessClaim run.t run.ρ run.a] fuel).bind fun πW =>
    (wiringOpening.prove H F (wiringStack I BK) [wiringClaim run.t run.sv] fuel).bind fun πσ =>
      (Qo.prove H F run.qQ [quotientClaim I run.α run.β run.γ run.t run.ρ run.a run.sv,
          sumClaim I (statementWords x Y s.statement.y s.statement.root) run.γ] fuel).map
        fun πQ => ⟨run.r₁, run.r₂, run.a, run.sv, πW, πσ, πQ⟩

/-! ## Completeness -/

theorem algebraMap_bitF (b : Bool) : algebraMap K E (bitF b : K) = (bitF b : E) := by
  cases b <;> simp [bitF]

/-- The honest first message's cells are the circuit's computation. -/
theorem cellsOf_honestRun (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) (M : MembershipCircuit) (tr : Transcript)
    (Wi Qo : OpeningSystem) (H : Bytes → Digest) (s : Secret) (m : Fin 4 → Fin 3 → K)
    (padW padQ : ℕ → ℕ → K) :
    I.cellsOf (honestRun I BK M tr Wi Qo H s m padW padQ).g = M.C.cellsOfBits (M.assign s) := by
  funext z
  show I.cellsOf (witnessOfTable fun b => algebraMap K E (witnessTable BK (cellBitsK M s) m b)) z = _
  rw [cellsOf_honest (algebraMap K E) I BK hB]
  exact algebraMap_bitF _

/-- **The four claims of an honest run hold of its tables, by numbers**, at non-degenerate
challenges: F1's completeness (`Reduction.honest_accepts`), passed to the tables
(`accepts_table_of_honest`, `slots_honest`), read as claims (`claims_iff_accepts`), then by
numbers (`mle_eq_tableEvalN`). -/
theorem honest_claims (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) (M : MembershipCircuit) {x Y : E}
    (hc : I.c = coordWeight x Y) (hw : WiringKeeps I.wiring M.C) (tr : Transcript)
    (Wi Qo : OpeningSystem) (H : Bytes → Digest) (s : Secret) (m : Fin 4 → Fin 3 → K)
    (padW padQ : ℕ → ℕ → K)
    (hab : ¬ Reduction.BadAB I (honestRun I BK M tr Wi Qo H s m padW padQ).g
      (honestRun I BK M tr Wi Qo H s m padW padQ).α (honestRun I BK M tr Wi Qo H s m padW padQ).β)
    (ht : ¬ Reduction.Degenerate I (honestRun I BK M tr Wi Qo H s m padW padQ).g
      (honestRun I BK M tr Wi Qo H s m padW padQ).α (honestRun I BK M tr Wi Qo H s m padW padQ).β
      (honestRun I BK M tr Wi Qo H s m padW padQ).t) :
    let run := honestRun I BK M tr Wi Qo H s m padW padQ
    let stmtW := statementWords x Y s.statement.y s.statement.root
    tableEvalN 25 (natTable run.cW) (witnessClaim run.t run.ρ run.a).point =
        (witnessClaim run.t run.ρ run.a).value ∧
      tableEvalN 24 (natTable (wiringTableK BK I.wiring)) (wiringClaim run.t run.sv).point =
        (wiringClaim run.t run.sv).value ∧
      tableEvalN 30 (natTable run.cQ)
          (quotientClaim I run.α run.β run.γ run.t run.ρ run.a run.sv).point =
        (quotientClaim I run.α run.β run.γ run.t run.ρ run.a run.sv).value ∧
      tableEvalN 30 (natTable run.cQ) (sumClaim I stmtW run.γ).point =
        (sumClaim I stmtW run.γ).value := by
  intro run stmtW
  -- The relation.
  have hsat : I.Relation stmtW (I.cellsOf run.g) := by
    rw [cellsOf_honestRun I BK hB M tr Wi Qo H s m padW padQ]
    exact honest_relation M I hc hw s
  -- F1: the honest messages are accepted.
  have hacc := Reduction.honest_accepts I stmtW run.g hsat run.α run.β run.γ run.t run.ρ hab ht
  -- The second message's degrees and the gate quotient over `K`.
  have hg22 : ∀ j, (run.g j).natDegree ≤ 2 ^ 22 + 2 :=
    natDegree_witnessOfTable_le (algebraMap K E) BK (cellBitsK M s) m
  obtain ⟨hh, hq, hgd⟩ := honest_degrees I run.g hg22 run.α run.β run.γ
  have hmem : run.R.qGate ∈ lifts (algebraMap K E) :=
    qGate_mem_lifts (algebraMap K E) I BK hB run.g
      (witnessOfTable_mem_lifts (algebraMap K E) I BK hB _) run.α run.β run.γ
  have hqK : (qGateKOf run.R).map (algebraMap K E) = run.R.qGate := by
    unfold qGateKOf
    rw [dif_pos hmem]
    exact Classical.choose_spec ((lifts_iff_set_range _).mp hmem)
  have hgK : (qGateKOf run.R).natDegree < 7 * 2 ^ 22 + 64 := by
    rw [← natDegree_map_eq_of_injective (algebraMap K E).injective, hqK]
    exact lt_of_le_of_lt hgd (by norm_num)
  obtain ⟨s1, s2, s3, s4⟩ := slots_honest limbE (22 + 2 + 1 + 1) (by norm_num) run.R (qGateKOf run.R)
    hh (lt_of_le_of_lt hq (by norm_num)) hgK
  -- The table holding the second message is accepted.
  have hacc' := accepts_table_of_honest (m := 22 + 2) I.params rfl limbE.Y
    (fun b => limbE.ι (run.cQ b)) stmtW run.g run.α run.β run.γ run.t run.ρ
    (I.params.sigmaPoly.eval run.t) (Params.opened run.g run.t) s1 s2 (s3.trans hqK) s4 hacc
  -- The four claims on the tables.
  have htt : ∀ i : Fin (22 + 2 + 1 + 1), 1 + sq^[(i : ℕ)] run.t ≠ 0 := fun i h =>
    ht (Or.inl ⟨i, h⟩)
  have hnz : I.params.claimDen run.α run.β run.t (Params.opened run.g run.t)
      (I.params.sigmaPoly.eval run.t) * I.params.vRows.eval run.t ≠ 0 := by
    rw [Reduction.claimDen_honest]
    exact fun h => ht (Or.inr h)
  have hσ := sigmaPoly_eq_wiringTableK (algebraMap K E) I BK hB
  obtain ⟨c1, c2, c3, c4⟩ := (claims_iff_accepts I.params I.basis le24 I.cellEquiv
    (fun x => cantorCells_point (n := 22) I.basis le24 x) rfl
    (fun b => algebraMap K E (run.cW b)) (fun b => algebraMap K E (wiringTableK BK I.wiring b)) hσ
    (fun b => limbE.ι (run.cQ b)) y one_add_y_ne (by simpa using one_add_y_sq_ne) stmtW
    run.α run.β run.γ run.t run.ρ (I.params.sigmaPoly.eval run.t) (Params.opened run.g run.t)
    htt hnz).mpr hacc'
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mle_eq_tableEvalN run.cW _).symm.trans c1
  · exact (mle_eq_tableEvalN (wiringTableK BK I.wiring) _).symm.trans c2
  · exact (mle_eq_tableEvalN run.cQ _).symm.trans c3
  · exact (mle_eq_tableEvalN run.cQ _).symm.trans c4

/-- **End-to-end completeness.** For every hash function `H` and permutation `F`, transcript `tr`,
secret `s` and prover randomness (`m`, `padW`, `padQ`): if the honest prover returns a proof `π`
and its challenges `(α, β, t)` are not degenerate, the deployed verifier accepts `π` for the
statement `s` proves, against the circuit's commitment. Given F0b's circuit (`M`, on a wiring
keeping what its cells carry, `hw`), the deployed weights (`hc`) and basis (`hB`), and the witness and quotient
openings `Wi`, `Qo` holding their chunks (`HiddenOpening.toSystem` for the redesigned layouts;
the wiring opening is proven). -/
theorem completeness_deployed (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) (M : MembershipCircuit) {x Y : E}
    (hc : I.c = coordWeight x Y) (hw : WiringKeeps I.wiring M.C) (tr : Transcript)
    (Wi Qo : OpeningSystem) (hWv : Wi.vars = 25) (hQv : Qo.vars = 30)
    (hWheld : ∀ t, InChunks (WhirBridge.cellVars WhirBridge.logRows)
      [(0, 2 ^ WhirBridge.cellVars WhirBridge.logRows), (1, 16)] t → Wi.Held t)
    (hQheld : ∀ t, InChunks (WhirBridge.cellVars WhirBridge.logRows) qChunks t → Qo.Held t)
    (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) (s : Secret)
    (m : Fin 4 → Fin 3 → K) (padW padQ : ℕ → ℕ → K) (π : DeployedProof)
    (hπ : honestProve I x Y BK M tr Wi Qo H F fuel s m padW padQ = some π)
    (hab : ¬ Reduction.BadAB I (honestRun I BK M tr Wi Qo H s m padW padQ).g
      (honestRun I BK M tr Wi Qo H s m padW padQ).α (honestRun I BK M tr Wi Qo H s m padW padQ).β)
    (ht : ¬ Reduction.Degenerate I (honestRun I BK M tr Wi Qo H s m padW padQ).g
      (honestRun I BK M tr Wi Qo H s m padW padQ).α (honestRun I BK M tr Wi Qo H s m padW padQ).β
      (honestRun I BK M tr Wi Qo H s m padW padQ).t) :
    deployedVerify I x Y tr wiringOpening Wi Qo H F (wiringOpening.root H (wiringStack I BK))
      s.statement π := by
  have hcl := honest_claims I BK hB M hc hw tr Wi Qo H s m padW padQ hab ht
  set run := honestRun I BK M tr Wi Qo H s m padW padQ with hrun
  obtain ⟨c1, c2, c3, c4⟩ := hcl
  unfold honestProve at hπ
  simp only [← hrun] at hπ
  obtain ⟨πW, hW, hπ⟩ := Option.bind_eq_some_iff.mp hπ
  obtain ⟨πσ, hσ, hπ⟩ := Option.bind_eq_some_iff.mp hπ
  obtain ⟨πQ, hQ, rfl⟩ := Option.map_eq_some_iff.mp hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Reduction.rustCheck_honest I run.g run.α run.β run.t).mpr ht
  · refine Wi.complete H F (natTable run.cW) padW _ fuel πW rfl
      (fun t ht' => witness_inChunks BK (cellBitsK M s) m t fun hin => ht' (hWheld t hin))
      (fun c hc' => ?_) hW
    rw [List.mem_singleton] at hc'
    subst hc'
    refine ⟨?_, hWv ▸ c1⟩
    rw [hWv]
    simp [witnessClaim]
  · refine wiringOpening.complete H F (natTable (wiringTableK BK I.wiring)) (fun _ _ => 0) _ fuel πσ rfl
      (fun t ht' => by
        unfold natTable
        exact if_neg (show ¬ t < 2 ^ (22 + 2) from ht'))
      (fun c hc' => ?_) hσ
    rw [List.mem_singleton] at hc'
    subst hc'
    exact ⟨by simp [wiringClaim, wiringOpening], c2⟩
  · refine Qo.complete H F (natTable run.cQ) padQ _ fuel πQ rfl
      (fun t ht' => quotient_inChunks run.R (qGateKOf run.R) t fun hin => ht' (hQheld t hin))
      (fun c hc' => ?_) hQ
    rw [hQv]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact ⟨by simp [quotientClaim], c3⟩
    · exact ⟨by simp [sumClaim], c4⟩

end Completeness
