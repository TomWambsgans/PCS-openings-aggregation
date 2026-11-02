-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Reduce
import LeanVM.Protocol.Whir.Sound.Start
import LeanVM.Protocol.Whir.Sound.Weights
import LeanVM.Protocol.Whir.Complete.Tables

/-!
# The deployed claims: `WitnessClaims`, `QuotientClaims`, discharged

`DecoderDeployed.lean`'s `knowledgeSoundness_deployed_decoded` leaves the claims on tables:
`WitnessClaims D read₁` and `QuotientClaims W D read₂`, for the claim maps `D.clW`, `D.clσ`,
`D.clQ` of a `Deploy` and reads of a table as F1's messages. Here all of them are concrete:

* **`deployD c r`**: the deployed openings at `2^r` rows (`witnessLayout r`, `wiringLayout r`,
  `quotientLayout r`, rate `1/2`), each handed the claims `reduce` computes from the proof and
  the chain's challenges (`Reduce.lean`'s transcription of `quotient::protocol::reduce`): the
  witness claim, the wiring claim, the quotient claim and the claim at `sum_point`. When
  `reduce` rejects (`VerifyError::Degenerate`) an opening is handed two claims no table satisfies
  (`rejectClaims`: one point, values `0` and `1`), so a run the Rust rejects is one the model can
  only accept with the opening's soundness error (the model accepts at least what the Rust
  does). `deployD_clW`, `deployD_clσ`, `deployD_clQ`: otherwise the claims **are** `reduce`'s.
* **`tabFn`**, **`tabEval_eq_mle`**: a table read as F1 reads tables (`c b` the entry whose index
  has bits `b`); its multilinear extension (`Table::eval`, `tabEval`) is F1's `mle` of it.
* **`read₁`**, **`read₂`**: a witness table read as its four row polynomials
  (`witnessOfTable`), a quotient table as the second message it holds (`quotientsOfTable`, the
  extension's `Y`), within the bounds. Generic over the layout's `Layout.table` (`readHidden`,
  the gadget layout's): they read the table, not the stack.
* **`witnessClaims_deployD`**: `WitnessClaims` for any parameters and bounds; the witness claim
  is F1's (`Reduce.witness_iff`, through `witness_claim`).
* **`quotientClaims_deployD`**: `QuotientClaims` for F1's instance `I` (`Instance.params`) when
  its basis is `beta()`'s words, its weights `coordinate_weight`'s and `tau` solves
  `row_vanishing`'s system (`Reduce.matches_params`), and the wire reads the statement as its
  halves then `1, 0, 0, 0` (`hdec`); through `quotient_mle`, `sum_mle` (`claims_iff_accepts`'s
  steps).
* **`wiringClaim_deployD`**: for the wiring term: a wiring table satisfying the wiring opening's
  claim has its polynomial take the fifth value at `t` (`Reduce.wiring_iff`).
* **`knowledgeSoundness_deployed_concrete`**: `knowledgeSoundness_deployed_decoded_bits` at
  `log_rows = 22` with these: what remains is the wiring term `εσ` and the hypotheses on the
  constants and the wire.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge Finset
open Reduce

/-! ## A table as F1 reads it -/

/-- A table's entries as F1's tables read them (`mle`, `witnessOfTable`, `quotientsOfTable`):
the entry whose index has bits `b`, bit `k` coordinate `k` (`boolPoint`'s order), in `E`. -/
def tabFn {v : ℕ} (T : Vector K (2 ^ v)) (b : Fin v → Bool) : E :=
  ofK T[Whir.bitsEquiv v b]

/-- **`Table::eval` is F1's `mle`**: at a point of `vars` coordinates, a table's multilinear
extension is `mle` of its entries at the point's coordinates. -/
theorem tabEval_eq_mle (L : Layout) (T : Tab L) (p : List E) (hp : p.length = L.vars) :
    tabEval L T p = mle (tabFn T) (fun k => p.getD k 0) := by
  unfold tabEval mle tabFn
  rw [← Equiv.sum_comp (Whir.bitsEquiv L.vars)]
  refine sum_congr rfl fun b _ => congrArg (ofK T[Whir.bitsEquiv L.vars b] * ·) ?_
  rw [Whir.bitsEquiv_val, Whir.Sound.boolPoint_bitsToNat, Whir.Complete.eqEval_comm,
    Whir.Sound.eqEval_bitsL p hp]
  refine prod_congr rfl fun k _ => ?_
  cases b k <;> simp [CharTwo.sub_eq_add]

/-! ## The deployed openings' claims -/

/-- **Claims no table satisfies**: the same point, values `0` and `1` (`reduce` rejected). -/
def rejectClaims (v : ℕ) : List Claim := [⟨List.replicate v 0, 0⟩, ⟨List.replicate v 0, 1⟩]

/-- A layout adds at most one stack claim of its own (a hidden layout's gadget). -/
theorem extra_length_le (L : Layout) : L.extra.length ≤ 1 := by
  unfold Layout.extra
  split <;> simp

/-- A statement of claims on a layout: the claims if they are a statement (with the layout's own,
at most `2^46 + 1`; every point of `vars` coordinates, as `reduce`'s are), `rejectClaims`
otherwise. -/
def toStmt (L : Layout) (cs : List Claim) : Stmt L.stacking :=
  if h : cs.length + L.stacking.extra.length ≤ 2 ^ 46 + 1 ∧
      ∀ c ∈ cs, c.point.length = L.stacking.vars then ⟨cs, h.1, h.2⟩
  else ⟨rejectClaims L.vars, by
      have := extra_length_le L
      show 2 + L.extra.length ≤ _
      omega, by simp [rejectClaims, Layout.stacking]⟩

/-- The claims an opening is handed: `sel` of `reduce`'s output, `rejectClaims` if it rejected. -/
def claimsFrom (v : ℕ) (o : Option Reduced) (sel : Reduced → List Claim) : List Claim :=
  match o with
  | some r => sel r
  | none => rejectClaims v

@[simp] theorem claimsFrom_some (v : ℕ) (r : Reduced) (sel : Reduced → List Claim) :
    claimsFrom v (some r) sel = sel r := rfl

@[simp] theorem claimsFrom_none (v : ℕ) (sel : Reduced → List Claim) :
    claimsFrom v none sel = rejectClaims v := rfl

/-- `reduce` on the reduction's proof and challenges at `2^r` rows: the statement's halves, the
chain's `α, β, γ, t, ρ`, the values `a_0..a_3`, `next`. -/
def reduceOf (c : Consts) (r : ℕ) (π : RootProof E) (ch : Chals E) : Option Reduced :=
  reduce c (r + 2) (stmtHalves π.stmt) ch.α ch.β ch.γ ch.t π.v.1 π.v.2 ch.ρ

/-- **The deployed openings** at `2^r` rows (`verify_openings`): the witness layout with the
witness claim, the wiring layout with the wiring claim, the quotient layout with the quotient
claim and the claim at `sum_point`, at rate `1/2`, the claims `reduce`'s. -/
def deployD (c : Consts) (r : ℕ) : Deploy E where
  R := logInvRate
  Lw := witnessLayout r
  Lσ := wiringLayout r
  LQ := quotientLayout r
  clW π ch := toStmt (witnessLayout r)
    (claimsFrom (witnessLayout r).vars (reduceOf c r π ch) fun x => [x.witness])
  clσ π ch := toStmt (wiringLayout r)
    (claimsFrom (wiringLayout r).vars (reduceOf c r π ch) fun x => [x.wiring])
  clQ π ch := toStmt (quotientLayout r)
    (claimsFrom (quotientLayout r).vars (reduceOf c r π ch) fun x => [x.quotient, x.sum])

theorem reject_unsat (L : Layout) (T : Tab L) :
    ¬ ∀ cl ∈ rejectClaims L.vars, tabEval L T cl.point = cl.value := by
  intro h
  have h0 := h _ (List.mem_cons_self ..)
  have h1 := h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  exact zero_ne_one (h0.symm.trans h1)

theorem toStmt_claims (L : Layout) (cs : List Claim) :
    ((toStmt L cs).claims = cs ∧ ∀ c ∈ cs, c.point.length = L.vars) ∨
      (toStmt L cs).claims = rejectClaims L.vars := by
  unfold toStmt
  split_ifs with h
  · exact Or.inl ⟨rfl, h.2⟩
  · exact Or.inr rfl

/-- A table satisfying the claims an opening is handed: `reduce` did not reject, and the table
satisfies its claims, each point of `vars` coordinates. -/
theorem holds_cases (L : Layout) (T : Tab L) (o : Option Reduced) (sel : Reduced → List Claim)
    (h : ∀ cl ∈ (toStmt L (claimsFrom L.vars o sel)).claims,
      tabEval L T cl.point = cl.value) :
    ∃ r, o = some r ∧ ∀ cl ∈ sel r, cl.point.length = L.vars ∧ tabEval L T cl.point = cl.value := by
  rcases toStmt_claims L (claimsFrom L.vars o sel) with ⟨he, hlen⟩ | he
  · rw [he] at h
    cases o with
    | none => exact absurd h (reject_unsat L T)
    | some r => exact ⟨r, rfl, fun cl hcl => ⟨hlen cl hcl, h cl hcl⟩⟩
  · rw [he] at h
    exact absurd h (reject_unsat L T)

/-! ### Not vacuous: the openings are handed `reduce`'s claims -/

theorem toStmt_of (L : Layout) (cs : List Claim) (h1 : cs.length + L.extra.length ≤ 2 ^ 46 + 1)
    (h2 : ∀ c ∈ cs, c.point.length = L.vars) : (toStmt L cs).claims = cs := by
  unfold toStmt
  split_ifs with h
  · rfl
  · exact absurd ⟨h1, h2⟩ h

theorem short_of_le {L : Layout} {cs : List Claim} (h : cs.length ≤ 2) :
    cs.length + L.extra.length ≤ 2 ^ 46 + 1 := by
  have := extra_length_le L
  omega

/-- When `reduce` does not reject, the witness opening is handed its witness claim. -/
theorem deployD_clW (c : Consts) (r : ℕ) (π : RootProof E) (ch : Chals E) (x : Reduced)
    (hx : reduceOf c r π ch = some x) : ((deployD c r).clW π ch).claims = [x.witness] := by
  obtain ⟨-, rfl⟩ := reduce_eq_some hx
  show (toStmt _ (claimsFrom _ (reduceOf c r π ch) _)).claims = _
  rw [hx, claimsFrom_some]
  refine toStmt_of _ _ (short_of_le (by simp)) ?_
  simp only [List.mem_singleton, forall_eq, witness_point_eq]
  simp [witnessLayout, Layout.hidden, cellVars]
  omega

/-- When `reduce` does not reject, the wiring opening is handed its wiring claim. -/
theorem deployD_clσ (c : Consts) (r : ℕ) (π : RootProof E) (ch : Chals E) (x : Reduced)
    (hx : reduceOf c r π ch = some x) : ((deployD c r).clσ π ch).claims = [x.wiring] := by
  obtain ⟨-, rfl⟩ := reduce_eq_some hx
  show (toStmt _ (claimsFrom _ (reduceOf c r π ch) _)).claims = _
  rw [hx, claimsFrom_some]
  refine toStmt_of _ _ (short_of_le (by simp)) ?_
  simp only [List.mem_singleton, forall_eq, wiring_point_eq]
  simp [wiringLayout, Layout.new, cellVars]

/-- When `reduce` does not reject, the quotient opening is handed its quotient claim and the
claim at `sum_point`. -/
theorem deployD_clQ (c : Consts) (r : ℕ) (π : RootProof E) (ch : Chals E) (x : Reduced)
    (hx : reduceOf c r π ch = some x) :
    ((deployD c r).clQ π ch).claims = [x.quotient, x.sum] := by
  obtain ⟨-, rfl⟩ := reduce_eq_some hx
  show (toStmt _ (claimsFrom _ (reduceOf c r π ch) _)).claims = _
  rw [hx, claimsFrom_some]
  refine toStmt_of _ _ (short_of_le (by simp)) ?_
  intro cl hcl
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · rw [quotient_point_eq]
    simp [quotientLayout, Layout.hidden, cellVars]
    omega
  · rw [sum_point_eq]
    simp [quotientLayout, Layout.hidden, cellVars, Reduce.sumPoint]
    omega

/-! ## The reads -/

/-- **A witness table read as F1's first message**: its four row polynomials
(`witnessOfTable`), of degree below `2^(r + 1)`. -/
noncomputable def read₁ (r : ℕ) {P : Params E} (B : P.Bounds) (hB : 2 ^ (r + 1) ≤ B.witness) :
    Tab (witnessLayout r) → B.Msg₁ := fun T =>
  ⟨witnessOfTable (k := r + 1) (tabFn T), fun j => (natDegree_witnessOfTable_le _ j).trans hB⟩

/-- **A quotient table read as F1's second message** (`quotientsOfTable` at the extension's
`Y`). -/
noncomputable def read₂ (r : ℕ) {P : Params E} (B : P.Bounds) (hw : 2 ^ (r + 1) ≤ B.witness)
    (hq : 2 ^ (r + 2 + 2) ≤ B.quotient) : Tab (quotientLayout r) → B.Msg₂ := fun T =>
  ⟨quotientsOfTable (m := r + 2) y (tabFn T),
    (tables_within_bounds P B hw hq y (fun _ => 0) (tabFn T)).2⟩

/-! ## The claims, discharged -/

/-- **`WitnessClaims`, discharged**: a witness table satisfying the deployed witness opening's
claims reads as a first message satisfying F1's witness claim, for any parameters. -/
theorem witnessClaims_deployD (c : Consts) (r : ℕ) (hr : 1 ≤ r) {P : Params E} (B : P.Bounds)
    (hB : 2 ^ (r + 1) ≤ B.witness) : WitnessClaims (deployD c r) (read₁ r B hB) := by
  intro π ch T h
  obtain ⟨x, hx, hcl⟩ := holds_cases (witnessLayout r) T (reduceOf c r π ch)
    (fun x => [x.witness]) h
  obtain ⟨hnz, rfl⟩ := reduce_eq_some hx
  obtain ⟨hlen, hev⟩ := hcl _ (List.mem_singleton_self _)
  rw [tabEval_eq_mle (witnessLayout r) T _ hlen] at hev
  exact (witness_iff c r _ _ _ _ _ _ _ _ hr hnz (tabFn T)).mp hev

/-- **The wiring claim on a table** (for the wiring term): a wiring table satisfying the deployed
wiring opening's claims has its polynomial (`tablePoly`) take the fifth value at `t`, and
`reduce` did not reject. -/
theorem wiringClaim_deployD (c : Consts) (r : ℕ) (hr : 1 ≤ r) (π : RootProof E) (ch : Chals E)
    (T : Tab (wiringLayout r))
    (h : ∀ cl ∈ ((deployD c r).clσ π ch).claims, tabEval (wiringLayout r) T cl.point = cl.value) :
    (denominators c (r + 2) ch.α ch.β ch.t π.v.1 π.v.2).prod ≠ 0 ∧
      (tablePoly (tabFn T)).eval ch.t = π.v.2 := by
  obtain ⟨x, hx, hcl⟩ := holds_cases (wiringLayout r) T (reduceOf c r π ch) (fun x => [x.wiring]) h
  obtain ⟨hnz, rfl⟩ := reduce_eq_some hx
  obtain ⟨hlen, hev⟩ := hcl _ (List.mem_singleton_self _)
  rw [tabEval_eq_mle (wiringLayout r) T _ hlen] at hev
  exact ⟨hnz, (wiring_iff c r _ _ _ _ _ _ _ _ hr hnz (tabFn T)).mp hev⟩

/-- F1's instance's parameters, unfolded. -/
theorem params_eq (I : Instance E) :
    I.params = Params.ofCantor I.basis le24 I.wiring 8 (fun J => weightedSum (regionWeight I.c J))
      (pubProd (invSeq I.basis.β) (regionMu I.c) 11 (22 + 2))
      (membershipPub_hPub I.basis (invSeq I.basis.β) I.c le24 (invSeq_zero _)
        fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd) := rfl

/-- **`QuotientClaims`, discharged** for F1's instance: when its basis is `beta()`'s words, its
weights `coordinate_weight`'s, `tau` solves `row_vanishing`'s system, and the wire reads the
statement's bytes as their halves then `1, 0, 0, 0`, a quotient table satisfying the deployed
quotient opening's two claims reads as a second message satisfying F1's two quotient claims. -/
theorem quotientClaims_deployD (I : Instance E) (c : Consts)
    (hβ : ∀ k < 22 + 2, I.basis.β k = ofK (c.beta k))
    (hc : ∀ k < 8, coordinateWeight k = some (I.c k)) (hτ : RowVanishing c 22)
    (W : Wire I.params I.bounds) (hdec : ∀ sb, W.decode sb = stmtWords sb)
    (hw : 2 ^ (22 + 1) ≤ I.bounds.witness) (hq : 2 ^ (22 + 2 + 2) ≤ I.bounds.quotient) :
    QuotientClaims W (deployD c 22) (read₂ 22 I.bounds hw hq) := by
  intro π ch T h
  obtain ⟨x, hx, hcl⟩ := holds_cases (quotientLayout 22) T (reduceOf c 22 π ch)
    (fun x => [x.quotient, x.sum]) h
  obtain ⟨hnz, rfl⟩ := reduce_eq_some hx
  obtain ⟨hl1, h1⟩ := hcl _ (List.mem_cons_self ..)
  obtain ⟨hl2, h2⟩ := hcl _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  rw [tabEval_eq_mle (quotientLayout 22) T _ hl1] at h1
  rw [tabEval_eq_mle (quotientLayout 22) T _ hl2] at h2
  have htarget : I.params.target (W.decode π.stmt) ch.γ = target (stmtHalves π.stmt) ch.γ := by
    rw [hdec]
    refine (membership_target I.basis le24 I.wiring (invSeq I.basis.β) I.c (invSeq_zero _)
      (fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd) (stmtHalves π.stmt) ch.γ).trans ?_
    unfold target
    ring
  exact quotientClaims_of c 22 (stmtHalves π.stmt) ch.α ch.β ch.γ ch.t π.v.1 π.v.2 ch.ρ
    (by norm_num) I.params (matches_params I c hβ hc hτ) I.basis le24 (cantorCells I.basis le24)
    (fun x => Params.ofCantor_pt I.basis le24 I.wiring 8 _ _
      (membershipPub_hPub I.basis (invSeq I.basis.β) I.c le24 (invSeq_zero _)
        fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd) x)
    (W.decode π.stmt) htarget hnz (tabFn T) h1 h2

/-! ## The deployed statement, concrete -/

section Final

variable (I : Instance E) (c : Consts)

theorem rows_ok : WhirBridge.minLogRows ≤ 22 ∧ 22 ≤ WhirBridge.maxLogRows := by
  unfold WhirBridge.minLogRows WhirBridge.maxLogRows
  omega

/-- The witness table's read at the instance's bounds. -/
noncomputable def readW : Tab (witnessLayout 22) → I.bounds.Msg₁ := read₁ 22 I.bounds le_rfl

/-- The quotient table's read at the instance's bounds. -/
noncomputable def readQ : Tab (quotientLayout 22) → I.bounds.Msg₂ :=
  read₂ 22 I.bounds le_rfl le_rfl

/-- **The deployed witness decoder** (`Decoder.lean`'s `tableCode` at the witness layout, the
tables read by `readW`): what the extractor applies to the witness root's Merkle word. -/
noncomputable def witnessDecoder : TableCode I.bounds.Msg₁ :=
  tableCode (deployD c 22).Lw (deployD c 22).R
    (admissible_of_eq rfl rfl (layouts_ok 22 rows_ok.1 rows_ok.2).1) (readW I)

/-- **Knowledge soundness of the deployed verifier, its claims `reduce`'s**: the reduction's
chain, then `opening::verify` on the witness, wiring and quotient tables with the claims
`quotient::protocol::reduce` computes (`deployD`), at `2^22` rows, over `F192`, against F1's
instance `I`; the extractor (`adversaryExtractor`) decodes the witness root's word with the
computable decoder and reads each table as its four row polynomials. If the instance's basis is
`beta()`'s words (`hβ`), its weights `coordinate_weight`'s (`hc`), `tau` solves `row_vanishing`'s
system (`hτ`) and the wire reads the statement as its halves then `1, 0, 0, 0` (`hdec`), the
verifier accepts while the extracted list holds no witness with probability at most the openings'
terms, the wiring term `εσ`, and `N (2^-128 + 5 N / 2^256)`, `N = QS + Q + 6 + 3 QO`.
`WitnessClaims` and `QuotientClaims` are discharged (`witnessClaims_deployD`,
`quotientClaims_deployD`); the wiring term `hσ` remains. -/
theorem knowledgeSoundness_deployed_concrete
    (hβ : ∀ k < 22 + 2, I.basis.β k = ofK (c.beta k))
    (hc : ∀ k < 8, coordinateWeight k = some (I.c k)) (hτ : RowVanishing c 22)
    (W : Wire I.params I.bounds) (hdec : ∀ sb, W.decode sb = stmtWords sb)
    (setup : OracleComp KeccakCalls Bytes32)
    (A : Bytes32 → OracleComp KeccakCalls (RootProof E × OpenProofs)) (QS Q QO : ℕ)
    (hS : IsTotalQueryBound setup QS) (hQ : ∀ ir, IsTotalQueryBound (A ir) Q)
    (hO : ∀ (L : Layout) w, IsTotalQueryBound (ourVerifier L logInvRate w) QO) (εσ : ℝ≥0∞)
    (hσ : Pr{let z ← (simulateQ randomOracle (deployedExp W (deployD c 22) (withSetup setup A))).run'
      ∅}[WDd (P := I.params) z] ≤ εσ) :
    Pr{let z ← (simulateQ randomOracle (deployedExp W (deployD c 22) (withSetup setup A))).run' ∅}[
        BreaksD W (witnessDecoder I c) z] ≤
      openingBound (QS + Q + 6) + εσ + openingBound (QS + Q + 6 + QO + QO) +
        ((QS + Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
          5 * ((QS + Q + 6 + QO + QO + QO : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  knowledgeSoundness_deployed_decoded_bits W (deployD c 22) card_E
    (Params.ofCantor_nCells I.basis le24 I.wiring 8 _ _
      (membershipPub_hPub I.basis (invSeq I.basis.β) I.c le24 (invSeq_zero _)
        fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd))
    rfl
    (Params.ofCantor_identity_le_margin I.basis le24 I.wiring _ _
      (membershipPub_hPub I.basis (invSeq I.basis.β) I.c le24 (invSeq_zero _)
        fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd)
      (natDegree_membershipPub_le (invSeq I.basis.β) I.c))
    22 rows_ok.1 rows_ok.2 rfl rfl rfl (readW I) (readQ I)
    (witnessClaims_deployD c 22 (by norm_num) I.bounds le_rfl)
    (quotientClaims_deployD I c hβ hc hτ W hdec le_rfl le_rfl)
    setup A QS Q QO hS hQ hO εσ hσ

end Final

end Compose
