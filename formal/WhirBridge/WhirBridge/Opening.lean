/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

The opening check of `crates/quotient/src/opening.rs` (`verify`, with `Layout`) as a program of the
verifier language of leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0,
MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`, its transcription of leanVM's verifier at
`c445e3d5`), and its reading as mumbai's stacked opening `verifyStackedOpening`.
-/
import LeanVM.Protocol.Whir.Sound.Spec
import LeanVM.Protocol.EndToEnd.Sound.Glue

/-!
# The opening check

`opening::verify(layout, root, claims, proof)` (`crates/quotient/src/opening.rs:222-288`):

1. reject unless every claim's point has the table's `vars` coordinates;
2. seed the transcript with `(keccak256(LABEL), keccak256(root ‖ claims))`;
3. sample `λ`, set `λ_i = λ^i`, the target `Σ λ_i v_i`, and the weight closure
   `x ↦ Σ_i eq(p_i[..ℓ], x[..ℓ]) · Σ_l λ_i eq(p_i[ℓ..], block_l) · eq(bits(l), x[ℓ..])`
   (`ℓ = log_n − 6`, the lane's coordinates; `l` ranges over the layout's lanes);
4. `verify_whir(transcript, log_n, placed, LOG_INV_RATE, target, root, &weight)`, then
   `transcript.finish()`.

`openingCheck L R claims` is steps 1, 3 and 4 as a program of mumbai's language (`Prog`), each
definition below transcribing the Rust it names. What the program does not carry is the
transcript's seed (step 2), the root (in mumbai's language the root is commitment `0` of the
history, read by the program; here it is an argument of `verify_whir`), `placed` (the pruned
Merkle form's zero prefix, which mumbai's full-leaf `Proof` does not have) and the final
`finish` (mumbai's `runProof` accepts only a fully read proof): see `WhirBridge/Gaps.lean`.

`openingCheck_eq`: the program **is** mumbai's `verifyStackedOpening L.logN R (stackClaims L claims)`
after the length check: the same challenge, target and weight, each claim's weight
`claimWeight L c` being the Rust's per-claim term with its power of `λ` pulled out.
`isMultiaffine_claimWeight`: every such weight is multiaffine on the stack's `log_n` coordinates,
the hypothesis of mumbai's `stackedSpec`.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)

/-! ## The layout (`opening.rs:26-97`) -/

/-- `LANE_FOLD` (`opening.rs:27`): the first fold of leanVM's WHIR, `2^6` lanes. -/
def laneFold : ℕ := 6

/-- `LOG_INV_RATE` (`opening.rs:140`): rate `1/2`. -/
def logInvRate : ℕ := 1

/-- `Layout` (`opening.rs:39-45`): a table of `vars` variables, committed as a stack of `log_n`
variables whose lane `l` holds the table's block `blocks[l]` of `2^(log_n − 6)` entries. -/
structure Layout where
  vars : ℕ
  logN : ℕ
  blocks : List ℕ
  deriving DecidableEq, Repr

namespace Layout

/-- `log_lane` (`opening.rs:67-69`). -/
def logLane (L : Layout) : ℕ := L.logN - laneFold

/-- `lanes` (`opening.rs:71-73`). -/
def lanes (L : Layout) : ℕ := L.blocks.length

/-- `placed` (`opening.rs:76-78`): whole lanes. -/
def placed (L : Layout) : ℕ := L.lanes * 2 ^ L.logLane

end Layout

/-- `Layout::new(vars, log_chunk, log_n, chunks)` (`opening.rs:49-65`): lanes for the leading
`len` entries of each chunk `(chunk, len)` of `2^log_chunk` entries, in order. Its assertions are
`Layout.NewOK`. -/
def Layout.new (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : Layout where
  vars := vars
  logN := logN
  blocks := chunks.flatMap fun c ↦
    (List.range ((c.2 + 2 ^ (logN - laneFold) - 1) / 2 ^ (logN - laneFold))).map fun j ↦
      c.1 <<< (logChunk - (logN - laneFold)) ||| j

/-- The assertions of `Layout::new` (`opening.rs:51, 55, 59-63`). -/
def Layout.NewOK (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : Prop :=
  logN - laneFold ≤ logChunk ∧ logChunk ≤ vars ∧
    (∀ c ∈ chunks, c.1 >>> (vars - logChunk) = 0 ∧ c.2 ≤ 2 ^ logChunk) ∧
    0 < (Layout.new vars logChunk logN chunks).lanes ∧
    (Layout.new vars logChunk logN chunks).lanes ≤ 2 ^ laneFold

instance (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) :
    Decidable (Layout.NewOK vars logChunk logN chunks) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ## Claims and their weights (`opening.rs:29-34, 91-104, 222-277`) -/

/-- A claim (`opening.rs:31-34`): the table's multilinear extension at `point` is `value`. The
Rust holds `F192` limbs; `ext` (`opening.rs:201-203`) reads them as the verifier's `E`, the same
field `K[y]/(y^3 + y + 1)`, `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`. -/
structure Claim where
  point : List E
  value : E

/-- `eq_bits(point, index)` (`opening.rs:100-104`): `Π_k (bit k of index ? p_k : 1 + p_k)`. -/
def eqBits (point : List E) (index : ℕ) : E :=
  point.zipIdx.foldl (fun w pk ↦ w * if (index >>> pk.2) % 2 = 1 then pk.1 else 1 + pk.1) 1

/-- `Layout::lane_weights(point)` (`opening.rs:92-96`): each lane's weight in a claim at `point`,
`eq` of the point's high coordinates at the lane's block. -/
def Layout.laneWeights (L : Layout) (point : List E) : List E :=
  L.blocks.map fun b ↦ eqBits (point.drop L.logLane) b

/-- The powers `verify` builds (`opening.rs:236-239`): `[1]`, then `last · λ` until there is one
per claim; at least one. -/
def lambdas (lam : E) (n : ℕ) : List E := powers lam (max n 1)

/-- The target (`opening.rs:240-243`): `Σ λ_i v_i`, the claims zipped with the powers. -/
def target (ls : List E) (claims : List Claim) : E :=
  (claims.zip ls).foldl (fun acc cl ↦ acc + cl.2 * cl.1.value) 0

/-- The weight's parts (`opening.rs:246-254`): per claim, its point's lane coordinates, and each
lane's scale `λ_i · lane_weight`. -/
def parts (L : Layout) (ls : List E) (claims : List Claim) : List (List E × List E) :=
  (claims.zip ls).map fun cl ↦
    (cl.1.point.take L.logLane, (L.laneWeights cl.1.point).map (cl.2 * ·))

/-- The weight closure (`opening.rs:256-277`), at a stack point `x`: the lane's coordinates
first, then the lane index's six. -/
def weight (L : Layout) (ls : List E) (claims : List Claim) (x : List E) : E :=
  let low := x.take L.logLane
  let high := x.drop L.logLane
  let laneEq := (List.range L.lanes).map fun l ↦
    high.zipIdx.foldl (fun w pk ↦ w * if (l >>> pk.2) % 2 = 1 then pk.1 else 1 + pk.1) 1
  (parts L ls claims).foldl (fun acc part ↦
    let onLanes := (part.2.zip laneEq).foldl (fun s we ↦ s + we.1 * we.2) 0
    let eq := (part.1.zip low).foldl (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1
    acc + eq * onLanes) 0

/-- **The opening check** `opening::verify` (`opening.rs:222-288`) as a program of mumbai's
verifier language, at rate exponent `R` (`LOG_INV_RATE = 1`): the length check, the batching
challenge, then `verify_whir` with the target and the weight. -/
def openingCheck (L : Layout) (R : ℕ) (claims : List Claim) : Prog Unit := do
  Prog.require (∀ c ∈ claims, c.point.length = L.vars)
  let lam ← Prog.sampleChallenge
  let ls := lambdas lam claims.length
  verifyWhir L.logN R (target ls claims) (weight L ls claims)

/-! ## The claims as mumbai's stack claims -/

/-- **One claim's weight on the stack**: the Rust's per-claim term (`opening.rs:266-276`) with its
power of `λ` pulled out, `eq(p[..ℓ], x[..ℓ]) · Σ_l lane_weight_l · eq(bits(l), x[ℓ..])`. -/
def claimWeight (L : Layout) (c : Claim) (x : List E) : E :=
  ((c.point.take L.logLane).zip (x.take L.logLane)).foldl
      (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1 *
    ((L.laneWeights c.point).zip ((List.range L.lanes).map fun l ↦ eqBits (x.drop L.logLane) l)).foldl
      (fun s we ↦ s + we.1 * we.2) 0

/-- The claims as mumbai's stack claims (`StackClaim`: a weight on the stack and a value). -/
def stackClaims (L : Layout) (claims : List Claim) : List StackClaim :=
  claims.map fun c ↦ (claimWeight L c, c.value)

/-! ### List lemmas -/

section Lists

theorem foldl_zip_eq_foldl_zipWith {α β γ : Type} (op : γ → E → γ) (g : α → β → E) :
    ∀ (l : List α) (r : List β) (s : γ),
      (l.zip r).foldl (fun acc ab ↦ op acc (g ab.1 ab.2)) s = (List.zipWith g l r).foldl op s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l, b :: r, s => by
    simp only [List.zip_cons_cons, List.foldl_cons, List.zipWith_cons_cons]
    exact foldl_zip_eq_foldl_zipWith op g l r _

theorem zipWith_take_left {α β γ : Type} (f : α → β → γ) :
    ∀ (l : List α) (r : List β), List.zipWith f l r = List.zipWith f (l.take r.length) r
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: r => by
    simp only [List.zipWith_cons_cons, List.length_cons, List.take_succ_cons]
    rw [← zipWith_take_left f l r]

theorem take_powersFrom (a b : E) : ∀ n m, (powersFrom a b n).take m = powersFrom a b (min n m)
  | 0, m => by simp [powersFrom]
  | n + 1, 0 => by simp [powersFrom]
  | n + 1, m + 1 => by
    simp only [powersFrom, List.take_succ_cons, Nat.add_min_add_right]
    rw [take_powersFrom (a * b) b n m]

theorem take_lambdas (lam : E) (n : ℕ) : (lambdas lam n).take n = powers lam n := by
  rw [lambdas, powers, take_powersFrom, powers]
  congr 1
  omega

/-- The extra power `verify` builds for no claim is never read. -/
theorem dot_lambdas (lam : E) (vs : List E) {n : ℕ} (hn : vs.length = n) :
    dot (lambdas lam n) vs = dot (powers lam n) vs := by
  rw [dot, dot, zipWith_take_left, hn, take_lambdas]

/-- `Σ_i λ_i v_i` as `verify` folds it is mumbai's `dot`. -/
theorem target_eq_dot : ∀ (claims : List Claim) (ls : List E) (s : E),
    (claims.zip ls).foldl (fun acc cl ↦ acc + cl.2 * cl.1.value) s =
      (List.zipWith (· * ·) ls (claims.map (·.value))).foldl (· + ·) s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: cs, l :: ls, s => by
    simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons, List.zipWith_cons_cons]
    exact target_eq_dot cs ls _

/-- A lane scale `λ_i · w` pulls out of the lane sum. -/
theorem onLanes_scale (l : E) : ∀ (ws es : List E) (s : E),
    ((ws.map (l * ·)).zip es).foldl (fun s we ↦ s + we.1 * we.2) (l * s) =
      l * (ws.zip es).foldl (fun s we ↦ s + we.1 * we.2) s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | w :: ws, e :: es, s => by
    simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
    rw [show l * s + l * w * e = l * (s + w * e) by ring]
    exact onLanes_scale l ws es _

end Lists

/-! ### The program is mumbai's stacked opening -/

/-- **The target is mumbai's batched value** `dot(powers(λ, J), values)`. -/
theorem target_eq (lam : E) (claims : List Claim) :
    target (lambdas lam claims.length) claims =
      dot (powers lam claims.length) (claims.map (·.value)) := by
  rw [target, target_eq_dot, ← dot_lambdas lam _ (List.length_map _)]
  rfl

/-- The weight's fold over the claims, for any powers. -/
theorem weight_aux (L : Layout) (low le : List E) : ∀ (claims : List Claim) (ls : List E) (s : E),
    ((claims.zip ls).map fun cl ↦
        (cl.1.point.take L.logLane, (L.laneWeights cl.1.point).map (cl.2 * ·))).foldl
      (fun acc part ↦ acc +
        (part.1.zip low).foldl (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1 *
          (part.2.zip le).foldl (fun s we ↦ s + we.1 * we.2) 0) s =
    (List.zipWith (· * ·) ls (claims.map fun c ↦
        ((c.point.take L.logLane).zip low).foldl
            (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1 *
          ((L.laneWeights c.point).zip le).foldl (fun s we ↦ s + we.1 * we.2) 0)).foldl
      (· + ·) s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: cs, l :: ls, s => by
    simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons, List.zipWith_cons_cons]
    have h := onLanes_scale l (L.laneWeights c.point) le 0
    rw [mul_zero] at h
    rw [h, show ∀ a b : E, a * (l * b) = l * (a * b) from fun a b ↦ by ring]
    exact weight_aux L low le cs ls _

/-- **The weight is mumbai's batched weight** `dot(powers(λ, J), weights)`, each claim's weight
`claimWeight`. -/
theorem weight_eq (L : Layout) (lam : E) (claims : List Claim) (x : List E) :
    weight L (lambdas lam claims.length) claims x =
      dot (powers lam claims.length) (claims.map fun c ↦ claimWeight L c x) := by
  rw [← dot_lambdas lam _ (List.length_map _), dot]
  exact weight_aux L _ _ claims _ 0

/-- **The opening check is mumbai's stacked opening** on the claims' stack claims, after the
length check. -/
theorem openingCheck_eq (L : Layout) (R : ℕ) (claims : List Claim) :
    openingCheck L R claims =
      (Prog.require (∀ c ∈ claims, c.point.length = L.vars)).bind fun _ ↦
        verifyStackedOpening L.logN R (stackClaims L claims) := by
  have h1 : (stackClaims L claims).length = claims.length := List.length_map _
  have h2 : (stackClaims L claims).map (·.2) = claims.map (·.value) := by
    simp [stackClaims]
  have h3 : ∀ x, (stackClaims L claims).map (fun c ↦ c.1 x) =
      claims.map fun c ↦ claimWeight L c x := fun x ↦ by simp [stackClaims]
  have key : ∀ lam : E, verifyWhir L.logN R (target (lambdas lam claims.length) claims)
        (weight L (lambdas lam claims.length) claims) =
      verifyWhir L.logN R
        (dot (powers lam (stackClaims L claims).length) ((stackClaims L claims).map (·.2)))
        (fun point ↦ dot (powers lam (stackClaims L claims).length)
          ((stackClaims L claims).map fun c ↦ c.1 point)) := fun lam ↦
    congrArg₂ (verifyWhir L.logN R) (by rw [h1, h2, target_eq])
      (funext fun x ↦ by rw [h1, h3, weight_eq])
  unfold openingCheck verifyStackedOpening
  simp only [key]
  rfl

/-- With the lengths checked, the opening check is mumbai's stacked opening; otherwise it
rejects. -/
theorem openingCheck_eq_ite (L : Layout) (R : ℕ) (claims : List Claim) :
    openingCheck L R claims =
      if ∀ c ∈ claims, c.point.length = L.vars then
        verifyStackedOpening L.logN R (stackClaims L claims)
      else Prog.fail := by
  rw [openingCheck_eq, Prog.require]
  split_ifs <;> rfl

/-! ## The weights are multiaffine -/

section Multiaffine

open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd.Sound

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

theorem eqLow_aux : ∀ (a x : List E) (s : E),
    (a.zip x).foldl (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) s =
      (List.zipWith (fun x z ↦ 1 + x + z) a x).foldl (· * ·) s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: a, p :: x, s => by
    simp only [List.zip_cons_cons, List.foldl_cons, List.zipWith_cons_cons]
    rw [show s * (c * p + (1 + c) * (1 + p)) = s * (1 + c + p) by
      linear_combination (s * c * p) * two_eq_zero_E]
    exact eqLow_aux a x _

/-- `eq` as the Rust writes it, `c·p + (1 + c)(1 + p)`, is mumbai's `1 + c + p`. -/
theorem eqLow_eq_eqEval (a x : List E) :
    (a.zip x).foldl (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1 = eqEval a x := by
  rw [eqEval]
  exact eqLow_aux a x 1

theorem eOfNat_zero_E : eOfNat 0 = 0 := by
  unfold eOfNat
  rw [show K.ofBits 0 = 0 by decide +kernel]
  simp

theorem eOfNat_one_E : eOfNat 1 = 1 := by
  rw [eOfNat, show K.ofBits 1 = 1 from rfl, show ofK = algebraMap K E from rfl, map_one]

theorem bitFactor (n : ℕ) (p : E) :
    (if n % 2 = 1 then p else 1 + p) = 1 + eOfNat (n % 2) + p := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h, eOfNat_zero_E]; simp
  · rw [h, eOfNat_one_E]
    simp only [↓reduceIte]
    linear_combination (-1 : E) * two_eq_zero_E

theorem eqBits_aux (k : ℕ) : ∀ (y : List E) (s : ℕ) (acc : E),
    (y.zipIdx s).foldl (fun w pk ↦ w * if (k >>> pk.2) % 2 = 1 then pk.1 else 1 + pk.1) acc =
      (List.zipWith (fun x z ↦ 1 + x + z)
        ((List.range' s y.length).map fun bit ↦ eOfNat ((k >>> bit) % 2)) y).foldl (· * ·) acc
  | [], _, _ => by simp
  | p :: y, s, acc => by
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons, List.range'_succ,
      List.map_cons, List.zipWith_cons_cons]
    rw [bitFactor]
    exact eqBits_aux k y (s + 1) _

/-- `eq_bits(y, k)` is mumbai's `eq_eval(selector_point(k, |y|), y)`. -/
theorem eqBits_eq_eqEval (k : ℕ) (y : List E) :
    eqBits y k = eqEval (selectorPoint k y.length) y := by
  rw [eqBits, eqBits_aux, eqEval, selectorPoint, List.range_eq_range']

/-- A product of two weights each of which ignores every coordinate the other reads. -/
theorem isMultiaffine_mul_of_split {n : ℕ} {Φ Ψ : List E → E} (hΦ : IsMultiaffine n Φ)
    (hΨ : IsMultiaffine n Ψ)
    (hsplit : ∀ l : List E, l.length = n → ∀ k < n,
      (∀ X, Φ (l.set k X) = Φ l) ∨ (∀ X, Ψ (l.set k X) = Ψ l)) :
    IsMultiaffine n fun l ↦ Φ l * Ψ l := by
  intro l hl k hk X
  show Φ (l.set k X) * Ψ (l.set k X) =
    (1 - X) * (Φ (l.set k 0) * Ψ (l.set k 0)) + X * (Φ (l.set k 1) * Ψ (l.set k 1))
  rcases hsplit l hl k hk with h | h
  · rw [h X, h 0, h 1, hΨ l hl k hk X]; ring
  · rw [h X, h 0, h 1, hΦ l hl k hk X]; ring

theorem isMultiaffine_eqEval_take (a : List E) {n m : ℕ} (hm : m ≤ n) :
    IsMultiaffine n fun x ↦ eqEval a (x.take m) := by
  intro l hl j hj X
  simp only [List.take_set]
  rcases lt_or_ge j m with hjm | hjm
  · exact isMultiaffine_eqEval_any a m (l.take m) (by simp [hl]; omega) j hjm X
  · have hlen : (l.take m).length ≤ j := by simp; omega
    simp only [List.set_eq_of_length_le hlen]
    ring

theorem isMultiaffine_eqBits_drop (k : ℕ) {n m : ℕ} (hm : m ≤ n) :
    IsMultiaffine n fun x ↦ eqBits (x.drop m) k := by
  intro l hl j hj X
  have hlen : ∀ Y, ((l.set j Y).drop m).length = n - m := fun Y ↦ by simp [hl]
  simp only [eqBits_eq_eqEval, hlen]
  simp only [List.drop_set]
  split_ifs with hjm
  · ring
  · exact isMultiaffine_eqEval_any (selectorPoint k (n - m)) (n - m) (l.drop m) (by simp [hl])
      (j - m) (by omega) X

/-- The lane sum `Σ_l w_l · eq(bits(l), y)` as a list sum. -/
theorem lanes_eq_sum (ws : List E) (ks : List ℕ) (y : List E) :
    (ws.zip (ks.map fun l ↦ eqBits y l)).foldl (fun s we ↦ s + we.1 * we.2) 0 =
      ((ws.zip ks).map fun p ↦ p.1 * eqBits y p.2).sum := by
  rw [show (fun s (we : E × E) ↦ s + we.1 * we.2) = (fun s (we : E × E) ↦ s + (· * ·) we.1 we.2)
      from rfl, foldl_zip_eq_foldl_zipWith, foldl_add_eq, zero_add]
  induction ws generalizing ks with
  | nil => simp
  | cons w ws ih =>
    cases ks with
    | nil => simp
    | cons k ks =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, List.sum_cons]
      rw [ih]

/-- **A claim's weight is multiaffine** on the stack's `log_n` coordinates: the hypothesis of
mumbai's `stackedSpec`. -/
theorem isMultiaffine_claimWeight (L : Layout) (c : Claim) :
    IsMultiaffine L.logN (claimWeight L c) := by
  have hm : L.logLane ≤ L.logN := Nat.sub_le _ _
  have hfun : claimWeight L c = fun x ↦ eqEval (c.point.take L.logLane) (x.take L.logLane) *
      (((L.laneWeights c.point).zip (List.range L.lanes)).map fun p ↦
        p.1 * eqBits (x.drop L.logLane) p.2).sum := by
    funext x
    rw [claimWeight, eqLow_eq_eqEval, lanes_eq_sum]
  rw [hfun]
  refine isMultiaffine_mul_of_split (isMultiaffine_eqEval_take _ hm)
    (isMultiaffine_listSum_mem _ _ fun p _ ↦ (isMultiaffine_eqBits_drop p.2 hm).const_mul p.1)
    fun l hl j hj ↦ ?_
  rcases lt_or_ge j L.logLane with hjm | hjm
  · right
    intro X
    simp only [List.drop_set, hjm, ↓reduceIte]
  · left
    intro X
    have hlen : (l.take L.logLane).length ≤ j := by simp; omega
    simp only [List.take_set, List.set_eq_of_length_le hlen]

/-- Every claim's weight is multiaffine. -/
theorem isMultiaffine_stackClaims (L : Layout) (claims : List Claim) :
    ∀ c ∈ stackClaims L claims, IsMultiaffine L.logN c.1 := by
  intro c hc
  obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc
  exact isMultiaffine_claimWeight L c'

end Multiaffine

end WhirBridge

