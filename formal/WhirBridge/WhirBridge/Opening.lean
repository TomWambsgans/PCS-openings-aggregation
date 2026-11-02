/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

The opening check of `crates/quotient/src/opening.rs` (`verify`, with `Layout`) as a program of the
verifier language of leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0,
MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`, its transcription of leanVM's verifier at
`c445e3d5`), and its reading as mumbai's stacked opening `verifyStackedOpening`. The hidden branch of
the weight starts from the review's transcription (`formal/Review/HiddenWeight.lean`, this
repository, commit 4d5dd40).
-/
import LeanVM.Protocol.Whir.Sound.Spec
import LeanVM.Protocol.EndToEnd.Sound.Glue

/-!
# The opening check

`opening::verify(layout, root, claims, proof)` (`crates/quotient/src/opening.rs:728-819`):

1. reject unless every claim's point has the table's `vars` coordinates;
2. start the transcript from the IV `keccak256(prefix(layout) ‖ claims)` and a zero public digest
   (`iv`, `opening.rs:592-602`), read the root as the proof's first two scalars and reject unless it
   is the root expected;
3. sample `λ`, set `λ_i = λ^i`, the target `Σ λ_i v_i`, and the weight closure (`opening.rs:777-807`):
   per claim, its point's lane coordinates and its scales (`Layout::scales`, `opening.rs:253-268`)
   times `λ_i`, then, at a stack point `x = low ‖ high`,
   * a **public** layout (`log_piece = None`): `eq(p[..ℓ], low) · (on(0) + on(1))`, `on(odd)` the
     lane sum `Σ_l scale_l · eq_index(high, l)` over the block lanes of that parity;
   * a **hidden** layout (`log_piece = Some(s)`): `below · (even · on(0) + odd · on(1) + pieces ·
     on_overflow)`, the block lanes' `eq` with their first piece taken out, an odd lane's
     coordinate `s` flipped, and the overflow and share lanes' pieces;
4. `verify_whir(transcript, log_n, placed, LOG_INV_RATE, target, root, &weight)`, then
   `transcript.finish()`.

`Layout` mirrors the Rust struct field by field (`opening.rs:76-90`), `Layout.new` and `Layout.hidden`
its two constructors (`opening.rs:94-184`, the latter `hidden_with`), and `Layout.check L R claims` is
steps 1, 3 and 4 as a program of mumbai's language (`Prog`), each definition below transcribing the
Rust it names. Step 2 is `WhirBridge/Verifier.lean` (`openingVerifyWithHash`); `placed` (the pruned
Merkle form's zero prefix, which mumbai's full-leaf `Proof` does not have) is not modelled.

`Layout.check_eq`: the program **is** mumbai's `verifyStackedOpening L.logN R (L.stacking.claims claims)`
after the length check (a `Stacking.check`): the same challenge, target and weight, each claim's
weight `Layout.claimWeight L c` being the Rust's per-claim term with its power of `λ` pulled out.
`isMultiaffine_layoutClaimWeight`: every such weight, public or hidden, is multiaffine on the
stack's `log_n` coordinates, the hypothesis of mumbai's `stackedSpec`.

`Blocks` is the public stacking of a list of blocks (lane `l` holds block `blocks[l]`), with the
public claim weight `claimWeight`; `Table.lean` proves what a claim on it means for the table, and a
public `Layout` is one (`Layout.toBlocks`, `Table.lean`).
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)

/-- `LANE_FOLD` (`opening.rs:48`): the first fold of leanVM's WHIR, `2^6` lanes. -/
def laneFold : ℕ := 6

/-- `LOG_INV_RATE` (`opening.rs:549`): rate `1/2`. -/
def logInvRate : ℕ := 1

/-- A claim (`opening.rs:54-59`): the table's multilinear extension at `point` is `value`. The
Rust holds `F192` limbs; `ext` (`opening.rs:697-699`) reads them as the verifier's `E`, the same
field `K[y]/(y^3 + y + 1)`, `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`. -/
structure Claim where
  point : List E
  value : E

/-- `eq_bits(point, index)` (`opening.rs:345-349`), and the verifier's `eq_index`
(`opening.rs:772-776`): `Π_k (bit k of index ? p_k : 1 + p_k)`. -/
def eqBits (point : List E) (index : ℕ) : E :=
  point.zipIdx.foldl (fun w pk ↦ w * if (index >>> pk.2) % 2 = 1 then pk.1 else 1 + pk.1) 1

/-- The powers `verify` builds (`opening.rs:747-750`): `[1]`, then `last · λ` until there is one
per claim; at least one. -/
def lambdas (lam : E) (n : ℕ) : List E := powers lam (max n 1)

/-- The target (`opening.rs:751-754`): `Σ λ_i v_i`, the claims zipped with the powers. -/
def target (ls : List E) (claims : List Claim) : E :=
  (claims.zip ls).foldl (fun acc cl ↦ acc + cl.2 * cl.1.value) 0

/-! ## A stacking: what mumbai's stacked opening needs of a layout -/

/-- **A stacking**: a table of `vars` variables committed as a stack of `logN` variables, and one
claim's weight on the stack, multiaffine (the hypothesis of mumbai's `stackedSpec`). -/
structure Stacking where
  vars : ℕ
  logN : ℕ
  weight : Claim → List E → E
  multiaffine : ∀ c, IsMultiaffine logN (weight c)

/-- The claims as mumbai's stack claims (`StackClaim`: a weight on the stack and a value). -/
def Stacking.claims (S : Stacking) (cs : List Claim) : List StackClaim :=
  cs.map fun c ↦ (S.weight c, c.value)

/-- **The opening of a stacking**: the length check, then mumbai's stacked opening of the claims. -/
def Stacking.check (S : Stacking) (R : ℕ) (cs : List Claim) : Prog Unit :=
  (Prog.require (∀ c ∈ cs, c.point.length = S.vars)).bind fun _ ↦
    verifyStackedOpening S.logN R (S.claims cs)

theorem Stacking.check_eq_ite (S : Stacking) (R : ℕ) (cs : List Claim) :
    S.check R cs =
      if ∀ c ∈ cs, c.point.length = S.vars then verifyStackedOpening S.logN R (S.claims cs)
      else Prog.fail := by
  rw [Stacking.check, Prog.require]
  split_ifs <;> rfl

theorem Stacking.isMultiaffine_claims (S : Stacking) (cs : List Claim) :
    ∀ c ∈ S.claims cs, IsMultiaffine S.logN c.1 := by
  intro c hc
  obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc
  exact S.multiaffine c'

/-! ## The public stacking of a list of blocks -/

/-- A public stacking (`Layout::new`'s layouts): a table of `vars` variables, committed as a stack
of `log_n` variables whose lane `l` holds the table's block `blocks[l]` of `2^(log_n − 6)`
entries. -/
structure Blocks where
  vars : ℕ
  logN : ℕ
  blocks : List ℕ
  deriving DecidableEq, Repr

namespace Blocks

/-- `log_lane`. -/
def logLane (L : Blocks) : ℕ := L.logN - laneFold

/-- The lanes. -/
def lanes (L : Blocks) : ℕ := L.blocks.length

/-- Each lane's weight in a claim at `point`, `eq` of the point's high coordinates at the lane's
block (`Layout::scales` of a public layout, `opening.rs:253-261`). -/
def laneWeights (L : Blocks) (point : List E) : List E :=
  L.blocks.map fun b ↦ eqBits (point.drop L.logLane) b

end Blocks

/-- **One claim's weight on a public stack**: `eq(p[..ℓ], x[..ℓ]) · Σ_l lane_weight_l ·
eq(bits(l), x[ℓ..])`. -/
def claimWeight (L : Blocks) (c : Claim) (x : List E) : E :=
  ((c.point.take L.logLane).zip (x.take L.logLane)).foldl
      (fun w cp ↦ w * (cp.1 * cp.2 + (1 + cp.1) * (1 + cp.2))) 1 *
    ((L.laneWeights c.point).zip ((List.range L.lanes).map fun l ↦ eqBits (x.drop L.logLane) l)).foldl
      (fun s we ↦ s + we.1 * we.2) 0

/-- The claims as mumbai's stack claims. -/
def stackClaims (L : Blocks) (claims : List Claim) : List StackClaim :=
  claims.map fun c ↦ (claimWeight L c, c.value)

/-! ## The layout (`opening.rs:61-243`) -/

/-- What a lane of the stack holds (`Lane`, `opening.rs:61-73`). -/
inductive Lane where
  /-- The table's block `b` (in a hidden layout, all of it but one piece). -/
  | block (b : ℕ)
  /-- Pieces of the table, at its pieces `1, 2, ...`. -/
  | overflow
  /-- Randomness (but for the share lane's pieces `1, 2, ...`). -/
  | random
  deriving DecidableEq, Repr

/-- **`Layout`** (`opening.rs:76-90`), field by field: the table's variables, the stack's, what each
lane holds, a hidden layout's piece `2^log_piece` (`none` for a public layout), the table's pieces
the overflow lane holds at its pieces `1, 2, ...`, and the share lane. -/
structure Layout where
  vars : ℕ
  logN : ℕ
  lanes : List Lane
  logPiece : Option ℕ
  pieces : List ℕ
  share : Option ℕ
  deriving DecidableEq, Repr

namespace Layout

/-- `log_lane` (`opening.rs:186-188`). -/
def logLane (L : Layout) : ℕ := L.logN - laneFold

/-- `placed` (`opening.rs:200-202`): whole lanes. -/
def placed (L : Layout) : ℕ := L.lanes.length * 2 ^ L.logLane

/-- `layout_overflow` (`opening.rs:821-826`), `Layout::overflow`: the first overflow lane (the
lanes' count if there is none, where the Rust panics). -/
def overflow (L : Layout) : ℕ := L.lanes.findIdx (· == Lane.overflow)

/-- The blocks `Layout::new` lists (`opening.rs:94-104`): for each chunk `(chunk, len)` of
`2^log_chunk` entries, the blocks of `2^(log_n − 6)` entries covering its leading `len`. -/
def newBlocks (logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c ↦
    (List.range ((c.2 + 2 ^ (logN - laneFold) - 1) / 2 ^ (logN - laneFold))).map fun j ↦
      c.1 <<< (logChunk - (logN - laneFold)) ||| j

/-- **`Layout::new`** (`opening.rs:94-121`): a public layout, a lane per block. -/
def new (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : Layout where
  vars := vars
  logN := logN
  lanes := (newBlocks logChunk logN chunks).map .block
  logPiece := none
  pieces := []
  share := none

/-- A hidden layout's whole blocks (`opening.rs:140-148`). -/
def hiddenBlocks (logChunk logLane : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c ↦ (List.range (c.2 >>> logLane)).map fun j ↦ (c.1 <<< (logChunk - logLane)) + j

/-- A hidden layout's tails: the pieces of what each chunk holds past its whole blocks
(`opening.rs:140-148`). -/
def hiddenTails (logChunk logLane logPiece : ℕ) (chunks : List (ℕ × ℕ)) : List ℕ :=
  chunks.flatMap fun c ↦
    let first := c.1 <<< (logChunk - logLane)
    let whole := c.2 >>> logLane
    let start := (first + whole) <<< (logLane - logPiece)
    let tail := c.2 - (whole <<< logLane)
    (List.range ((tail + 2 ^ logPiece - 1) / 2 ^ logPiece)).map fun j ↦ start + j

/-- The odd random lanes (`opening.rs:156-160`): `2 (k · pairs / (random − 1)) + 1`. -/
def oddRandoms (total random : ℕ) : List ℕ :=
  (List.range (random - 1)).map fun k ↦ 2 * (k * ((total - 2) / 2) / (random - 1)) + 1

/-- The lanes before the blocks fill them (`opening.rs:149-160`): the last random, the one before
it the overflow lane, the odd random lanes written last. -/
def slots (total random : ℕ) : List (Option Lane) :=
  (List.range total).map fun i ↦
    if i ∈ oddRandoms total random then some .random
    else if i = total - 2 then some .overflow
    else if i = total - 1 then some .random
    else none

/-- The blocks fill the free lanes in order (`opening.rs:161-165`). -/
def fillBlocks : List (Option Lane) → List ℕ → List Lane
  | [], _ => []
  | some l :: rest, bs => l :: fillBlocks rest bs
  | none :: rest, b :: bs => .block b :: fillBlocks rest bs
  | none :: rest, [] => .block 0 :: fillBlocks rest []

/-- **`Layout::hidden_with`** (`opening.rs:129-184`; `Layout::hidden` is `log_piece = LOG_PIECE`): a
lane per whole block of a chunk, the overflow lane `L − 2`, the share lane `L − 1`, the other random
lanes odd; the overflow lane's pieces are the piece each block lane gives up (`k ⊕ (l mod 2)` at its
piece `k`: piece `l mod 2`), then the chunks' tails. -/
def hidden (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) (random logPiece : ℕ) : Layout :=
  let logLane := logN - laneFold
  let blocks := hiddenBlocks logChunk logLane chunks
  let total := blocks.length + 1 + random
  let lanes := fillBlocks (slots total random) blocks
  let givenUp := lanes.zipIdx.filterMap fun ll ↦ match ll.1 with
    | .block b => some ((b <<< (logLane - logPiece)) ||| (ll.2 &&& 1))
    | _ => none
  { vars := vars
    logN := logN
    lanes := lanes
    logPiece := some logPiece
    pieces := givenUp ++ hiddenTails logChunk logLane logPiece chunks
    share := some (total - 1) }

/-- `Layout::scales` (`opening.rs:253-268`), the lanes': `eq` of the point's high coordinates at
each block lane's block, zero on the other lanes. -/
def laneScales (L : Layout) (point : List E) : List E :=
  L.lanes.map fun
    | .block b => eqBits (point.drop L.logLane) b
    | _ => 0

/-- `Layout::scales`, the pieces': `eq` of the coordinates above a piece at each overflow piece. -/
def pieceScales (L : Layout) (point : List E) : List E :=
  match L.logPiece with
  | some s => L.pieces.map fun p ↦ eqBits (point.drop s) p
  | none => []

end Layout

/-! ## The weight closure (`opening.rs:718-807`) -/

/-- `ClaimWeight` (`opening.rs:718-725`): a claim's lane coordinates, and its lanes' and pieces'
scales. -/
structure Part where
  low : List E
  lanes : List E
  pieces : List E

/-- The scales times `λ_i` (`opening.rs:756-768`). -/
def Part.scale (l : E) (p : Part) : Part := ⟨p.low, p.lanes.map (l * ·), p.pieces.map (l * ·)⟩

/-- A claim's part before its power of `λ`. -/
def Layout.part (L : Layout) (c : Claim) : Part :=
  ⟨c.point.take L.logLane, L.laneScales c.point, L.pieceScales c.point⟩

/-- `parts` (`opening.rs:756-768`). -/
def Layout.parts (L : Layout) (ls : List E) (claims : List Claim) : List Part :=
  (claims.zip ls).map fun cl ↦ (L.part cl.1).scale cl.2

/-- `eq1` (`opening.rs:770`). -/
def eq1 (c p : E) : E := c * p + (1 + c) * (1 + p)

/-- `eq` (`opening.rs:771`): zipping. -/
def eqZ (a b : List E) : E := (a.zip b).foldl (fun w cp ↦ w * eq1 cp.1 cp.2) 1

/-- `Π (1 + p)` (`opening.rs:796-797`). -/
def onePlusProd (l : List E) : E := l.foldl (fun w p ↦ w * (1 + p)) 1

/-- One lane's term of `on(odd)` (`opening.rs:783-786`). -/
def onStep (scales laneEq : List E) (odd : ℕ) (sum : E) (ll : Lane × ℕ) : E :=
  match ll.1 with
  | .block _ => if ll.2 &&& 1 = odd then sum + scales.getD ll.2 0 * laneEq.getD ll.2 0 else sum
  | _ => sum

/-- `on(odd)` (`opening.rs:782-787`): the block lanes of one parity, each its scale times its
`eq_index`. -/
def onParity (lanes : List Lane) (scales laneEq : List E) (odd : ℕ) : E :=
  lanes.zipIdx.foldl (onStep scales laneEq odd) 0

/-- `lane_eq` (`opening.rs:780`): `eq_index(high, l)` for each lane. -/
def laneEqs (n : ℕ) (high : List E) : List E := (List.range n).map fun l ↦ eqBits high l

/-- One part's term of the weight (`opening.rs:781-806`): the public branch, or the hidden one. -/
def Layout.term (L : Layout) (laneEq low : List E) (part : Part) : E :=
  let on := onParity L.lanes part.lanes laneEq
  match L.logPiece with
  | none => eqZ part.low low * (on 0 + on 1)
  | some s =>
    let below := eqZ (part.low.take s) (low.take s)
    let above := eqZ (part.low.drop (s + 1)) (low.drop (s + 1))
    let firstAbove := onePlusProd (part.low.drop (s + 1))
    let firstPiece := onePlusProd (low.drop s)
    let block := fun c ↦ above * eq1 c (low.getD s 0) + firstAbove * (1 + c) * firstPiece
    let even := block (part.low.getD s 0)
    let odd := block (1 + part.low.getD s 0)
    let pieces := part.pieces.zipIdx.foldl
      (fun sum wk ↦ sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0
    let onOverflow := laneEq.getD L.overflow 0 + laneEq.getD (L.share.getD 0) 0
    below * (even * on 0 + odd * on 1 + pieces * onOverflow)

/-- **The weight closure** (`opening.rs:777-807`), at a stack point `x`: the lane's coordinates
first, then the lane index's six. -/
def Layout.weight (L : Layout) (ls : List E) (claims : List Claim) (x : List E) : E :=
  let low := x.take L.logLane
  let high := x.drop L.logLane
  let laneEq := laneEqs L.lanes.length high
  (L.parts ls claims).foldl (fun acc part ↦ acc + L.term laneEq low part) 0

/-- **The opening check** `opening::verify` (`opening.rs:728-819`) past its transcript's start, as a
program of mumbai's verifier language, at rate exponent `R` (`LOG_INV_RATE = 1`): the length
check, the batching challenge, then `verify_whir` with the target and the weight. -/
def Layout.check (L : Layout) (R : ℕ) (claims : List Claim) : Prog Unit := do
  Prog.require (∀ c ∈ claims, c.point.length = L.vars)
  let lam ← Prog.sampleChallenge
  let ls := lambdas lam claims.length
  verifyWhir L.logN R (target ls claims) (L.weight ls claims)

/-- **One claim's weight on the stack**: the closure's term for the claim with its power of `λ`
pulled out. -/
def Layout.claimWeight (L : Layout) (c : Claim) (x : List E) : E :=
  L.term (laneEqs L.lanes.length (x.drop L.logLane)) (x.take L.logLane) (L.part c)

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

/-- A fold of additions is a sum. -/
theorem foldl_add_map {α : Type} (g : α → E) : ∀ (xs : List α) (s : E),
    xs.foldl (fun acc a ↦ acc + g a) s = s + (xs.map g).sum
  | [], s => by simp
  | a :: xs, s => by
    rw [List.foldl_cons, foldl_add_map g xs, List.map_cons, List.sum_cons, add_assoc]

theorem getD_map_mul (l : E) (xs : List E) (i : ℕ) :
    (xs.map (l * ·)).getD i 0 = l * xs.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> simp

end Lists

/-! ### The program is mumbai's stacked opening -/

/-- **The target is mumbai's batched value** `dot(powers(λ, J), values)`. -/
theorem target_eq (lam : E) (claims : List Claim) :
    target (lambdas lam claims.length) claims =
      dot (powers lam claims.length) (claims.map (·.value)) := by
  rw [target, target_eq_dot, ← dot_lambdas lam _ (List.length_map _)]
  rfl

/-- One lane's term of `on(odd)`, as an addend. -/
def onTerm (scales laneEq : List E) (odd : ℕ) (ll : Lane × ℕ) : E :=
  match ll.1 with
  | .block _ => if ll.2 &&& 1 = odd then scales.getD ll.2 0 * laneEq.getD ll.2 0 else 0
  | _ => 0

theorem onStep_eq (scales laneEq : List E) (odd : ℕ) (sum : E) (ll : Lane × ℕ) :
    onStep scales laneEq odd sum ll = sum + onTerm scales laneEq odd ll := by
  rcases ll with ⟨_ | _ | _, i⟩ <;> simp only [onStep, onTerm] <;> (try split_ifs) <;> simp

/-- `on(odd)` as a sum. -/
theorem onParity_eq_sum (lanes : List Lane) (scales laneEq : List E) (odd : ℕ) :
    onParity lanes scales laneEq odd = (lanes.zipIdx.map (onTerm scales laneEq odd)).sum := by
  rw [onParity, show onStep scales laneEq odd = fun s ll ↦ s + onTerm scales laneEq odd ll from
    funext fun s ↦ funext fun ll ↦ onStep_eq _ _ _ s ll, foldl_add_map, zero_add]

theorem onParity_scale (lanes : List Lane) (l : E) (ps laneEq : List E) (odd : ℕ) :
    onParity lanes (ps.map (l * ·)) laneEq odd = l * onParity lanes ps laneEq odd := by
  rw [onParity_eq_sum, onParity_eq_sum, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun ll _ ↦ ?_
  rcases ll with ⟨_ | _ | _, i⟩ <;> simp only [onTerm]
  · split_ifs
    · rw [getD_map_mul]
      ring
    · ring
  · ring
  · ring

/-- The pieces' fold as a sum. -/
theorem pieces_eq_sum (ps low : List E) (s : ℕ) :
    ps.zipIdx.foldl (fun sum wk ↦ sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0 =
      (ps.zipIdx.map fun wk ↦ wk.1 * eqBits (low.drop s) (wk.2 + 1)).sum := by
  rw [foldl_add_map, zero_add]

theorem pieces_scale (l : E) (ps low : List E) (s : ℕ) :
    (ps.map (l * ·)).zipIdx.foldl (fun sum wk ↦ sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0 =
      l * ps.zipIdx.foldl (fun sum wk ↦ sum + wk.1 * eqBits (low.drop s) (wk.2 + 1)) 0 := by
  rw [pieces_eq_sum (ps.map (l * ·)), pieces_eq_sum ps, List.zipIdx_map, List.map_map,
    ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun wk _ ↦ ?_)
  simp only [Function.comp, Prod.map_fst, Prod.map_snd, id]
  ring

/-- **A part's scales pull out of its term.** -/
theorem term_scale (L : Layout) (laneEq low : List E) (l : E) (p : Part) :
    L.term laneEq low (p.scale l) = l * L.term laneEq low p := by
  simp only [Layout.term, Part.scale]
  split
  · rw [onParity_scale, onParity_scale]
    ring
  · rw [onParity_scale, onParity_scale, pieces_scale]
    ring

theorem weight_aux (L : Layout) (laneEq low : List E) :
    ∀ (claims : List Claim) (ls : List E) (s : E),
      ((claims.zip ls).map fun cl ↦ (L.part cl.1).scale cl.2).foldl
          (fun acc part ↦ acc + L.term laneEq low part) s =
        (List.zipWith (· * ·) ls (claims.map fun c ↦ L.term laneEq low (L.part c))).foldl
          (· + ·) s
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | c :: cs, l :: ls, s => by
    simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons, List.zipWith_cons_cons,
      term_scale]
    exact weight_aux L laneEq low cs ls _

/-- **The weight is mumbai's batched weight** `dot(powers(λ, J), weights)`, each claim's weight
`Layout.claimWeight`. -/
theorem Layout.weight_eq (L : Layout) (lam : E) (claims : List Claim) (x : List E) :
    L.weight (lambdas lam claims.length) claims x =
      dot (powers lam claims.length) (claims.map fun c ↦ L.claimWeight c x) := by
  rw [← dot_lambdas lam _ (List.length_map _), dot]
  exact weight_aux L _ _ claims _ 0

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

theorem eqZ_eq_eqEval (a x : List E) : eqZ a x = eqEval a x := eqLow_eq_eqEval a x

theorem eq1_eq (c p : E) : eq1 c p = 1 + c + p := by
  rw [eq1]
  linear_combination (c * p) * two_eq_zero_E

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

/-- **A public claim's weight is multiaffine** on the stack's `log_n` coordinates. -/
theorem isMultiaffine_claimWeight (L : Blocks) (c : Claim) :
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

/-! ### Combinators -/

/-- `f` ignores coordinate `k`. -/
def Ign (f : List E → E) (k : ℕ) : Prop := ∀ (l : List E) (X : E), f (l.set k X) = f l

theorem Ign.mul {f g : List E → E} {k : ℕ} (hf : Ign f k) (hg : Ign g k) :
    Ign (fun x ↦ f x * g x) k := fun l X ↦ by simp only [hf l X, hg l X]

theorem Ign.add {f g : List E → E} {k : ℕ} (hf : Ign f k) (hg : Ign g k) :
    Ign (fun x ↦ f x + g x) k := fun l X ↦ by simp only [hf l X, hg l X]

theorem isMultiaffine_mul' {n : ℕ} {f g : List E → E} (hf : IsMultiaffine n f)
    (hg : IsMultiaffine n g) (h : ∀ k < n, Ign f k ∨ Ign g k) :
    IsMultiaffine n fun x ↦ f x * g x :=
  isMultiaffine_mul_of_split hf hg fun l _ k hk ↦
    (h k hk).imp (fun h X ↦ h l X) (fun h X ↦ h l X)

theorem isMultiaffine_const (n : ℕ) (a : E) : IsMultiaffine n fun _ ↦ a := by
  intro l hl k hk X
  ring

theorem isMultiaffine_congr {n : ℕ} {f g : List E → E} (hf : IsMultiaffine n f)
    (h : ∀ l : List E, l.length = n → g l = f l) : IsMultiaffine n g := by
  intro l hl k hk X
  rw [h _ (by simp [hl]), h _ (by simp [hl]), h _ (by simp [hl])]
  exact hf l hl k hk X

/-- A weight of the first `m` coordinates. -/
theorem isMultiaffine_take' {n m : ℕ} {g : List E → E} (hm : m ≤ n) (hg : IsMultiaffine m g) :
    IsMultiaffine n fun x ↦ g (x.take m) := by
  intro l hl k hk X
  simp only [List.take_set]
  rcases lt_or_ge k m with hkm | hkm
  · exact hg (l.take m) (by simp [hl]; omega) k hkm X
  · have hlen : (l.take m).length ≤ k := by simp; omega
    simp only [List.set_eq_of_length_le hlen]
    ring

/-- A weight of the coordinates from `m` on. -/
theorem isMultiaffine_drop' {n m : ℕ} {g : List E → E} (hg : IsMultiaffine (n - m) g) :
    IsMultiaffine n fun x ↦ g (x.drop m) := by
  intro l hl k hk X
  simp only [List.drop_set]
  split_ifs with hkm
  · ring
  · exact hg (l.drop m) (by simp [hl]) (k - m) (by omega) X

theorem ign_take {g : List E → E} {m k : ℕ} (hk : m ≤ k) : Ign (fun x ↦ g (x.take m)) k :=
  fun l X ↦ by simp only [List.take_set_of_le hk]

theorem ign_drop {g : List E → E} {m k : ℕ} (hk : k < m) : Ign (fun x ↦ g (x.drop m)) k :=
  fun l X ↦ by simp only [List.drop_set_of_lt hk]

/-- A window `[s, ℓ)` ignores the coordinates outside it. -/
theorem ign_window {g : List E → E} {s ℓ k : ℕ} (hk : k < s ∨ ℓ ≤ k) :
    Ign (fun x ↦ g ((x.take ℓ).drop s)) k := by
  intro l X
  rcases hk with hk | hk
  · simp only [List.take_set, List.drop_set_of_lt hk]
  · simp only [List.take_set_of_le hk]

/-- A weight of the window `[s, ℓ)`. -/
theorem isMultiaffine_window {n s ℓ : ℕ} {g : List E → E} (hℓ : ℓ ≤ n)
    (hg : IsMultiaffine (ℓ - s) g) : IsMultiaffine n fun x ↦ g ((x.take ℓ).drop s) :=
  isMultiaffine_take' (g := fun z ↦ g (z.drop s)) hℓ (isMultiaffine_drop' hg)

theorem isMultiaffine_eqZ (a : List E) (n : ℕ) : IsMultiaffine n (eqZ a) := by
  have : eqZ a = eqEval a := funext (eqZ_eq_eqEval a)
  rw [this]
  exact isMultiaffine_eqEval_any a n

theorem isMultiaffine_eqBits (k n : ℕ) : IsMultiaffine n fun y ↦ eqBits y k := by
  have h := isMultiaffine_eqBits_drop k (n := n) (m := 0) (Nat.zero_le _)
  simpa using h

theorem onePlusProd_aux (a : E) : ∀ l : List E,
    l.foldl (fun w p ↦ w * (1 + p)) a =
      (List.zipWith (fun x z ↦ 1 + x + z) (List.replicate l.length 0) l).foldl (· * ·) a
  | [] => by simp
  | p :: l => by
    simp only [List.foldl_cons, List.length_cons, List.replicate_succ, List.zipWith_cons_cons,
      add_zero]
    exact onePlusProd_aux _ l

theorem onePlusProd_eq (l : List E) : onePlusProd l = eqEval (List.replicate l.length 0) l := by
  rw [onePlusProd, onePlusProd_aux, eqEval]

theorem isMultiaffine_onePlusProd (n : ℕ) : IsMultiaffine n onePlusProd :=
  isMultiaffine_congr (isMultiaffine_eqEval_any (List.replicate n 0) n) fun l hl ↦ by
    rw [onePlusProd_eq, hl]

/-- `eq1(c, y_0)` is affine in the first coordinate. -/
theorem isMultiaffine_eq1_head (c : E) (n : ℕ) : IsMultiaffine n fun y ↦ eq1 c (y.getD 0 0) := by
  intro l hl k hk X
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · obtain ⟨a, l', rfl⟩ : ∃ a l', l = a :: l' := by
      cases l with
      | nil => simp at hl; omega
      | cons a l' => exact ⟨a, l', rfl⟩
    simp only [List.set_cons_zero, List.getD_cons_zero, eq1_eq]
    ring
  · have hg : ∀ Y, (l.set k Y).getD 0 0 = l.getD 0 0 := fun Y ↦ by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
    show eq1 c ((l.set k X).getD 0 0) =
      (1 - X) * eq1 c ((l.set k 0).getD 0 0) + X * eq1 c ((l.set k 1).getD 0 0)
    rw [hg, hg, hg]
    ring

theorem ign_eq1_head (c : E) {k : ℕ} (hk : 0 < k) : Ign (fun y ↦ eq1 c (y.getD 0 0)) k := by
  intro l X
  show eq1 c ((l.set k X).getD 0 0) = eq1 c (l.getD 0 0)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]

theorem laneEqs_getD (N i : ℕ) (h : List E) :
    (laneEqs N h).getD i 0 = if i < N then eqBits h i else 0 := by
  by_cases hi : i < N
  · simp [laneEqs, hi, List.getD_eq_getElem?_getD]
  · simp [laneEqs, hi, List.getD_eq_getElem?_getD]

theorem isMultiaffine_laneEq (N i n : ℕ) : IsMultiaffine n fun h ↦ (laneEqs N h).getD i 0 := by
  simp only [laneEqs_getD]
  split_ifs
  · exact isMultiaffine_eqBits i n
  · exact isMultiaffine_const n 0

/-- `on(odd)` is multiaffine in the lane index's coordinates. -/
theorem isMultiaffine_onParity (lanes : List Lane) (ps : List E) (N odd n : ℕ) :
    IsMultiaffine n fun h ↦ onParity lanes ps (laneEqs N h) odd := by
  simp only [onParity_eq_sum]
  refine isMultiaffine_listSum_mem _ _ fun ll _ ↦ ?_
  rcases ll with ⟨_ | _ | _, i⟩ <;> simp only [onTerm]
  · split_ifs
    · exact (isMultiaffine_laneEq N i n).const_mul _
    · exact isMultiaffine_const n 0
  · exact isMultiaffine_const n 0
  · exact isMultiaffine_const n 0

/-- The pieces' term is multiaffine in the window's coordinates. -/
theorem isMultiaffine_pieces (ps : List E) (n : ℕ) :
    IsMultiaffine n fun y ↦ (ps.zipIdx.map fun wk ↦ wk.1 * eqBits y (wk.2 + 1)).sum :=
  isMultiaffine_listSum ps.zipIdx (fun wk ↦ wk.1) (fun wk y ↦ eqBits y (wk.2 + 1))
    fun wk ↦ isMultiaffine_eqBits _ n

/-- The block term of the hidden branch, in the window `y = low[s..]`. -/
def blockTerm (a : List E) (fa c : E) (y : List E) : E :=
  eqZ a (y.drop 1) * eq1 c (y.getD 0 0) + fa * (1 + c) * onePlusProd y

theorem isMultiaffine_blockTerm (a : List E) (fa c : E) (n : ℕ) :
    IsMultiaffine n (blockTerm a fa c) := by
  refine IsMultiaffine.add ?_ ((isMultiaffine_onePlusProd n).const_mul _)
  refine isMultiaffine_mul' (isMultiaffine_drop' (isMultiaffine_eqZ a _))
    (isMultiaffine_eq1_head c n) fun k _ ↦ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl (ign_drop (g := eqZ a) (by omega))
  · exact Or.inr (ign_eq1_head c hk)

/-- **The hidden branch's claim weight**, the window `y = x[s..ℓ]` and the lane index's
coordinates `x[ℓ..]` read apart. -/
theorem claimWeight_hidden (L : Layout) (c : Claim) {s : ℕ} (hs : L.logPiece = some s)
    (x : List E) :
    L.claimWeight c x =
      eqZ ((c.point.take L.logLane).take s) (x.take (min s L.logLane)) *
        (blockTerm ((c.point.take L.logLane).drop (s + 1))
            (onePlusProd ((c.point.take L.logLane).drop (s + 1)))
            ((c.point.take L.logLane).getD s 0) ((x.take L.logLane).drop s) *
          onParity L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) 0 +
         blockTerm ((c.point.take L.logLane).drop (s + 1))
            (onePlusProd ((c.point.take L.logLane).drop (s + 1)))
            (1 + (c.point.take L.logLane).getD s 0) ((x.take L.logLane).drop s) *
          onParity L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) 1 +
         (((L.pieceScales c.point).zipIdx.map fun wk ↦
            wk.1 * eqBits ((x.take L.logLane).drop s) (wk.2 + 1)).sum) *
          ((laneEqs L.lanes.length (x.drop L.logLane)).getD L.overflow 0 +
            (laneEqs L.lanes.length (x.drop L.logLane)).getD (L.share.getD 0) 0)) := by
  have hget : (x.take L.logLane).getD s 0 = ((x.take L.logLane).drop s).getD 0 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, add_zero]
  have hdrop : (x.take L.logLane).drop (s + 1) = ((x.take L.logLane).drop s).drop 1 := by
    rw [List.drop_drop]
  rw [Layout.claimWeight, Layout.term, hs]
  simp only [Layout.part, blockTerm, pieces_eq_sum, List.take_take, hget, hdrop]

/-- The public branch's claim weight. -/
theorem claimWeight_public (L : Layout) (c : Claim) (hs : L.logPiece = none) (x : List E) :
    L.claimWeight c x =
      eqZ (c.point.take L.logLane) (x.take L.logLane) *
        (onParity L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) 0 +
          onParity L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) 1) := by
  rw [Layout.claimWeight, Layout.term, hs]
  rfl

/-- **Every claim's weight is multiaffine**, for every layout, public or hidden: the hypothesis of
mumbai's `stackedSpec`. -/
theorem isMultiaffine_layoutClaimWeight (L : Layout) (c : Claim) :
    IsMultiaffine L.logN (L.claimWeight c) := by
  have hℓ : L.logLane ≤ L.logN := Nat.sub_le _ _
  have hon : ∀ odd, IsMultiaffine L.logN fun x ↦
      onParity L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) odd :=
    fun odd ↦ isMultiaffine_drop' (g := fun h ↦ onParity L.lanes (L.laneScales c.point)
      (laneEqs L.lanes.length h) odd) (isMultiaffine_onParity _ _ _ _ _)
  have hon_ign : ∀ odd k, k < L.logLane → Ign (fun x ↦ onParity L.lanes (L.laneScales c.point)
      (laneEqs L.lanes.length (x.drop L.logLane)) odd) k :=
    fun odd k hk ↦ ign_drop (g := fun h ↦ onParity L.lanes (L.laneScales c.point)
      (laneEqs L.lanes.length h) odd) hk
  rcases hs : L.logPiece with _ | s
  · have hf : L.claimWeight c = fun x ↦ eqZ (c.point.take L.logLane) (x.take L.logLane) *
        (onParity L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) 0 +
          onParity L.lanes (L.laneScales c.point) (laneEqs L.lanes.length (x.drop L.logLane)) 1) :=
      funext (claimWeight_public L c hs)
    rw [hf]
    refine isMultiaffine_mul' (isMultiaffine_take' hℓ (isMultiaffine_eqZ _ _))
      ((hon 0).add (hon 1)) fun k _ ↦ ?_
    rcases lt_or_ge k L.logLane with hk | hk
    · exact Or.inr ((hon_ign 0 k hk).add (hon_ign 1 k hk))
    · exact Or.inl (ign_take hk)
  · have hf := funext (claimWeight_hidden L c hs)
    rw [hf]
    -- the overflow and share lanes' `eq`
    have hov : IsMultiaffine L.logN fun x ↦
        (laneEqs L.lanes.length (x.drop L.logLane)).getD L.overflow 0 +
          (laneEqs L.lanes.length (x.drop L.logLane)).getD (L.share.getD 0) 0 :=
      isMultiaffine_drop' (g := fun h ↦ (laneEqs L.lanes.length h).getD L.overflow 0 +
        (laneEqs L.lanes.length h).getD (L.share.getD 0) 0)
        ((isMultiaffine_laneEq _ _ _).add (isMultiaffine_laneEq _ _ _))
    have hov_ign : ∀ k, k < L.logLane → Ign (fun x ↦
        (laneEqs L.lanes.length (x.drop L.logLane)).getD L.overflow 0 +
          (laneEqs L.lanes.length (x.drop L.logLane)).getD (L.share.getD 0) 0) k :=
      fun k hk ↦ ign_drop (g := fun h ↦ (laneEqs L.lanes.length h).getD L.overflow 0 +
        (laneEqs L.lanes.length h).getD (L.share.getD 0) 0) hk
    -- a window term times a lane term
    have hprod : ∀ (g : List E → E) (G : List E → E), IsMultiaffine (L.logLane - s) g →
        IsMultiaffine L.logN G → (∀ k, k < L.logLane → Ign G k) →
        IsMultiaffine L.logN (fun x ↦ g ((x.take L.logLane).drop s) * G x) ∧
          ∀ k, k < min s L.logLane → Ign (fun x ↦ g ((x.take L.logLane).drop s) * G x) k := by
      intro g G hg hG hGi
      refine ⟨isMultiaffine_mul' (isMultiaffine_window hℓ hg) hG fun k _ ↦ ?_, fun k hk ↦
        (ign_window (Or.inl (lt_of_lt_of_le hk (min_le_left _ _)))).mul
          (hGi k (lt_of_lt_of_le hk (min_le_right _ _)))⟩
      rcases lt_or_ge k L.logLane with hk | hk
      · exact Or.inr (hGi k hk)
      · exact Or.inl (ign_window (Or.inr hk))
    obtain ⟨h1, i1⟩ := hprod _ _ (isMultiaffine_blockTerm _ _ _ _) (hon 0) (hon_ign 0)
    obtain ⟨h2, i2⟩ := hprod _ _ (isMultiaffine_blockTerm _ _ _ _) (hon 1) (hon_ign 1)
    obtain ⟨h3, i3⟩ := hprod _ _ (isMultiaffine_pieces _ _) hov hov_ign
    refine isMultiaffine_mul' (isMultiaffine_take' (le_trans (min_le_right _ _) hℓ)
      (isMultiaffine_eqZ _ _)) ((h1.add h2).add h3) fun k _ ↦ ?_
    rcases lt_or_ge k (min s L.logLane) with hk | hk
    · exact Or.inr (((i1 k hk).add (i2 k hk)).add (i3 k hk))
    · exact Or.inl (ign_take hk)

end Multiaffine

/-! ## The stackings -/

/-- A public stacking's. -/
def Blocks.stacking (L : Blocks) : Stacking :=
  ⟨L.vars, L.logN, claimWeight L, isMultiaffine_claimWeight L⟩

/-- **A layout's stacking**: its claims' weights as `verify` evaluates them. -/
def Layout.stacking (L : Layout) : Stacking :=
  ⟨L.vars, L.logN, L.claimWeight, isMultiaffine_layoutClaimWeight L⟩

/-- **The opening check is mumbai's stacked opening** on the claims' stack claims, after the
length check. -/
theorem Layout.check_eq (L : Layout) (R : ℕ) (claims : List Claim) :
    L.check R claims = L.stacking.check R claims := by
  have h1 : (L.stacking.claims claims).length = claims.length := List.length_map _
  have h2 : (L.stacking.claims claims).map (·.2) = claims.map (·.value) := by
    simp [Stacking.claims]
  have h3 : ∀ x, (L.stacking.claims claims).map (fun c ↦ c.1 x) =
      claims.map fun c ↦ L.claimWeight c x := fun x ↦ by simp [Stacking.claims, Layout.stacking]
  have key : ∀ lam : E, verifyWhir L.logN R (target (lambdas lam claims.length) claims)
        (L.weight (lambdas lam claims.length) claims) =
      verifyWhir L.logN R
        (dot (powers lam (L.stacking.claims claims).length)
          ((L.stacking.claims claims).map (·.2)))
        (fun point ↦ dot (powers lam (L.stacking.claims claims).length)
          ((L.stacking.claims claims).map fun c ↦ c.1 point)) := fun lam ↦
    congrArg₂ (verifyWhir L.logN R) (by rw [h1, h2, target_eq])
      (funext fun x ↦ by rw [h1, h3, Layout.weight_eq])
  unfold Layout.check Stacking.check verifyStackedOpening
  simp only [key]
  rfl

end WhirBridge
