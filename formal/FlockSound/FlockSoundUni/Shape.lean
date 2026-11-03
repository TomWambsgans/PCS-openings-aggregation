-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.Decode

/-!
# Reads of a known length, and the sumcheck's claims by index

The channel's reads (`nextScalars`, `samples`, `readRounds`) always return as many entries as they
are asked for, but in an arbitrary monad that is not a fact one can read off a bound variable. Here
it is an equation of programs instead: each read is its own result **fitted** to its length
(`fitL`, `fitN`: padded or cut, the identity at the right length), so a later step may assume the
length (`samples_fit`, `nextScalars_fit`, `readRounds_fit`).

The sumcheck's decoding (`decodeSC`) is a fold over its rounds; `scClaim c es d t` is its running
claim before round `t`, by index (`scClaim_succ`), a function of the rounds before `t` only
(`scClaim_congr`), and `decodeSC_eq` reads the fold as the rounds' challenges and the last claim.

`rd d a` is round `a` of a transcript (`noRound` past its end).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics

/-! ## Fitting a read to its length -/

/-- The first `n` entries of a list, padded with `0`: the list itself when it has `n`. -/
def fitL : ℕ → List E → List E
  | 0, _ => []
  | n + 1, l => l.headD 0 :: fitL n l.tail

@[simp] theorem length_fitL : ∀ (n : ℕ) (l : List E), (fitL n l).length = n
  | 0, _ => rfl
  | n + 1, l => by simp [fitL, length_fitL n]

/-- A round past the end of a transcript. -/
def noRound : UMsg × List E := ((none, []), [])

/-- **Round `a` of a transcript** (`noRound` past its end). -/
def rd (d : Done) (a : ℕ) : UMsg × List E := d.getD a noRound

/-- The first `n` rounds of a transcript, padded with `noRound`: itself when it has `n`. -/
def fitN : ℕ → Done → Done
  | 0, _ => []
  | n + 1, d => d.headD noRound :: fitN n d.tail

@[simp] theorem length_fitN : ∀ (n : ℕ) (d : Done), (fitN n d).length = n
  | 0, _ => rfl
  | n + 1, d => by simp [fitN, length_fitN n]

section Fit

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem repeatM_fit (act : ChanM m E) : ∀ n : ℕ, repeatM act n = fitL n <$> repeatM act n
  | 0 => by simp [repeatM, fitL]
  | n + 1 => by
    conv_lhs => rw [repeatM, repeatM_fit act n]
    simp [repeatM, fitL, map_bind]

/-- **`samples` is fitted to its count.** -/
theorem samples_fit (F : KeccakState → m KeccakState) (n : ℕ) :
    samples F n = fitL n <$> samples F n := by
  rw [samples_eq]
  exact repeatM_fit _ n

/-- **`nextScalars` is fitted to its count.** -/
theorem nextScalars_fit (n : ℕ) : nextScalars (m := m) n = fitL n <$> nextScalars (m := m) n := by
  rw [nextScalars_eq]
  exact repeatM_fit _ n

/-- **`readRounds` is fitted to its rounds.** -/
theorem readRounds_fit (F : KeccakState → m KeccakState) :
    ∀ rs : List Compose.RoundSpec, readRounds F rs = fitN rs.length <$> readRounds F rs
  | [] => by simp [readRounds, fitN]
  | s :: rs => by
    conv_lhs => rw [readRounds, readRounds_fit F rs]
    simp [readRounds, fitN, map_bind]

theorem readRounds_fit_replicate (F : KeccakState → m KeccakState) (n : ℕ) (s : Compose.RoundSpec) :
    readRounds F (List.replicate n s) = fitN n <$> readRounds F (List.replicate n s) := by
  conv_lhs => rw [readRounds_fit F]
  simp

end Fit

/-! ## Transcripts by index -/

theorem rd_cons_zero (r : UMsg × List E) (d : Done) : rd (r :: d) 0 = r := rfl

theorem rd_cons_succ (r : UMsg × List E) (d : Done) (a : ℕ) : rd (r :: d) (a + 1) = rd d a := rfl

theorem rd_drop (d : Done) (a b : ℕ) : rd (d.drop a) b = rd d (a + b) := by
  simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem rd_append_left {d d' : Done} {a : ℕ} (h : a < d.length) : rd (d ++ d') a = rd d a := by
  simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_append_right {d d' : Done} {a : ℕ} (h : d.length ≤ a) :
    rd (d ++ d') a = rd d' (a - d.length) := by
  simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem rd_take {d : Done} {a j : ℕ} (h : a < j) : rd (d.take j) a = rd d a := by
  simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_take, h, ite_true]

theorem rd_eq_getElem {d : Done} {a : ℕ} (h : a < d.length) : rd d a = d[a] := by
  simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem headD_eq_getD' (l : List E) : l.headD 0 = l.getD 0 0 := List.headD_eq_getD

/-- A list of length `n` is the `List.ofFn` of its entries. -/
theorem eq_ofFn_getD {α : Type} {l : List α} {n : ℕ} (h : l.length = n) (x : α) :
    l = List.ofFn fun i : Fin n ↦ l.getD i x := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp [List.getD_eq_getElem?_getD]

theorem map_eq_ofFn {α β : Type} {l : List α} {n : ℕ} (h : l.length = n) (x : α) (g : α → β) :
    l.map g = List.ofFn fun i : Fin n ↦ g (l.getD i x) := by
  rw [eq_ofFn_getD h x, List.map_ofFn]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  congr 1
  funext i
  simp [Function.comp, i.isLt]

theorem reverse_ofFn {α : Type} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn fun i ↦ f (Fin.rev i) := by
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  congr 1
  ext
  simp only [Fin.val_rev]
  simp at h2
  omega

/-! ## The sumcheck's claims by index -/

/-- **The running claim before round `t`** of the decoded sumcheck from the claim `c`, its rounds'
`eq` factors `es` and its rounds' reads `d`. -/
def scClaim : E → List (Option E) → Done → ℕ → E
  | c, _, _, 0 => c
  | c, es, d, t + 1 =>
    scClaim (polyEval (decodeMsg c (es.headD none) (d.headD noRound).1.2) ((d.headD noRound).2.headD 0))
      es.tail d.tail t

theorem scClaim_zero (c : E) (es : List (Option E)) (d : Done) : scClaim c es d 0 = c := rfl

/-- **One round of claims**: the message decoded from the claim before, at the round's challenge. -/
theorem scClaim_succ : ∀ (t : ℕ) (c : E) (es : List (Option E)) (d : Done),
    scClaim c es d (t + 1) =
      polyEval (decodeMsg (scClaim c es d t) (es.getD t none) (rd d t).1.2) ((rd d t).2.headD 0)
  | 0, c, es, d => by
    cases es <;> cases d <;> rfl
  | t + 1, c, es, d => by
    rw [scClaim, scClaim_succ t, scClaim]
    cases es <;> cases d <;> rfl

/-- **The claim before round `t` reads the rounds before `t` only.** -/
theorem scClaim_congr (c : E) (es : List (Option E)) {d d' : Done} :
    ∀ t : ℕ, (∀ v < t, rd d v = rd d' v) → scClaim c es d t = scClaim c es d' t
  | 0, _ => rfl
  | t + 1, h => by
    rw [scClaim_succ, scClaim_succ, scClaim_congr c es t fun v hv ↦ h v (by omega),
      h t (by omega)]

/-- **The decoded sumcheck** (`decodeSC`) of as many rounds as factors: the rounds' challenges and
the last claim. -/
theorem decodeSC_eq : ∀ (c : E) (es : List (Option E)) (d : Done), d.length = es.length →
    decodeSC c es d = (d.map fun r ↦ r.2.headD 0, scClaim c es d es.length)
  | c, [], [], _ => rfl
  | c, e :: es, r :: d, h => by
    have h' : d.length = es.length := by simpa using h
    simp only [decodeSC, decodeSC_eq _ es d h', List.map_cons, List.length_cons, scClaim,
      List.headD_cons, List.tail_cons]
  | _, [], _ :: _, h => absurd h (by simp)
  | _, _ :: _, [], h => absurd h (by simp)

end FlockSound.Uni
