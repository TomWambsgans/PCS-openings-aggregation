-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The functions costed are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/Keccak.lean`'s `absorbWith`, `keccak256With`; `Statement/LeanVmVerifier.lean`'s `duplex`,
-- `absorb`, `squeeze`, `Prog`; `Statement/Prover/Run.lean`'s `leafDigestsM`, `parentsM`, `levelsM`,
-- `buildTreeM`; `Statement/Prover/Ntt.lean`'s `stackWordFast`) and `ZK/Format.lean`'s; the program's
-- cost is `lean_vm/LeanVM/Protocol/Compile/Cost.lean`'s `Prog.Costs` (quarters of a query), and the
-- calculus with a postcondition is shaped after it. `len_stackWordFast` is
-- `EndToEnd/Completeness/E2ECompleteness/HashLen.lean`'s.
import ZK.ProverBridgeReduce
import LeanVM.Protocol.Verifier.Cost
import Field.Sampleable

/-!
# The formatting's calls of `π`: the calculus

`QB X n Q`: **every path of `X` makes at most `n` calls of `π`, and every value it returns satisfies
`Q`** (whatever `π` answers). It implies VCVio's `IsTotalQueryBound X n` (`QB.total`), and composes
along `bind` with the continuation charged only at the values the first part can return (`QB.bind`), as
mumbai's `Prog.Costs` does for the verifier's programs.

* Keccak-256 over `π` of `n` bytes: `⌊n / 136⌋ + 1` calls (`qb_keccak256With`); the sponge's `absorb`
  at most one, `squeeze` one.
* A Merkle tree of `2^h` rows of `64` words (`buildTreeM`): at most `5 · 2^h` (`qb_buildTreeM`: four per
  `512`-byte leaf, one per node).
* `fmt`'s expansion of a pruned multiproof of `k` positions and rows of at most `2^10` words in a tree of
  height `h` (`expandMulti`): at most `k · (61 + h)` (`qb_expandMulti`: the leaves hashed, then per
  level at most `k` parents, `expandLevel` at most doubling the known nodes and `pairUp` halving them).
* `fmt`'s run of the verifier's program (`fillRun`): a program of cost `n` quarters (`Prog.Costs`, every
  commitment of height at most `H`), from a state whose roots have height at most `H` and whose `j`
  multiproofs are small, makes at most `n + j · M` calls (`qb_fillRun`): a read, a sample, a proof of
  work, a commitment cost at most the quarters they are charged, and each query consumes a multiproof,
  whose expansion costs at most `M`.
-/

open OracleComp OracleSpec
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## The calculus -/

/-- **At most `n` calls of `π` on every path, every value returned satisfying `Q`.** -/
def QB {α : Type} : OracleComp PermSpec α → ℕ → (α → Prop) → Prop
  | .pure a, _, Q => Q a
  | .liftBind _ k, n, Q => 0 < n ∧ ∀ u, QB (k u) (n - 1) Q

variable {α β γ : Type}

theorem qb_pure (a : α) (n : ℕ) (Q : α → Prop) :
    QB (pure a : OracleComp PermSpec α) n Q ↔ Q a := Iff.rfl

theorem qb_ret (a : α) (n : ℕ) : QB (pure a : OracleComp PermSpec α) n fun _ ↦ True := trivial

theorem qb_query_bind (q : PermSpec.Domain) (k : PermSpec.Range q → OracleComp PermSpec α)
    (n : ℕ) (Q : α → Prop) :
    QB (liftM (PermSpec.query q) >>= k) n Q ↔ 0 < n ∧ ∀ u, QB (k u) (n - 1) Q := Iff.rfl

theorem QB.mono {X : OracleComp PermSpec α} :
    ∀ {n m : ℕ} {Q R : α → Prop}, QB X n Q → n ≤ m → (∀ a, Q a → R a) → QB X m R := by
  induction X using OracleComp.inductionOn with
  | pure a => intro n m Q R h _ hQR; exact hQR a h
  | query_bind q k ih =>
    intro n m Q R h hnm hQR
    rw [qb_query_bind] at h ⊢
    exact ⟨by omega, fun u ↦ ih u (h.2 u) (by omega) hQR⟩

/-- **Sequencing**: the calls add, the continuation charged only at the values the first part
returns. -/
theorem QB.bind {X : OracleComp PermSpec α} {f : α → OracleComp PermSpec β} :
    ∀ {a b : ℕ} {P : α → Prop} {R : β → Prop}, QB X a P → (∀ x, P x → QB (f x) b R) →
      QB (X >>= f) (a + b) R := by
  induction X using OracleComp.inductionOn with
  | pure x =>
    intro a b P R hX hf
    rw [pure_bind]
    exact (hf x hX).mono (by omega) fun _ h ↦ h
  | query_bind q k ih =>
    intro a b P R hX hf
    rw [bind_assoc, qb_query_bind]
    rw [qb_query_bind] at hX
    refine ⟨by omega, fun u ↦ ?_⟩
    exact (ih u (hX.2 u) hf).mono (by omega) fun _ h ↦ h

theorem QB.bind_le {X : OracleComp PermSpec α} {f : α → OracleComp PermSpec β} {a b c : ℕ}
    {P : α → Prop} {R : β → Prop} (hX : QB X a P) (hf : ∀ x, P x → QB (f x) b R)
    (h : a + b ≤ c) : QB (X >>= f) c R :=
  (hX.bind hf).mono h fun _ h ↦ h

theorem QB.map {X : OracleComp PermSpec α} {n : ℕ} {P : α → Prop} {R : β → Prop} (g : α → β)
    (hX : QB X n P) (hg : ∀ a, P a → R (g a)) : QB (g <$> X) n R := by
  rw [map_eq_bind_pure_comp]
  exact hX.bind_le (fun a ha ↦ (qb_pure _ 0 _).2 (hg a ha)) (by omega)

/-- **`QB` bounds the calls on every path.** -/
theorem QB.total {X : OracleComp PermSpec α} :
    ∀ {n : ℕ} {Q : α → Prop}, QB X n Q → IsTotalQueryBound X n := by
  induction X using OracleComp.inductionOn with
  | pure a => intro n Q _; trivial
  | query_bind q k ih =>
    intro n Q h
    rw [qb_query_bind] at h
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨h.1, fun u ↦ ih u (h.2 u)⟩

theorem qb_permF (x : KeccakState) : QB (permF x) 1 fun _ ↦ True := by
  unfold permF
  rw [← bind_pure (liftM _)]
  exact (qb_query_bind _ _ _ _).2 ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-! ## Lists and arrays -/

theorem qb_mapM (f : β → OracleComp PermSpec γ) (c : ℕ) :
    ∀ l : List β, (∀ a ∈ l, QB (f a) c fun _ ↦ True) →
      QB (l.mapM f) (l.length * c) fun r ↦ r.length = l.length
  | [], _ => by rw [List.mapM_nil]; exact (qb_pure _ _ _).2 rfl
  | a :: l, hf => by
    rw [List.mapM_cons, List.length_cons]
    refine (hf a List.mem_cons_self).bind_le (fun b _ ↦
      (qb_mapM f c l fun a' ha' ↦ hf a' (List.mem_cons_of_mem _ ha')).bind_le
        (fun r hr ↦ (qb_pure _ 0 _).2 (by rw [List.length_cons, hr])) le_rfl) ?_
    rw [Nat.succ_mul]; omega

theorem qb_arrayMapM (f : β → OracleComp PermSpec γ) (c : ℕ) (xs : Array β)
    (hf : ∀ a, QB (f a) c fun _ ↦ True) : QB (xs.mapM f) (xs.size * c) fun _ ↦ True := by
  rw [Array.mapM_eq_mapM_toList, ← Array.length_toList]
  exact (qb_mapM f c xs.toList fun a _ ↦ hf a).map _ fun _ _ ↦ trivial

/-! ## Keccak-256 over `π` and the sponge -/

theorem qb_absorbWith : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    QB (absorbWith permF blocks state data) (blocks + 1) fun _ ↦ True
  | 0, state, data => qb_permF _
  | blocks + 1, state, data => by
    simp only [absorbWith]
    exact (qb_permF _).bind_le (fun _ _ ↦ qb_absorbWith blocks _ _) (by omega)

/-- **Keccak-256 over `π` of `n` bytes makes `⌊n / 136⌋ + 1` calls.** -/
theorem qb_keccak256With (data : List UInt8) :
    QB (keccak256With permF data) (data.length / 136 + 1) fun _ ↦ True := by
  unfold keccak256With
  exact (qb_absorbWith _ _ _).bind_le (fun _ _ ↦ qb_ret _ 0) (by simp [rate])

theorem qb_keccak256With_le {data : List UInt8} {k : ℕ} (h : data.length < 136 * k) :
    QB (keccak256With permF data) k fun _ ↦ True :=
  (qb_keccak256With data).mono (by omega) fun _ h ↦ h

theorem qb_duplex (sp : Sponge) : QB (duplex permF sp) 1 fun _ ↦ True := by
  unfold duplex
  exact (qb_permF _).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl

theorem qb_absorb (sp : Sponge) (x : E) (tag : ℕ) :
    QB (Compile.absorb permF sp x tag) 1 fun _ ↦ True := by
  unfold Compile.absorb
  split
  · exact (qb_duplex sp).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl
  · exact (qb_ret _ 0).bind_le (fun _ _ ↦ qb_ret _ 1) le_rfl

theorem qb_squeeze (sp : Sponge) : QB (squeeze permF sp) 1 fun _ ↦ True := by
  unfold squeeze
  exact (qb_duplex sp).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl

/-! ## Lengths -/

theorem len_wordBytes (w : UInt64) : (wordBytes w).length = 8 := by simp [wordBytes]

theorem len_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  rw [digestBytes, List.length_flatMap]
  simp [len_wordBytes]

theorem len_flatMap_kBytes (row : List K) : (row.flatMap kBytes).length = 8 * row.length := by
  induction row with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [kBytes, len_wordBytes]
    ring

/-! ## Merkle trees -/

theorem len_stackWordFast (μ R : ℕ) (stack : Array K) (p : ℕ) :
    (LeanVM.Prover.stackWordFast μ R stack p).length = 64 := by
  unfold LeanVM.Prover.stackWordFast LeanVM.Prover.stackWordFast.stackWordOf
  split <;> simp

theorem qb_leafDigestsM (h : ℕ) (word : Word) (hw : ∀ p, (word p).length ≤ 64) :
    QB (LeanVM.Prover.leafDigestsM permF h word) (2 ^ h * 4) fun _ ↦ True := by
  unfold LeanVM.Prover.leafDigestsM
  have := qb_arrayMapM (fun i ↦ keccak256With permF ((word i).flatMap kBytes)) 4
    (Array.range (2 ^ h)) fun i ↦ qb_keccak256With_le (by rw [len_flatMap_kBytes]; have := hw i; omega)
  rwa [Array.size_range] at this

theorem qb_parentsM (level : Array Digest) (n : ℕ) :
    QB (LeanVM.Prover.parentsM permF level n) n fun _ ↦ True := by
  unfold LeanVM.Prover.parentsM
  have := qb_arrayMapM (fun j ↦ keccak256With permF (digestBytes (level.getD (2 * j) default) ++
    digestBytes (level.getD (2 * j + 1) default))) 1 (Array.range n) fun j ↦ qb_keccak256With_le
    (by rw [List.length_append, len_digestBytes, len_digestBytes]; omega)
  rwa [Array.size_range, Nat.mul_one] at this

theorem qb_levelsM : ∀ (k : ℕ) (level : Array Digest),
    QB (LeanVM.Prover.levelsM permF k level) (2 ^ k) fun _ ↦ True
  | 0, level => qb_ret _ _
  | k + 1, level => by
    simp only [LeanVM.Prover.levelsM]
    exact (qb_parentsM level _).bind_le (fun up _ ↦
      (qb_levelsM k up).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl) (by rw [pow_succ]; omega)

/-- **A Merkle tree of `2^h` rows of at most `64` words**: at most `5 · 2^h` calls. -/
theorem qb_buildTreeM (h : ℕ) (word : Word) (hw : ∀ p, (word p).length ≤ 64) :
    QB (LeanVM.Prover.buildTreeM permF h word) (2 ^ h * 5) fun _ ↦ True := by
  unfold LeanVM.Prover.buildTreeM
  exact (qb_leafDigestsM h word hw).bind_le (fun _ _ ↦
    (qb_levelsM h _).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl) (by omega)

/-! ## The expansion of a pruned multiproof -/

/-- **A small pruned multiproof**: at most `2^10` positions, rows of at most `2^10` words. -/
def MultiSmall (mp : Multi) : Prop := mp.1.length ≤ 2 ^ 10 ∧ ∀ r ∈ mp.2.1, r.length ≤ 2 ^ 10

theorem qb_pairUp : ∀ level : List (ℕ × Digest),
    QB (pairUp level) (level.length / 2) fun up ↦ up.length ≤ level.length / 2
  | (a, x) :: (b, y) :: rest => by
    simp only [pairUp, List.length_cons]
    refine (qb_keccak256With_le (k := 1) ?_).bind_le (fun h _ ↦ (qb_pairUp rest).bind_le
      (fun r hr ↦ (qb_pure _ 0 _).2 ?_) le_rfl) ?_
    · rw [List.length_append, len_digestBytes, len_digestBytes]; omega
    · rw [List.length_cons]; omega
    · omega
  | [] => (qb_pure _ _ _).2 (Nat.zero_le _)
  | [_] => (qb_pure _ _ _).2 (Nat.zero_le _)

theorem length_withSibling (p : ℕ) (d s : Digest) : (withSibling p d s).length = 2 := by
  unfold withSibling; split <;> rfl

/-- `expandLevel` at most doubles the known nodes. -/
theorem length_expandLevel : ∀ (known : List (ℕ × Digest)) (sibs : List Digest),
    (expandLevel known sibs).1.length ≤ 2 * known.length
  | (p, d) :: (q, e) :: rest, sibs => by
    by_cases hq : q = p ^^^ 1
    · have ih := length_expandLevel rest sibs
      simp only [expandLevel, hq, ↓reduceIte, List.length_cons]
      omega
    · cases sibs with
      | nil => simp [expandLevel, hq]
      | cons s ss =>
        have ih := length_expandLevel ((q, e) :: rest) ss
        simp only [expandLevel, hq, ↓reduceIte, List.length_append, length_withSibling,
          List.length_cons] at ih ⊢
        omega
  | [(p, d)], s :: ss => by simp [expandLevel, length_withSibling]
  | [(p, d)], [] => by simp [expandLevel]
  | [], sibs => by simp [expandLevel]

/-- **The levels of the expansion**: at most `h · k` calls from `k` known leaves. -/
theorem qb_expandLevels : ∀ (h : ℕ) (known : List (ℕ × Digest)) (sibs : List Digest),
    QB (expandLevels h known sibs) (h * known.length) fun _ ↦ True
  | 0, _, _ => qb_ret _ _
  | h + 1, known, sibs => by
    have hl := length_expandLevel known sibs
    rcases hE : expandLevel known sibs with ⟨level, rest⟩
    rw [hE] at hl
    dsimp only at hl
    simp only [expandLevels, hE]
    refine (qb_pairUp level).bind_le (b := h * known.length) (fun up hup ↦
      ((qb_expandLevels h up rest).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl).mono
        (Nat.mul_le_mul_left h (by omega)) fun _ h ↦ h) ?_
    rw [Nat.succ_mul]; omega

theorem len_rowAt (mp : Multi) (R : ℕ) (hR : ∀ r ∈ mp.2.1, r.length ≤ R) (p : ℕ) :
    (((mp.1.zip mp.2.1).find? fun e ↦ e.1 = p).elim [] fun e ↦ e.2.map K.ofLane).length ≤ R := by
  cases h : (mp.1.zip mp.2.1).find? fun e ↦ e.1 = p with
  | none => simp
  | some e =>
    simp only [Option.elim, List.length_map]
    exact hR _ (List.of_mem_zip (List.mem_of_find?_eq_some h)).2

/-- **The expansion of a small multiproof** in a tree of height `h`: at most `k · 61 + h · k` calls,
`k` its positions (a row of at most `2^10` words is `8192` bytes, `61` blocks). -/
theorem qb_expandMulti (mp : Multi) (height : ℕ) (ps : List ℕ) (hmp : MultiSmall mp) :
    QB (expandMulti mp height ps) (mp.1.length * 61 + height * mp.1.length) fun _ ↦ True := by
  unfold expandMulti
  refine (qb_mapM _ 61 mp.1 fun p _ ↦ (qb_keccak256With_le ?_).bind_le (fun _ _ ↦ qb_ret _ 0)
    le_rfl).bind_le (b := height * mp.1.length) (fun leaves hl ↦ ?_) le_rfl
  · rw [len_flatMap_kBytes]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 8 (len_rowAt mp _ hmp.2 p)) (by norm_num)
  · rw [← hl]
    exact (qb_expandLevels height leaves _).bind_le (fun _ _ ↦ qb_ret _ 0) le_rfl

/-! ## The verifier's program run -/

/-- **`fillRun` of a program of cost `n` quarters**, its commitments of height at most `H`, from a
state whose roots have height at most `H` and whose multiproofs are small, each expansion at most `M`
calls: at most `n` calls for the reads, samples, proofs of work and commitments, and `M` per
multiproof. -/
theorem qb_fillRun {α : Type} (H M : ℕ)
    (hM : ∀ mp : Multi, MultiSmall mp → ∀ h ≤ H, ∀ ps, QB (expandMulti mp h ps) M fun _ ↦ True)
    (p : Prog α) : ∀ (n : ℕ) (s : FillState), p.Costs H n (fun _ ↦ True) →
      (∀ r ∈ s.roots, r.2.1 ≤ H) → (∀ mp ∈ s.multis, MultiSmall mp) →
      QB (fillRun p s) (n + s.multis.length * M) fun _ ↦ True := by
  induction p with
  | ret a => intro n s _ _ _; exact qb_ret _ _
  | fail => intro n s _ _ _; exact qb_ret _ _
  | read k ih =>
    intro n s hc hr hm
    obtain ⟨h1, hk⟩ := hc
    simp only [fillRun]
    split
    · exact qb_ret _ _
    · next x xs _ =>
      exact (qb_absorb _ _ _).bind_le (b := (n - 1) + s.multis.length * M)
        (fun sp _ ↦ ih x (n - 1) _ (hk x) hr hm) (by omega)
  | sample k ih =>
    intro n s hc hr hm
    obtain ⟨h1, hk⟩ := hc
    simp only [fillRun]
    refine (qb_squeeze _).bind_le (b := (n - 4) + s.multis.length * M) (fun x _ ↦ ?_) (by omega)
    obtain ⟨c, sp⟩ := x
    exact ih c (n - 4) _ (hk c) hr hm
  | grind bits k ih =>
    intro n s hc hr hm
    obtain ⟨h1, hk⟩ := hc
    simp only [fillRun]
    split
    · exact qb_ret _ _
    · next x xs _ =>
      refine (qb_absorb _ _ _).bind_le (b := 1 + ((n - 5) + s.multis.length * M)) (fun sp _ ↦
        (qb_squeeze _).bind_le (b := (n - 5) + s.multis.length * M) (fun y _ ↦ ?_) le_rfl)
        (by omega)
      obtain ⟨_, sp'⟩ := y
      exact ih (n - 5) _ hk hr hm
  | commit height width k ih =>
    intro n s hc hr hm
    obtain ⟨hh, h2, hk⟩ := hc
    simp only [fillRun]
    split
    · next x0 x1 xs _ =>
      refine (qb_absorb _ _ _).bind_le (b := 1 + ((n - 2) + s.multis.length * M)) (fun sp _ ↦
        (qb_absorb _ _ _).bind_le (b := (n - 2) + s.multis.length * M) (fun sp' _ ↦ ?_) le_rfl)
        (by omega)
      split
      · next root _ =>
        refine ih (n - 2) _ hk ?_ hm
        intro r hr'
        rcases List.mem_append.mp hr' with h | h
        · exact hr r h
        · rw [List.mem_singleton] at h; subst h; exact hh
      · exact qb_ret _ _
    · exact qb_ret _ _
  | query i ps k ih =>
    intro n s hc hr hm
    obtain ⟨h1, hk⟩ := hc
    simp only [fillRun]
    split
    · next r height w mp rest hri hms =>
      have hH : height ≤ H := hr _ (List.mem_of_getElem? hri)
      have hmp : MultiSmall mp := hm mp (by rw [hms]; exact List.mem_cons_self)
      have hrest : ∀ m ∈ rest, MultiSmall m := fun m h ↦
        hm m (by rw [hms]; exact List.mem_cons_of_mem _ h)
      refine (hM mp hmp height hH ps).bind_le
        (b := (n - Prog.openCost H ps.length) + rest.length * M)
        (fun opens _ ↦ ih _ _ _ (hk _) hr hrest) ?_
      rw [hms, List.length_cons, Nat.succ_mul]; omega
    · exact qb_ret _ _

end PcsQuotient.EndToEnd.Core
