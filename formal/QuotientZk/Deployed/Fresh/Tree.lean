-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Fresh.Ops

/-!
# Fresh Fiat–Shamir inputs: Merkle trees

* Every tree only logs Keccak-256 inputs: nodes (`H(left ‖ right)`, 64 bytes, `NodeOf`), and leaves
  (a secret table's rows, longer than 192 bytes by hypothesis, `RowLike`; or public rows). Its
  levels are `depth + 1` (`trip_levels`, `trip_tree₀_secret`, `trip_tree₀_public`).
* **The witness table's root is fresh** (`trip_tree₀_key`): its first leaf's row is not an initial
  input, so its digest is a fresh answer; a fresh digest `a` is the first half of no 64-byte input
  (`KeyD`), so `H(a ‖ b)` is a fresh answer again, and the other nodes of its level have other left
  halves (answers held before it, which it is not). Up to the root, which is then the last half of
  no 96-byte input: the chain's first input, `st₀ ‖ rootWords root`, is fresh.
-/

open OracleComp OracleSpec QuotientRpm
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false

/-- A node of a level `l`: `H(x ‖ z)` for `x` in `l`. -/
def NodeOf (l : List Bytes32) (y : Inp) : Prop := ∃ x ∈ l, ∃ z : Bytes32, y = .inl (x.toList ++ z.toList)

/-- A 64-byte Keccak-256 input. -/
def Len64 (y : Inp) : Prop := ∃ b, y = .inl b ∧ b.length = 64

/-- A long Keccak-256 input (a secret row). -/
def RowLike (y : Inp) : Prop := ∃ b, y = .inl b ∧ 192 < b.length

/-- A Keccak-256 input. -/
def IsInl (y : Inp) : Prop := ∃ b, y = .inl b

theorem NodeOf.len64 {l : List Bytes32} {y : Inp} (h : NodeOf l y) : Len64 y := by
  obtain ⟨x, -, z, rfl⟩ := h
  exact ⟨_, rfl, by simp⟩

theorem NodeOf.mono {l l' : List Bytes32} (hl : ∀ x ∈ l, x ∈ l') {y : Inp} (h : NodeOf l y) :
    NodeOf l' y := by
  obtain ⟨x, hx, z, rfl⟩ := h
  exact ⟨x, hl x hx, z, rfl⟩

theorem Len64.isInl {y : Inp} (h : Len64 y) : IsInl y := by
  obtain ⟨b, h, -⟩ := h; exact ⟨b, h⟩
theorem RowLike.isInl {y : Inp} (h : RowLike y) : IsInl y := by
  obtain ⟨b, h, -⟩ := h; exact ⟨b, h⟩

/-- Fresh as a left half of 64 bytes and as the root words of 96 bytes. -/
def KeyD (K0 : List Inp) (st : DSt) (h : Bytes32) : Prop :=
  ∀ y ∈ dom K0 st, ∀ b, y = .inl b →
    (b.length = 64 → b.take 32 ≠ h.toList) ∧ (b.length = 96 → b.drop 32 ≠ rootWords h)

theorem KeyD.ext {K0 : List Inp} {Φ : Inp → Prop} {st st' : DSt} {h : Bytes32} (hk : KeyD K0 st h)
    (he : Ext Φ st st')
    (hΦ : ∀ y, Φ y → ∀ b, y = .inl b →
      (b.length = 64 → b.take 32 ≠ h.toList) ∧ (b.length = 96 → b.drop 32 ≠ rootWords h)) :
    KeyD K0 st' h :=
  fun y hy => (he.mem_dom hy).elim (hk y) (hΦ y)

theorem KeyD.of_noHit {K0 : List Inp} {st : DSt} {t : Inp} {u : Out} (hu : NoHit K0 st t u) :
    KeyD K0 (addE st t u) u.1 := fun y hy b hb =>
  have hy' := (mem_dom_addE K0 st t u y).mp hy
  ⟨fun _ => hu.left y hy' b hb, fun _ => hu.root y hy' b hb⟩

/-- A row is never a node nor the chain's 96-byte input. -/
theorem keyD_rowLike (h : Bytes32) (y : Inp) (hy : RowLike y) (b : List UInt8) (hb : y = .inl b) :
    (b.length = 64 → b.take 32 ≠ h.toList) ∧ (b.length = 96 → b.drop 32 ≠ rootWords h) := by
  obtain ⟨b', rfl, hl⟩ := hy
  cases hb
  exact ⟨fun h => by omega, fun h => by omega⟩

/-- A pub-only extension: no challenge appended. -/
def ExtP (Φ : Inp → Prop) (st st' : DSt) : Prop := Ext Φ st st' ∧ st'.hist = st.hist

theorem ExtP.refl {Φ : Inp → Prop} (st : DSt) : ExtP Φ st st := ⟨Ext.refl st, rfl⟩

theorem ExtP.trans {Φ : Inp → Prop} {st st' st'' : DSt} (h₁ : ExtP Φ st st') (h₂ : ExtP Φ st' st'') :
    ExtP Φ st st'' := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem ExtP.mono {Φ Ψ : Inp → Prop} {st st' : DSt} (h : ExtP Φ st st') (hΦ : ∀ y, Φ y → Ψ y) :
    ExtP Ψ st st' := ⟨h.1.mono hΦ, h.2⟩

theorem ExtP.of_addE {Φ : Inp → Prop} {st : DSt} {t : Inp} (u : Out) (ht : st.cache t = none)
    (hΦ : Φ t) : ExtP Φ st (addE st t u) := ⟨Ext.of_addE u ht hΦ, rfl⟩

section Trees

variable {S : Type} {P : Proto S Inp Out Msg Tbl Pos} {s : S} {cw : Fin 3 → Bytes32 → List UInt8}
  {K0 : List Inp}

/-- A Keccak-256 query of an input satisfying `Φ`, from `st₀`: the answer is held after it. -/
theorem trip_hashH_ext (m : List UInt8) (Φ : Inp → Prop) (hΦ : Φ (.inl m)) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀) (hashH m)
      (fun a st => ExtP Φ st₀ st ∧ CachedDig st a) :=
  (trip_hashH m _).mono (fun st hst => by
    subst hst
    exact ⟨fun v hv => ⟨ExtP.refl _, _, v, hv, rfl⟩, fun hc u _ =>
      ⟨ExtP.of_addE u hc hΦ, .inl m, u, by simp [addE_cache], rfl⟩⟩) (fun _ _ h => h)

/-- **One level up**: logs only nodes of the level; half as many digests, all held. -/
theorem trip_levelUp : ∀ (l : List Bytes32) (st₀ : DSt),
    Trip P s cw K0 (fun st => st = st₀) (levelUp l)
      (fun out st => ExtP (NodeOf l) st₀ st ∧ out.length = l.length / 2 ∧
        ∀ x ∈ out, CachedDig st x)
  | a :: b :: rest, st₀ => by
    unfold levelUp
    refine Trip.bind (trip_hashH_ext _ (NodeOf (a :: b :: rest))
      ⟨a, by simp, b, rfl⟩ st₀) fun h => Trip.intro fun st₁ ⟨he₁, hc₁⟩ =>
        Trip.bind (trip_levelUp rest st₁) fun t => ?_
    refine (Trip.pure _ _).mono (fun st ⟨he, hl, hc⟩ => ⟨he₁.trans (he.mono fun y hy =>
      hy.mono fun x hx => by simp [hx]), ?_, ?_⟩) (fun _ _ h => h)
    · simp [hl]; omega
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc₁.ext he.1
      · exact hc x hx
  | [a], st₀ => by
    unfold levelUp
    exact (Trip.pure _ _).mono (fun st hst => by subst hst; exact ⟨ExtP.refl _, by simp, by simp⟩)
      (fun _ _ h => h)
  | [], st₀ => by
    unfold levelUp
    exact (Trip.pure _ _).mono (fun st hst => by subst hst; exact ⟨ExtP.refl _, by simp, by simp⟩)
      (fun _ _ h => h)

/-- **A tree's levels**: only 64-byte inputs logged; `depth + 1` levels. -/
theorem trip_levels : ∀ (d : ℕ) (l : List Bytes32) (st₀ : DSt),
    Trip P s cw K0 (fun st => st = st₀) (levels d l)
      (fun lv st => ExtP Len64 st₀ st ∧ lv.length = d + 1)
  | 0, l, st₀ => by
    unfold levels
    exact (Trip.pure _ _).mono (fun st hst => by subst hst; exact ⟨ExtP.refl _, rfl⟩)
      (fun _ _ h => h)
  | d + 1, l, st₀ => by
    unfold levels
    refine Trip.bind (trip_levelUp l st₀) fun up => Trip.intro fun st₁ ⟨he₁, _, _⟩ =>
      Trip.bind (trip_levels d up st₁) fun rest => ?_
    exact (Trip.pure _ _).mono (fun st ⟨he, hl⟩ =>
      ⟨(he₁.mono fun y hy => hy.len64).trans he, by simp [hl]⟩) (fun _ _ h => h)

/-- One level up from a fresh left digest: a fresh digest again, the first of the next level. -/
theorem trip_levelUp_key (a b : Bytes32) (rest : List Bytes32) (st₀ : DSt) :
    Trip P s cw K0
      (fun st => st = st₀ ∧ KeyD K0 st₀ a ∧ ∀ x ∈ rest, CachedDig st₀ x)
      (levelUp (a :: b :: rest))
      (fun out st => ExtP (NodeOf (a :: b :: rest)) st₀ st ∧ out.length = (rest.length + 2) / 2 ∧
        (∀ x ∈ out, CachedDig st x) ∧ ∃ h out', out = h :: out' ∧ KeyD K0 st h) := by
  unfold levelUp
  have h1 : Trip P s cw K0
      (fun st => GInv P.n K0 st ∧ (st = st₀ ∧ KeyD K0 st₀ a ∧ ∀ x ∈ rest, CachedDig st₀ x))
      (hashH (a.toList ++ b.toList))
      (fun h st => ExtP (NodeOf (a :: b :: rest)) st₀ st ∧ CachedDig st h ∧ KeyD K0 st h ∧
        ∀ x ∈ rest, x ≠ h) := by
    refine (trip_hashH_fresh _ _).mono ?_ (fun _ _ h => h)
    rintro st ⟨hg, rfl, hk, hrest⟩
    have hm : (.inl (a.toList ++ b.toList) : Inp) ∉ dom K0 st := fun hm =>
      (hk _ hm _ rfl).1 (by simp) (by simp)
    refine ⟨hm, fun u hu => ⟨ExtP.of_addE u (hg.cache_none hm) ⟨a, by simp, b, rfl⟩,
      ⟨.inl (a.toList ++ b.toList), u, by simp [addE_cache], rfl⟩, KeyD.of_noHit hu,
      fun x hx e => ?_⟩⟩
    obtain ⟨y, v, hy, hv⟩ := hrest x hx
    exact hu.dig y (hg.dom_of y (by simp [hy])) v hy (hv.trans e)
  refine Trip.ginv (Trip.bind h1 fun h => Trip.intro fun st₁ hmid => ?_)
  obtain ⟨he₁, hc₁, hk₁, hne⟩ := hmid
  refine Trip.bind (trip_levelUp rest st₁) fun t => ?_
  refine (Trip.pure _ _).mono (fun st hst => ?_) (fun _ _ h => h)
  obtain ⟨he, hl, hc⟩ := hst
  refine ⟨he₁.trans (he.mono fun y hy => hy.mono fun x hx => by simp [hx]),
    by simp [hl], ?_, h, t, rfl, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc₁.ext he.1
    · exact hc x hx
  · refine hk₁.ext he.1 fun y hy b' hb' => ?_
    obtain ⟨x, hx, z, rfl⟩ := hy
    cases hb'
    refine ⟨fun _ => ?_, fun hl => by simp at hl⟩
    have hxh := hne x hx
    simp only [Vector.length_toList, List.take_left']
    exact fun e => hxh (Vector.toList_inj.mp e)

/-- **The root of a tree whose first leaf is fresh is fresh** (`KeyD`); only 64-byte inputs
logged. -/
theorem trip_levels_key : ∀ (d : ℕ) (a b : Bytes32) (rest : List Bytes32) (st₀ : DSt),
    rest.length + 2 = 2 ^ (d + 1) →
    Trip P s cw K0
      (fun st => st = st₀ ∧ KeyD K0 st₀ a ∧ ∀ x ∈ rest, CachedDig st₀ x)
      (levels (d + 1) (a :: b :: rest))
      (fun lv st => ExtP Len64 st₀ st ∧ lv.length = d + 2 ∧ KeyD K0 st (rootOf lv))
  | 0, a, b, rest, st₀, hl => by
    have h0 : rest.length + 2 = 2 := by simpa using hl
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    unfold levels
    refine Trip.bind (trip_levelUp_key a b [] st₀) fun up => Trip.intro fun st₁ hpost => ?_
    obtain ⟨he₁, hl₁, -, h, out', rfl, hk⟩ := hpost
    have ho : out' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl₁)
    subst ho
    unfold levels
    exact (Trip.pure _ _).mono (fun st hst => by
      subst hst
      exact ⟨he₁.mono fun y hy => hy.len64, rfl, by simpa [rootOf] using hk⟩) (fun _ _ h => h)
  | d + 1, a, b, rest, st₀, hl => by
    unfold levels
    refine Trip.bind (trip_levelUp_key a b rest st₀) fun up => Trip.intro fun st₁ hpost => ?_
    obtain ⟨he₁, hl₁, hc₁, h, out', rfl, hk⟩ := hpost
    have h2 : 2 ^ 1 ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlen : out'.length + 1 = 2 ^ (d + 1) := by
      have : (rest.length + 2) / 2 = 2 ^ (d + 1) := by
        rw [hl, pow_succ]; omega
      simpa [this] using hl₁
    obtain ⟨b', rest', rfl⟩ : ∃ b' rest', out' = b' :: rest' := by
      cases out' with
      | nil => simp at hlen; omega
      | cons b' rest' => exact ⟨b', rest', rfl⟩
    have ih := (trip_levels_key d h b' rest' st₁ (by simp at hlen; omega)).mono
      (fun st hst => ⟨hst, hk, fun x hx => hc₁ x (by simp [hx])⟩) (fun _ _ h => h)
    refine Trip.bind ih fun lv => ?_
    refine (Trip.pure _ _).mono (fun st hst => ?_) (fun _ _ h => h)
    obtain ⟨he, hlv, hkr⟩ := hst
    refine ⟨(he₁.mono fun y hy => hy.len64).trans he, by simp [hlv], ?_⟩
    cases lv with
    | nil => simp at hlv
    | cons c cs => simpa [rootOf, List.getLast?_cons_cons] using hkr

/-! ## Leaves -/

/-- A secret leaf: a row, held after it once the table's challenges are drawn. -/
theorem trip_leafH_ext (k : Tbl) (x : ℕ) (st₀ : DSt) (hrow : ∀ h k x, RowLike (P.rowFn s h k x)) :
    Trip P s cw K0 (fun st => st = st₀) (leafH k x)
      (fun a st => ExtP RowLike st₀ st ∧ (P.cK k ≤ st₀.hist.length → CachedDig st a)) := by
  refine (trip_leafH k x _).mono (fun st hst => ?_) (fun _ _ h => h)
  subst hst
  intro r
  refine ⟨fun h => ⟨ExtP.refl _, fun h' => absurd h' (by omega)⟩, fun _ =>
    ⟨fun v hv => ⟨ExtP.refl _, fun _ => ⟨r, v, hv, rfl⟩⟩, fun hc u _ =>
      ⟨ExtP.of_addE u hc (hrow _ _ _), fun _ => ⟨r, u, by simp [addE_cache], rfl⟩⟩⟩⟩

/-- A public leaf. -/
theorem trip_hashH_inl (m : List UInt8) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀) (hashH m) (fun a st => ExtP IsInl st₀ st ∧ CachedDig st a) :=
  trip_hashH_ext m IsInl ⟨m, rfl⟩ st₀

/-- The leaves of a secret table. -/
theorem trip_leaves (k : Tbl) (l : List ℕ) (st₀ : DSt) (hrow : ∀ h k x, RowLike (P.rowFn s h k x)) :
    Trip P s cw K0 (fun st => st = st₀) (l.mapM (leafH k))
      (fun ls st => ExtP RowLike st₀ st ∧ ls.length = l.length ∧
        (P.cK k ≤ st₀.hist.length → ∀ x ∈ ls, CachedDig st x)) := by
  have h := trip_mapM (P := P) (s := s) (cw := cw) (K0 := K0) (leafH k)
    (fun acc st => ExtP RowLike st₀ st ∧
      (P.cK k ≤ st₀.hist.length → ∀ x ∈ acc, CachedDig st x))
    (fun a acc => Trip.intro fun st₁ ⟨he₁, hc₁⟩ => (trip_leafH_ext k a st₁ hrow).mono
      (fun st h => h) (fun b st ⟨he, hc⟩ => ⟨he₁.trans he, fun hk x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact (hc₁ hk x hx).ext he.1
        · rw [List.mem_singleton.mp hx]; exact hc (by rw [he₁.2]; exact hk)⟩)) l []
  exact h.mono (fun st hst => ⟨by subst hst; exact ExtP.refl _, by simp⟩) (fun ls st hp =>
    ⟨hp.1.1, hp.2, by simpa using hp.1.2⟩)

/-- The leaves of the witness table: the first one's digest is fresh. -/
theorem trip_leaves_key (k : Tbl) (d : ℕ) (st₀ : DSt) (hrow : ∀ h k x, RowLike (P.rowFn s h k x))
    (hcK : P.cK k = 0) (h0 : P.rowFn s [] k 0 ∉ dom K0 st₀) :
    Trip P s cw K0 (fun st => st = st₀) ((List.range (2 ^ (d + 1))).mapM (leafH k))
      (fun ls st => ExtP RowLike st₀ st ∧ ∃ a b rest, ls = a :: b :: rest ∧
        rest.length + 2 = 2 ^ (d + 1) ∧ KeyD K0 st a ∧ ∀ x ∈ rest, CachedDig st x) := by
  have h2 : 2 ≤ 2 ^ (d + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ (d + 1) = m + 1 := ⟨2 ^ (d + 1) - 1, by omega⟩
  rw [hm, List.range_succ_eq_map, List.mapM_cons]
  have hr : P.rowFn s (st₀.hist.take (P.cK k)) k ⟨0 % 2 ^ 23, Nat.mod_lt _ (by positivity)⟩ =
      P.rowFn s [] k 0 := by
    rw [hcK]; rfl
  have hfirst : Trip P s cw K0 (fun st => GInv P.n K0 st ∧ st = st₀) (leafH k 0)
      (fun a st => ExtP RowLike st₀ st ∧ KeyD K0 st a ∧ CachedDig st a) := by
    refine (trip_leafH k 0 _).mono (fun st hst => ?_) (fun _ _ h => h)
    obtain ⟨hg, rfl⟩ := hst
    intro r
    have hrr : r = P.rowFn s [] k 0 := hr
    have hc : st.cache r = none := hg.cache_none (by rw [hrr]; exact h0)
    refine ⟨fun h => absurd h (by omega), fun _ => ⟨fun v hv => by rw [hc] at hv; simp at hv,
      fun _ u hu => ⟨ExtP.of_addE u hc (hrow _ _ _), KeyD.of_noHit hu,
        ⟨r, u, by simp [addE_cache], rfl⟩⟩⟩⟩
  refine Trip.ginv (Trip.bind hfirst fun a => Trip.intro fun st₁ ⟨he₁, hk₁, hc₁⟩ =>
    Trip.bind (trip_leaves k _ st₁ hrow) fun bs => ?_)
  refine (Trip.pure _ _).mono (fun st ⟨he, hl, hc⟩ => ?_) (fun _ _ h => h)
  have hcb : ∀ x ∈ bs, CachedDig st x := hc (by rw [hcK]; omega)
  obtain ⟨b, rest, rfl⟩ : ∃ b rest, bs = b :: rest := by
    cases bs with
    | nil => simp at hl; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  refine ⟨he₁.trans he, a, b, rest, rfl, by simp at hl; omega, hk₁.ext he.1 fun y hy =>
    keyD_rowLike a y hy, fun x hx => hcb x (by simp [hx])⟩

/-- **A secret table's tree**: rows and nodes logged; `depth₀ + 1` levels. -/
theorem trip_tree₀_secret (sh : OpenShape) (k : Tbl) (hk : sh.secret = some k) (st₀ : DSt)
    (hrow : ∀ h k x, RowLike (P.rowFn s h k x)) :
    Trip P s cw K0 (fun st => st = st₀) (tree₀ sh)
      (fun lv st => ExtP (fun y => Len64 y ∨ RowLike y) st₀ st ∧ lv.length = sh.depth₀ + 1) := by
  simp only [tree₀, hk]
  refine Trip.bind (trip_leaves k _ st₀ hrow) fun leaves => Trip.intro fun st₁ ⟨he₁, _, _⟩ => ?_
  exact (trip_levels sh.depth₀ leaves st₁).mono (fun st h => h) (fun lv st ⟨he, hl⟩ =>
    ⟨(he₁.mono fun y h => Or.inr h).trans (he.mono fun y h => Or.inl h), hl⟩)

/-- **A public tree**: Keccak-256 inputs logged; `depth₀ + 1` levels. -/
theorem trip_tree₀_public (sh : OpenShape) (hk : sh.secret = none) (st₀ : DSt) :
    Trip P s cw K0 (fun st => st = st₀) (tree₀ sh)
      (fun lv st => ExtP IsInl st₀ st ∧ lv.length = sh.depth₀ + 1) := by
  simp only [tree₀, hk]
  have h := trip_mapM (P := P) (s := s) (cw := cw) (K0 := K0) hashH
    (fun _ st => ExtP IsInl st₀ st)
    (fun a acc => Trip.intro fun st₁ he₁ => (trip_hashH_inl a st₁).mono (fun st h => h)
      (fun b st ⟨he, _⟩ => he₁.trans he)) sh.pubRows []
  refine Trip.bind (h.mono (fun st hst => by subst hst; exact ExtP.refl _) (fun _ _ h => h))
    fun leaves => Trip.intro fun st₁ ⟨he₁, _⟩ => ?_
  exact (trip_levels sh.depth₀ leaves st₁).mono (fun st h => h) (fun lv st ⟨he, hl⟩ =>
    ⟨he₁.trans (he.mono fun y h => h.isInl), hl⟩)

/-- **The witness table's tree**: its root is fresh (`KeyD`), if its first row is not held. -/
theorem trip_tree₀_key (sh : OpenShape) (k : Tbl) (hk : sh.secret = some k) (d : ℕ)
    (hd : sh.depth₀ = d + 1) (st₀ : DSt) (hrow : ∀ h k x, RowLike (P.rowFn s h k x))
    (hcK : P.cK k = 0) (h0 : P.rowFn s [] k 0 ∉ dom K0 st₀) :
    Trip P s cw K0 (fun st => st = st₀) (tree₀ sh)
      (fun lv st => ExtP (fun y => Len64 y ∨ RowLike y) st₀ st ∧ lv.length = sh.depth₀ + 1 ∧
        KeyD K0 st (rootOf lv)) := by
  simp only [tree₀, hk, hd]
  refine Trip.bind (trip_leaves_key k d st₀ hrow hcK h0) fun leaves => Trip.intro fun st₁ hp => ?_
  obtain ⟨he₁, a, b, rest, rfl, hl, hka, hc⟩ := hp
  exact (trip_levels_key d a b rest st₁ hl).mono (fun st h => ⟨h, hka, hc⟩) (fun lv st ⟨he, hlv, hkr⟩ =>
    ⟨(he₁.mono fun y h => Or.inr h).trans (he.mono fun y h => Or.inl h), hlv, hkr⟩)

end Trees


end QuotientZk.Deployed.Fresh
