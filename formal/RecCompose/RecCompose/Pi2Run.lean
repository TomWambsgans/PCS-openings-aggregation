-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's verifier is `formal/RecStatement`'s
-- (`RecStatement/Verifier.lean`: `reduceWith`, `runWith`, `run`).
import RecCompose.Chan

/-!
# π2's run: its public data and its success do not depend on the hashes

`RecStatement.runWith F s iv input stream`, over any lawful monad and any permutation `F`, at any IV: it succeeds exactly
when the stream has `pi2Bytes s` bytes (π2's public data, `W`'s and `Q`'s roots, the `2^r` fold values and `ξ`; the
challenges read none), and then its public scalars are `pi2Pubs s input stream` (the statement's four words, then the
public reads at their offsets) and its pair points theirs (`runWith_post`). So the run over the permutation and the
run over Keccak-f[1600] at any other IV (`RecStatement.run`) agree on them (`run_ok_of_runWith`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A public read's scalars, at `cur`. -/
def readValue (d : Array UInt8) (cur : ℕ) : RecStatement.Read → List E
  | .integer b => [eK (UInt64.ofNat (integerAt d cur b))]
  | .root => [halfAt d cur, halfAt d (cur + 16)]
  | .scalar => [scalarAt d cur]

/-- The public scalars after a read at `cur`. -/
def pubsStep (d : Array UInt8) (cur : ℕ) (rd : RecStatement.Read) (pubs : List E) : List E :=
  pubs ++ readValue d cur rd

/-- **π2's public scalars** on a stream: the statement's four words, then each public read at its offset. -/
def pi2Pubs (s : RecStatement.Spec) (input : List UInt8) (stream : Array UInt8) : List E :=
  foldReads RecStatement.Read.bytes pubsStep stream 0 s.reads (publicWordsOf input)

/-- **The bytes π2's verifier reads**: the public reads, `W`'s and `Q`'s roots, the `2^r` fold values and `ξ`. -/
def pi2Bytes (s : RecStatement.Spec) : ℕ :=
  (s.reads.map RecStatement.Read.bytes).sum + (32 + (32 + (24 * 2 ^ s.logRow + 24)))

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem reads_reduceWith (F : KeccakState → m KeccakState) (s : RecStatement.Spec) (stmt : List E) :
    Reads (RecStatement.reduceWith F s stmt) (pi2Bytes s) fun d cur r ↦
      r.scalars = foldReads RecStatement.Read.bytes pubsStep d cur s.reads stmt ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint := by
  unfold RecStatement.reduceWith
  refine reads_mono (reads_bind (reads_forIn RecStatement.Read.bytes pubsStep _ (fun rd b ↦ ?_) s.reads stmt)
    fun pubs _ ↦
      reads_bind reads_nextRoot fun wRoot _ ↦
      reads_bind (reads_sample F) fun α _ ↦
      reads_bind (reads_sample F) fun β _ ↦
      reads_bind (reads_sample F) fun γ _ ↦
      reads_bind reads_nextRoot fun qRoot _ ↦
      reads_bind (reads_sample F) fun t _ ↦
      reads_bind (reads_nextScalars _) fun a _ ↦
      reads_bind reads_nextScalar fun ξ _ ↦
      reads_bind (reads_sample F) fun ρ _ ↦ reads_pure _) (by unfold pi2Bytes; omega) ?_
  · cases rd with
    | integer bytes =>
      refine reads_mono (reads_bind (reads_nextInteger bytes) fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
    | root =>
      refine reads_mono (reads_bind reads_nextRoot fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
    | scalar =>
      refine reads_mono (reads_bind reads_nextScalar fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
  · rintro d cur r ⟨pubs, hpubs, w, -, α, -, β, -, γ, -, q, -, t, -, a, -, ξ, -, ρ, -, hr⟩
    subst hr
    exact ⟨hpubs, rfl⟩

/-- **π2's run, over any permutation, at any IV**: it succeeds exactly when the stream has `pi2Bytes s` bytes, and then
its public scalars are `pi2Pubs` and its pair points theirs. -/
theorem runWith_post (F : KeccakState → m KeccakState) (s : RecStatement.Spec) (iv input : List UInt8)
    (stream : Array UInt8) :
    Holds (RecStatement.runWith F s iv input stream) fun o ↦
      (∀ r, o.result = .ok r → stream.size = pi2Bytes s ∧ r.scalars = pi2Pubs s input stream ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint) ∧
      (stream.size = pi2Bytes s → ∃ r, o.result = .ok r) := by
  unfold RecStatement.runWith
  refine holds_bind (holds_true _) fun seed _ ↦ holds_bind (Q := fun p ↦
    (∀ r, p.1 = .ok r → stream.size = pi2Bytes s ∧ r.scalars = pi2Pubs s input stream ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint) ∧
      (stream.size = pi2Bytes s → ∃ r, p.1 = .ok r)) ?_ fun p hp ↦ ?_
  · rw [ExceptT.run_bind, StateT.run_bind]
    refine holds_bind (reads_reduceWith F s (publicWordsOf input) (Chan.start seed stream)) ?_
    rintro ⟨e, c'⟩ ⟨hd, hok, hfit⟩
    simp only [Chan.start] at hd hok hfit
    cases e with
    | error err =>
      simp only [StateT.run_pure]
      refine holds_pure ⟨fun r hr ↦ absurd hr (by simp), fun hsz ↦ ?_⟩
      obtain ⟨a, ha⟩ := hfit (by omega)
      exact absurd ha (by simp)
    | ok r =>
      simp only
      obtain ⟨hcur, hsc, hpp⟩ := hok r rfl
      rw [ExceptT.run_bind, StateT.run_bind, finish_run]
      simp only [pure_bind]
      split_ifs with hf
      · simp only
        refine holds_pure ⟨fun r' hr' ↦ ?_, fun _ ↦ ⟨r, rfl⟩⟩
        simp only [Except.ok.injEq] at hr'
        subst hr'
        refine ⟨by rw [← hd, ← hf, hcur]; omega, hsc, hpp⟩
      · simp only [StateT.run_pure]
        refine holds_pure ⟨fun r' hr' ↦ absurd hr' (by simp), fun hsz ↦ absurd ?_ hf⟩
        rw [hcur, hd, hsz]; omega
  · obtain ⟨result, chan⟩ := p
    exact holds_pure hp

/-- A postcondition of a computation in `Id` holds of its value. -/
theorem holds_id {α : Type} {X : Id α} {P : α → Prop} (h : Holds X P) : P X.run := by
  have h2 : ((X.run, P X.run) : α × Prop) = (X.run, True) := h
  exact of_eq_true (congrArg Prod.snd h2)

end Generic

/-- **The run over the permutation and the run over Keccak-f[1600] agree on the public data**: if π2's run over any `F`
at any IV succeeds, so does `RecStatement.run` at any IV, with the same public scalars and pair points. -/
theorem run_ok_of_runWith {m : Type → Type} [Monad m] [LawfulMonad m] (s : RecStatement.Spec) (input : List UInt8)
    (stream : Array UInt8) (iv' : List UInt8) (r : RecStatement.Reduced) (hsz : stream.size = pi2Bytes s)
    (hsc : r.scalars = pi2Pubs s input stream) (hpp : r.pairPoints = r.scalars.map RecStatement.pairPoint) :
    ∃ r', (RecStatement.run s iv' input stream).result = .ok r' ∧ r'.scalars = r.scalars ∧
      r'.pairPoints = r.pairPoints := by
  have h := holds_id (runWith_post (m := Id) (fun x ↦ pure (keccakF1600 x)) s iv' input stream)
  obtain ⟨r', hr'⟩ := h.2 hsz
  obtain ⟨-, hsc', hpp'⟩ := h.1 r' hr'
  exact ⟨r', hr', by rw [hsc', hsc], by rw [hpp', hpp, hsc', hsc]⟩

end RecCompose
