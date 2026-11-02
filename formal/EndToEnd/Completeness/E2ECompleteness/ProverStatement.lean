-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): Keccak-256 (`keccak256`, `Digest.toBytes`), the fields.
import E2ECompleteness.End
import Compose.Reduce

/-!
# The Statement's statement is `formal/Completeness`'s

A witness of the Statement (`PcsQuotient.Secret`, `Vector`s) read as `formal/Completeness`'s
(`secretOf`, functions on `Fin 32`, `End.lean`) proves the same statement (`secretOf_statement`:
both hash with leanerVM's `keccak256` and fold the path the same way), and the reduction's target,
`Compose.Reduce.target` of the statement's halves, is F1's target of the deployed instance on
Completeness's statement words (**`target_stmt`**).
-/

open LeanVM LeanVM.Parameters Finset
open QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness

/-- A vector's entries listed in order. -/
theorem ofFn_getElem_vector {n : ℕ} (v : Vector UInt8 n) : List.ofFn (fun i : Fin n ↦ v[i]) = v.toList := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- **`pair`, transcribed twice.** -/
theorem pair_secretOf (a b : PcsQuotient.Bytes32) :
    Completeness.pair (fun i ↦ a[i]) (fun i ↦ b[i]) = fun i ↦ (PcsQuotient.pair a b)[i] := by
  funext i
  simp only [Completeness.pair, PcsQuotient.pair, ofFn_getElem_vector]

theorem replicate_fn (c : UInt8) : (fun _ : Fin 32 ↦ c) = fun i : Fin 32 ↦ (Vector.replicate 32 c)[i] := by
  funext i
  simp

/-- The path folded twice: the same nodes. -/
theorem foldl_root (w : PcsQuotient.Secret) :
    ∀ (L : List (Fin 32)) (node : PcsQuotient.Bytes32),
      L.foldl (fun nd i ↦ if (secretOf w).directions i then Completeness.pair ((secretOf w).siblings i) nd
          else Completeness.pair nd ((secretOf w).siblings i)) (fun j ↦ node[j]) =
        fun j ↦ (L.foldl (fun nd i ↦ if w.directions[i] then PcsQuotient.pair w.siblings[i] nd
          else PcsQuotient.pair nd w.siblings[i]) node)[j]
  | [], _ => rfl
  | i :: L, node => by
    simp only [List.foldl_cons]
    rw [← foldl_root w L]
    congr 1
    have hs : (secretOf w).siblings i = fun j ↦ w.siblings[i][j] := rfl
    have hd : (secretOf w).directions i = w.directions[i] := rfl
    rw [hs, hd]
    split_ifs <;> rw [pair_secretOf]

/-- **The statement of a witness, read as Completeness's**, is the Statement's. -/
theorem secretOf_statement (w : PcsQuotient.Secret) :
    (secretOf w).statement = ⟨fun i ↦ w.statement.y[i], fun i ↦ w.statement.root[i]⟩ := by
  have hx : (secretOf w).x = fun i ↦ w.x[i] := rfl
  unfold Completeness.Secret.statement Completeness.Secret.root Completeness.Secret.leaf
  rw [hx, show (fun _ : Fin 32 ↦ Completeness.yPad) = fun i : Fin 32 ↦
      (Vector.replicate 32 PcsQuotient.yPad)[i] from replicate_fn _,
    show (fun _ : Fin 32 ↦ Completeness.leafPad) = fun i : Fin 32 ↦
      (Vector.replicate 32 PcsQuotient.leafPad)[i] from replicate_fn _,
    pair_secretOf, pair_secretOf]
  show _ = (⟨fun i ↦ (PcsQuotient.pair w.x (Vector.replicate 32 PcsQuotient.yPad))[i],
    fun i ↦ ((List.finRange PcsQuotient.depth).foldl _ (PcsQuotient.pair w.x
      (Vector.replicate 32 PcsQuotient.leafPad)))[i]⟩ : Completeness.Statement)
  rw [foldl_root]
  rfl

/-! ## The halves -/

theorem ofU64_ofNat (n : ℕ) : Primitives.F64.ofU64 (UInt64.ofNat n) = K.ofBits n := rfl

theorem ofBits_mod (n : ℕ) : K.ofBits (n % 2 ^ 64) = K.ofBits n := by
  unfold K.ofBits
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_mod_of_dvd]

/-- **A half of the statement, transcribed twice.** -/
theorem half_eq_stmtHalf (b : Fin 32 → UInt8) (h : Fin 2) :
    half Primitives.F192.G Primitives.F192.Y b h = Compose.Reduce.stmtHalf b h := by
  rw [half_G_Y]
  unfold rustHalf Compose.Reduce.stmtHalf Primitives.F192.new
  rw [ofU64_ofNat, ofU64_ofNat, ofBits_mod]
  rfl

theorem yOf_append (a b : PcsQuotient.Bytes32) : Compose.Reduce.yOf (a ++ b) = fun i ↦ a[i] := by
  funext i
  show (a ++ b)[(i : ℕ)]'(by omega) = a[i]
  exact Vector.getElem_append_left i.isLt

theorem rootOf_append (a b : PcsQuotient.Bytes32) : Compose.Reduce.rootOf (a ++ b) = fun i ↦ b[i] := by
  funext i
  show (a ++ b)[32 + (i : ℕ)]'(by omega) = b[i]
  rw [Vector.getElem_append_right (by omega) (by omega)]
  simp

/-- **The reduction's target is F1's**, on Completeness's statement words of the witness. -/
theorem target_stmt (w : PcsQuotient.Secret) (stmt : PcsQuotient.Statement)
    (hrel : PcsQuotient.Relation stmt w) (γ : E) :
    Completeness.deployedInstanceE.params.target
        (statementWords Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y
          (secretOf w).statement.root) γ =
      Compose.Reduce.target (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) γ := by
  have I := Completeness.deployedInstanceE
  rw [statementWords_eq]
  have ht := membership_target Completeness.deployedInstanceE.basis le24
    Completeness.deployedInstanceE.wiring (invSeq Completeness.deployedInstanceE.basis.β)
    Completeness.deployedInstanceE.c (invSeq_zero _)
    (fun d hd _ ↦ invSeq_sum Completeness.deployedInstanceE.basis.β
      Completeness.deployedInstanceE.basis.zero d hd)
    (halves Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y (secretOf w).statement.root) γ
  refine ht.trans ?_
  rw [secretOf_statement, hrel]
  simp only [halves, Compose.Reduce.target, Compose.Reduce.stmtHalves, yOf_append, rootOf_append,
    half_eq_stmtHalf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  ring

end E2ECompleteness

/-- info: 'E2ECompleteness.target_stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.target_stmt
