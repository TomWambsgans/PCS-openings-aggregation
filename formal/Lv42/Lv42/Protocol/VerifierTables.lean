/-
  Lv42.Protocol.VerifierTables

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Spec/Verifier.lean (its tables, `verifier.py:730-879`). MIT OR
  Apache-2.0; see NOTICE.md.

  The verifier's six instruction tables, as far as the arithmetization reads them: their opcodes
  and column names, and the padding row (zero but for the `BLAKE2S` value limbs, which hold
  Flock's padding instance).
-/

module

public import Lv42.Protocol.Blake2sHash

/-!
# The verifier's tables

`LeanVM.Spec.Verifier` of leanerVM `f0393df4` transcribes leanVM's BLAKE2s-era Python verifier
(`python-verifier/verifier.py` at leanVM `3f7dc2196e43ca60034c5803eb307c050b4f91d9`, which is
leanVM `42422001`'s: `python-verifier` is identical at both). Its verifier is not ported. The
leanISA instance (`Lv42.Protocol.LeanIsa`) reads one thing of it, the padding row of each
opcode table (`padRowK`), which is a function of the table's opcode and column names; this
module keeps those, unchanged, and drops the tables' flushes and constraints (the `Form`s the
old verifier evaluates), which the instance takes from Clean's components instead.
-/

namespace Lv42.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-! ### Opcodes (`verifier.py:846-851`) -/

/-- Opcode `XOR`. -/
def opXor : ℕ := 0
/-- Opcode `MUL`. -/
def opMul : ℕ := 1
/-- Opcode `SET`. -/
def opSet : ℕ := 2
/-- Opcode `DEREF`. -/
def opDeref : ℕ := 3
/-- Opcode `JUMP`. -/
def opJump : ℕ := 4
/-- Opcode `BLAKE2S`. -/
def opBlake2s : ℕ := 5

/-! ### The instruction tables (`verifier.py:730-879`) -/

/-- `_cols(columns, name)`: the index of a column by name. -/
def colIdx (columns : List String) (name : String) : ℕ := columns.idxOf name

/-- `ARITH_COLUMNS`. -/
def arithColumns : List String :=
  ["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a",
    "cnt_b", "cnt_c", "cnt_bc"]

/-- `SET_COLUMNS`. -/
def setColumns : List String := ["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"]

/-- `DEREF_COLUMNS`. -/
def derefColumns : List String :=
  ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr",
    "cnt_target", "cnt_local", "cnt_bc"]

/-- `JUMP_COLUMNS`. -/
def jumpColumns : List String :=
  ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc",
    "w", "b"]

/-- `BLAKE2S_COLUMNS`. -/
def blake2sColumns : List String :=
  ["pc", "fp", "o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md",
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi",
    "out0_lo", "out0_hi", "out1_lo", "out1_hi", "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "md_lo",
    "md_hi",
    "cnt_m0", "cnt_m1", "cnt_m2", "cnt_m3", "cnt_cv0", "cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md",
    "cnt_bc"]

/-- One instruction's table, as the padding row reads it: its name, its opcode (also its index in
`TABLES`) and its column names (`verifier.py:730-750`; the Python's flushes and constraints are
not kept). -/
structure Table where
  /-- The table's name. -/
  name : String
  /-- Its opcode, also its index in `TABLES`. -/
  opcode : ℕ
  /-- Its column names. -/
  columns : List String
  deriving Inhabited

/-- `Table.width`. -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `TABLES`, in opcode order (`verifier.py:857-864`). -/
def tables : List Table :=
  [⟨"xor", opXor, arithColumns⟩, ⟨"mul", opMul, arithColumns⟩, ⟨"set", opSet, setColumns⟩,
    ⟨"deref", opDeref, derefColumns⟩, ⟨"jump", opJump, jumpColumns⟩,
    ⟨"blake2s", opBlake2s, blake2sColumns⟩]

/-- `BLAKE2S_SLOTS`: the `BLAKE2S` limb each Flock slot carries; slots 8 and 9 carry none
(`verifier.py:868-871`). -/
def blake2sSlots : List (Option String) :=
  [some "cv0_lo", some "cv0_hi", some "cv1_lo", some "cv1_hi", some "out0_lo", some "out0_hi",
    some "out1_lo", some "out1_hi", none, none,
    some "m0_lo", some "m0_hi", some "m1_lo", some "m1_hi", some "m2_lo", some "m2_hi",
    some "m3_lo", some "m3_hi", some "md_lo", some "md_hi"]

/-- `PADDING_INSTANCE`: Flock's padding instance, the compression of BLAKE2s-256 of 64 zero
bytes, in `BLAKE2S_SLOTS` order: the parameterized IV, the digest, a zero message, then the
one-block final metadata, counter 64 and the last-block flag (`verifier.py:875-876`). -/
def paddingInstance : List ℕ :=
  let word := fun (v : Vector UInt32 8) (k : ℕ) ↦
    (v.getD (2 * k) 0).toNat ||| (v.getD (2 * k + 1) 0).toNat <<< 32
  let digest := Blake2sHash.blake2sBytes (List.replicate 64 0)
  (List.range 4).map (word Blake2sHash.paramIv) ++ (List.range 4).map (word digest) ++
    List.replicate 10 0 ++ [64, 0xFFFFFFFF]

/-- `Table.padding`: the row a padding row holds, zero but for `BLAKE2S`'s value limbs, which are
`q_flock`'s slots and so hold its padding instance (`verifier.py:752-756`). -/
def Table.padding (t : Table) : List E :=
  let slots := if t.opcode = opBlake2s then blake2sSlots else []
  t.columns.map fun name ↦
    if some name ∈ slots then eOfNat (paddingInstance.getD (slots.idxOf (some name)) 0) else 0

end
end Lv42.Protocol.Verifier
