-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Graph
import Implementation.Arith

/-!
# The graph, interpreted on calldata

What the contract computes, node by node, as `crates/evm/src/codegen.rs` compiles each node: every
value is an EVM word (a natural number below `2^256`), and

* `const c` is `c`;
* `statement k` and `root k` are the high (`k` even) or low (`k` odd) 128 bits of the word of the
  arguments at `32 ⌊k/2⌋` (the statement) or `64 + 32 ⌊k/2⌋` (the commitments), the arguments being
  calldata after the 4-byte selector (`CALLDATALOAD`, `SHR 128` or `AND 2^128 - 1`);
* `input i` is the word at `128 + 24 i` shifted right by 64 bits: the scalar's 24 big-endian bytes;
* `add` is `XOR`, `mul` is `FIELD_MUL` (`mulE`), `frob` the Frobenius (`frobE`);
* `seed` is the hash of the label: the 16-byte name, the circuit's commitment (the index root, which
  the contract reads from storage), the 64 bytes of the statement;
* `hash st xs` is the hash of the words `st` and `xs`, each 32 bytes big-endian (`MSTORE`);
* `low a` is the low 192 bits of `a` (`AND 2^192 - 1`).

The hash `H` is a parameter: Keccak-256 (`KECCAK256`) as deployed, any function in the model.
`run` adds what the contract checks before its calls: the calldata's length and selector, and that
every node of `nonzero` is not zero; it gives the words written for the calls of `PCS_OPEN`
(`outputs`: a node's value, a constant, a word of calldata, or the stored root with its halves
reversed, as `PCS_OPEN` reads a root). The value of the call is not modelled (the contract
reverts on any).
-/

namespace Implementation

open Emitted

/-- The big-endian number of some bytes. -/
def beNat (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The `n` big-endian bytes of `w mod 256^n` (`MSTORE` for `n = 32`). -/
def beBytes (n w : Nat) : List UInt8 :=
  (List.range n).map fun k => ((w >>> (8 * (n - 1 - k))) % 256).toUInt8

/-- `CALLDATALOAD`: the big-endian word of the 32 bytes at `o`, zero past the end. -/
def cdWord (cd : List UInt8) (o : Nat) : Nat := beNat ((List.range 32).map fun k => cd.getD (o + k) 0)

/-- The little-endian number of some bytes. -/
def leNat (l : List UInt8) : Nat := beNat l.reverse

/-- The high (`k` even) or low (`k` odd) 128 bits of a word. -/
def half (w k : Nat) : Nat := if k % 2 = 0 then w >>> 128 else w % 2 ^ 128

/-- Bytes from the numbers of `Graph.lean`. -/
def bytesOf (l : List Nat) : List UInt8 := l.map Nat.toUInt8

/-- **One node's value**, from the values of the nodes before it. `idx` is the index root's 32
bytes, `cd` the calldata. -/
def step (H : List UInt8 → Vector UInt8 32) (idx cd : List UInt8) (vals : Array Nat) : Node → Nat
  | .const c => c
  | .statement k => half (cdWord cd (4 + 32 * (k / 2))) k
  | .root k => half (cdWord cd (4 + 64 + 32 * (k / 2))) k
  | .input i => cdWord cd (4 + 128 + 24 * i) >>> 64
  | .add a b => vals[a]! ^^^ vals[b]!
  | .mul a b => mulE vals[a]! vals[b]!
  | .frob a => frobE vals[a]!
  | .seed => beNat (H (bytesOf name ++ idx ++ (cd.drop 4).take 64)).toList
  | .hash st xs => beNat (H (beBytes 32 vals[st]! ++ xs.flatMap fun x => beBytes 32 vals[x]!)).toList
  | .low a => vals[a]! % B192

/-- The values of a list of nodes, in order. -/
def valuesOf (H : List UInt8 → Vector UInt8 32) (idx cd : List UInt8) (l : List Node) : Array Nat :=
  l.foldl (fun vals n => vals.push (step H idx cd vals n)) #[]

/-- **The values of the graph's nodes.** -/
def values (H : List UInt8 → Vector UInt8 32) (idx cd : List UInt8) : Array Nat :=
  valuesOf H idx cd nodes

/-- A root as `PCS_OPEN` reads it (`machine::root_word`): the little-endian numbers of its two
16-byte halves, the first high. -/
def rootWord (r : List UInt8) : Nat := leNat (r.take 16) * 2 ^ 128 + leNat (r.drop 16)

/-- An output word's value. -/
def wordOf (idx cd : List UInt8) (vals : Array Nat) : Word → Nat
  | .node i => vals[i]!
  | .const w => w
  | .calldata o => cdWord cd (4 + o)
  | .storedRoot => rootWord idx

/-- The calldata of a call of the verifier: `4 + 128 + 24 · inputs` bytes, the selector first. -/
def WellFormed (cd : List UInt8) : Prop :=
  cd.length = 4 + 128 + 24 * inputs ∧ cd.take 4 = bytesOf selector

instance (cd : List UInt8) : Decidable (WellFormed cd) := by unfold WellFormed; infer_instance

/-- **What the contract writes for its calls**, or `none` where it reverts before them: on
calldata of another length or selector, or when a node of `nonzero` is zero. -/
def run (H : List UInt8 → Vector UInt8 32) (idx : Vector UInt8 32) (cd : List UInt8) :
    Option (List Nat) :=
  if WellFormed cd then
    let vals := values H idx.toList cd
    if nonzero.all fun i => vals[i]! != 0 then some (outputs.map (wordOf idx.toList cd vals))
    else none
  else none

/-- A list cut into runs of the given lengths. -/
def splitRuns {α : Type} : List Nat → List α → List (List α)
  | [], _ => []
  | n :: ns, l => l.take n :: splitRuns ns (l.drop n)

/-- The inputs of the calls of `PCS_OPEN`: the words as `runs` cuts them, each 32 bytes big-endian. -/
def calls (words : List Nat) : List (List UInt8) :=
  (splitRuns runs words).map fun ws => ws.flatMap (beBytes 32)

/-- **The contract's verdict**: it returns the word 1 exactly when it reaches its calls and every
call attests (`attest`, `PCS_OPEN`). -/
def accepts (attest : List UInt8 → Bool) (H : List UInt8 → Vector UInt8 32) (idx : Vector UInt8 32)
    (cd : List UInt8) : Bool :=
  match run H idx cd with
  | some ws => (calls ws).all attest
  | none => false

end Implementation
