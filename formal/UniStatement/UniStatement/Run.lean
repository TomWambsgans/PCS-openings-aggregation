-- Part of this repository. Transcribed from `crates/leanvm_univariate/src/contract.rs` (`rust_verifier`, `NAME`,
-- `calldata`) and `crates/leanvm_flock_gas/src/shapes.rs` (the measured shapes, `PROGRAM_IV`). MIT OR
-- Apache-2.0; see NOTICE.md.
module

public import UniStatement.Verifier

/-!
# A run of the verifier on calldata, and the setup constants

**The calldata** (`contract.rs`): the selector, the public input's 32 bytes (four 64-bit words, each
big-endian, word `k` the public word `k`), then the **stream** (`C1`'s root, Flock's messages, `C2`'s root,
the values at `t`, `ρ`'s and the batch's messages). The contract is built for one shape and one program,
whose 32-byte IV the transcript's seed takes.

**The run** (`runWith`, `rust_verifier`): the seed, `reduceWith`, then `finish`. **The verdict**
(`Outcome.accepts`): no stream error and every value the verifier collected is zero. Then the openings
(`Opening.lean`) check the claims it hands `PCS_OPEN`.

**The setup constants as data**: the measured shapes (`workloads`, leanVM's own `gas-dump` runs of the
aggregation guest at 32 to 2,000 signatures; `reference` is 1,000), the guest's bytecode (`2^23` words, so
`2^19` instructions), its IV (`programIv`). The stacks' layouts and the heap's are functions of the shape
(`layouts`, `Shape.heap`), as in the Rust.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol

/-- The public input's four words (`rust_verifier`): the 64-bit big-endian words of its 32 bytes, in `K`. -/
def publicWordsOf (publicInput : List UInt8) : List E :=
  (List.range 4).map fun k ↦ eK (beWordAt publicInput.toArray (8 * k))

/-- **A run's outcome**: the verifier's result (its claims, or the stream error) and the channel at the end
(the challenges drawn and the values collected). -/
structure Outcome where
  result : Except UniError Reduced
  chan : Chan

/-- **The verdict**: no stream error, and every value the verifier requires to be zero is. -/
def Outcome.accepts (o : Outcome) : Bool :=
  (match o.result with
    | .ok _ => true
    | .error _ => false) && o.chan.zeros.all (· == 0)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The verifier on calldata** over `F` (`rust_verifier`): the seed of the IV and the public input, the
walk, nothing of the stream left. -/
def runWith (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) : m Outcome := do
  let seed ← seedWith F iv publicInput
  let walk : ChanM m Reduced := do
    let r ← reduceWith F shape (publicWordsOf publicInput) blake2s mode
    finish (m := m)
    return r
  let (result, chan) ← (walk.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

end With

/-- The run over Keccak-f[1600]: the deployed contract's computation. -/
def run (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) : Outcome :=
  Id.run (runWith (m := Id) (fun s ↦ pure (keccakF1600 s)) shape iv publicInput stream blake2s mode)

/-! ### The setup constants -/

/-- `BYTECODE_LEN` (`shapes.rs`): the aggregation guest's stacked bytecode, `2^23` words. -/
def bytecodeLogLen : ℕ := 23

/-- `BUS_BITS`: a bus tuple has `2^4` slots. -/
def busBits : ℕ := 4

/-- `PROGRAM_IV` (`shapes.rs`): the aggregation guest's Fiat–Shamir IV (the BLAKE2s of the R1CS digest and
of the stacked bytecode). -/
def programIv : List UInt8 :=
  [0xb5, 0x41, 0x04, 0x5c, 0x98, 0x65, 0x5d, 0xb5, 0xa8, 0xaa, 0xc6, 0x1e, 0xfd, 0xb0, 0xad, 0xea, 0x1e, 0xaf,
    0xab, 0x5f, 0x51, 0x02, 0xa4, 0xe3, 0xf9, 0x3d, 0xf9, 0xc7, 0x53, 0x27, 0x1e, 0x1e]

/-- `Shape::of`: the measured shape's memory, the bytecode's instructions (`log₂ len − BUS_BITS`), the rows. -/
def shapeOf (logMemory : ℕ) (tableRows : List ℕ) : Shape := ⟨logMemory, bytecodeLogLen - busBits, tableRows⟩

/-- **The measured shapes** (`WORKLOADS`, `shapes.rs`): name, signatures, shape (rows in leanVM's order XOR,
MUL, SET, DEREF, JUMP, BLAKE2S). -/
def workloads : List (String × ℕ × Shape) :=
  [("xmss32", 32, shapeOf 16 [6060, 6490, 11768, 4703, 2699, 6489]),
    ("xmss128", 128, shapeOf 18 [23629, 25224, 32804, 17879, 10468, 25881]),
    ("xmss400", 400, shapeOf 20 [73426, 78352, 92398, 55231, 32463, 80825]),
    ("xmss1000", 1000, shapeOf 21 [183266, 195439, 223851, 137591, 80937, 202025]),
    ("xmss1290", 1290, shapeOf 22 [236343, 252019, 287373, 177391, 104394, 260605]),
    ("xmss2000", 2000, shapeOf 22 [366327, 390501, 442955, 274831, 161790, 404025])]

/-- The shape of a workload by name. -/
def shapeNamed (n : String) : Option Shape := (workloads.find? (·.1 == n)).map (·.2.2)

/-- **The reference shape** (`shapes::reference`): 1,000 signatures, 1,023,109 cycles. -/
def reference : Shape := shapeOf 21 [183266, 195439, 223851, 137591, 80937, 202025]

end UniStatement

end
