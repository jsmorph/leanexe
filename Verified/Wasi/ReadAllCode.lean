import Verified.Wasi.ReadCode

/-! The code of `readAll limit`, which the compiler places in the calling function after the code
of `limit`.  It uses six i64 locals from `base`: the limit at `base`, the errno at `base + 1`, the
buffer's root at `base + 2`, the bytes held at `base + 3`, the address of a read and then its count
at `base + 4`, and the read capacity 4,096 at `base + 5`.  It allocates one buffer of
`limit + 4,096` bytes and reads into its unused tail until a read returns an errno or no bytes, or
until more than `limit` bytes are held, and it leaves the errno, the root, and the length on the
stack.  A limit of `2 ^ 32 - 4096` or more gives errno 61 and the empty buffer `(0, 0)`. -/

namespace Verified.Wasi

open Wasm

/-- The address of a read: the root plus the bytes held. -/
def readAllAddressCode (base : Nat) : Program :=
  [.localGet (base + 2), .localGet (base + 3), .addI64, .localSet (base + 4)]

/-- The tests after a read: an errno or a read of no bytes ends the loop, and otherwise the count
extends the bytes held and the loop ends when they exceed the limit. -/
def readAllTestCode (base : Nat) : Program :=
  [.extendUI32, .localSet (base + 1),
   .localGet (base + 1), .eqzI64, .eqz, .br_if 1,
   .const 8, .load32 0, .extendUI32, .localSet (base + 4),
   .localGet (base + 4), .eqzI64, .br_if 1,
   .localGet (base + 3), .localGet (base + 4), .addI64, .localSet (base + 3),
   .localGet base, .localGet (base + 3), .ltUI64, .br_if 1,
   .br 0]

/-- One read into the buffer's tail, followed by the tests that end the loop. -/
def readAllBody (base : Nat) : Program :=
  readAllAddressCode base ++ readCallCode (base + 4) (base + 5) ++ readAllTestCode base

def readAllOverflowCode (base : Nat) : Program :=
  [.constI64 61, .localSet (base + 1), .constI64 0, .localSet (base + 2),
   .constI64 0, .localSet (base + 3)]

def readAllLoopCode (base : Nat) : Program :=
  [.block 0 0 [.loop 0 0 (readAllBody base) [] []] [] []]

def readAllValidCodeWith (calls : List LeanExe.Wasi.Call) (base : Nat) : Program :=
  [.localGet base, .constI64 4096, .addI64, .call (3 + calls.length), .localSet (base + 2),
   .constI64 0, .localSet (base + 1), .constI64 0, .localSet (base + 3),
   .constI64 4096, .localSet (base + 5)] ++ readAllLoopCode base

def readAllValidCode (base : Nat) : Program := readAllValidCodeWith [] base

/-- The code after the limit's: it takes the limit from the stack and leaves the errno, the root,
and the length there. -/
def readAllCodeWith (calls : List LeanExe.Wasi.Call) (base : Nat) : Program :=
  [.localSet base, .localGet base, .constI64 4294963200, .geUI64,
   .iff 0 0 (readAllOverflowCode base) (readAllValidCodeWith calls base) [] [],
   .localGet (base + 1), .localGet (base + 2), .localGet (base + 3)]

def readAllCode (base : Nat) : Program := readAllCodeWith [] base

end Verified.Wasi
