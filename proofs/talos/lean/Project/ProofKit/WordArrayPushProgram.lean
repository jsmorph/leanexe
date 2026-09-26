import Project.ProofKit.ArrayPush
import Project.ProofKit.FixedArrayAllocate
import Project.ProofKit.WordArrayCapacity

namespace Project.ProofKit.WordArrayPush
open Wasm

/-- The source pointer and appended word are already in slots `base` and
    `base + 6`. The fifteen scratch slots belong to this push operation. -/
def prepare (base : Nat) : Wasm.Program :=
  [.localGet base, .wrapI64, .load64 0, .localSet (base + 1),
    .localGet (base + 1), .constI64 1, .mulI64, .localSet (base + 2),
    .localGet (base + 1), .constI64 1, .addI64, .localSet (base + 3)]

def installLength (base : Nat) : Wasm.Program :=
  [.localGet (base + 14), .localSet (base + 4),
    .localGet (base + 4), .wrapI64, .localGet (base + 3), .store64 0]

def program (base : Nat) : Wasm.Program :=
  prepare base ++
    FixedArrayCapacity.localProgram (base + 3) 1 (base + 9) ++
    FixedArrayAllocate.program (base + 9) 1 ++ installLength base ++
    FixedArrayCopy.prefixProgram base (base + 4) (base + 2) (base + 5) ++
    UInt64Array.pushStoreProgram (base + 4) (base + 1) (base + 6) ++
    [.localGet (base + 4)]

end Project.ProofKit.WordArrayPush
