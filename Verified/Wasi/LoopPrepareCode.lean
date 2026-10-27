import Verified.Wasi.Code

namespace Verified.Wasi

open Wasm

def loopPrepareCode (h base : Nat) (slots : List Slot) (pool : Bytes.LiteralPool)
    (count : Expr S context .word) (initial : Expr S context type) (live : Nat → Bool) : Program :=
  Relocation.program (count.code (pool := pool) h slots base (fun i => live i || initial.uses i)) ++
    [.localSet base] ++
    Relocation.program (initial.code (pool := pool) h slots (base + 1) live ++
      coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)) ++
    storeCode h (base + 2) type.types ++ [.constI64 0, .localSet (base + 1)]

end Verified.Wasi
