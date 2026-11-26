module

public import LeanExe.Base

@[expose] public section

/-!
`natOfBytes`, in a module of its own so that `LeanExe.FileNat` can call it in its elaborators,
which run at the meta phase, and state theorems about it as ordinary code.
-/

namespace LeanExe.FileNat

/-- The number whose base-256 digits, the lowest first, are the bytes `l`. -/
def natOfBytes : List UInt8 → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * natOfBytes l

end LeanExe.FileNat
