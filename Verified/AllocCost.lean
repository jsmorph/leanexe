module

public import LeanExe.Base

@[expose] public section

namespace Verified

/-- The growth of `top` for an allocation of `bytes` payload bytes that no free block supplies. -/
def allocCost (bytes : Nat) : Nat := 48 + bytes

end Verified
