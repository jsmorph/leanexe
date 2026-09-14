import Project.ProofKit.F64Order

namespace Project.ProofKit.F64Minmod
open Project.ProofKit.F64Order

def minmod (a b : UInt64) : UInt64 :=
  if decide (a < 0x8000000000000000) == decide (b < 0x8000000000000000) then
    if absBits a ≤ absBits b then a else b
  else 0

end Project.ProofKit.F64Minmod
