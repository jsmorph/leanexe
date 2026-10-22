import Library.Numerics.Bounds.Program

namespace Library.Numerics.Limiters.Minmod

/-- The smaller of two words of the same sign in magnitude, or 0. -/
abbrev minmod (a b : Float) : Float :=
  if (a.toBits < 0x8000000000000000) == (b.toBits < 0x8000000000000000) then
    if Library.Numerics.Bounds.absBits a.toBits ≤ Library.Numerics.Bounds.absBits b.toBits then a else b
  else 0

end Library.Numerics.Limiters.Minmod
