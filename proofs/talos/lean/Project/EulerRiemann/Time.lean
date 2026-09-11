import Project.Euler2DConservative.Model

namespace Project.EulerRiemann.Time
open Wasm.IEEE64 (add sub mul div)

def endTime : UInt64 := 0x3FE999999999999A

def smallNaturalBits (n : Nat) : UInt64 :=
  if n = 0 then 0
  else
    let exponent :=
      if n < 2 then 0 else if n < 4 then 1 else if n < 8 then 2
      else if n < 16 then 3 else if n < 32 then 4 else if n < 64 then 5
      else if n < 128 then 6 else if n < 256 then 7 else if n < 512 then 8 else 9
    ((1023 + exponent).toUInt64 <<< 52) |||
      ((n.toUInt64 <<< (52 - exponent).toUInt64) &&& 0x000FFFFFFFFFFFFF)

def spacing (n : Nat) : UInt64 := div 0x3FF0000000000000 (smallNaturalBits n)

def proposal (n : Nat) (time alpha : UInt64) : UInt64 :=
  min (div (mul 0x3FD999999999999A (spacing n)) alpha) (sub endTime time)

def validAdvance (time dt : UInt64) : Bool :=
  Project.Euler2DConservative.Model.positiveBits dt &&
    decide (time < add time dt) && decide (add time dt ≤ endTime)

end Project.EulerRiemann.Time
