import LeanExe.Float64

namespace LeanExe.Lib.Transcendental

def expTaylor6Polynomial (x : UInt64) : UInt64 :=
  let a := Float64.addBits (Float64.mulBits 0x3F56C16C16C16C17 x) 0x3F81111111111111
  let b := Float64.addBits (Float64.mulBits a x) 0x3FA5555555555555
  let c := Float64.addBits (Float64.mulBits b x) 0x3FC5555555555555
  let d := Float64.addBits (Float64.mulBits c x) 0x3FE0000000000000
  let e := Float64.addBits (Float64.mulBits d x) 0x3FF0000000000000
  Float64.addBits (Float64.mulBits e x) 0x3FF0000000000000

def expTaylor6 (bits : UInt64) : Option UInt64 :=
  if bits == 0 || (bits >= 0x8000000000000000 && bits <= 0xBFF0000000000000) then
    some (expTaylor6Polynomial bits)
  else none

end LeanExe.Lib.Transcendental
