import LeanExe.Float64

namespace LeanExe.Examples.Float64Bits

def addBits (left right : UInt64) : UInt64 :=
  LeanExe.Float64.addBits left right

def mulBits (left right : UInt64) : UInt64 :=
  LeanExe.Float64.mulBits left right

def mulThenAddBits (left right addend : UInt64) : UInt64 :=
  LeanExe.Float64.addBits (LeanExe.Float64.mulBits left right) addend

def addMulBits (addend left right : UInt64) : UInt64 :=
  LeanExe.Float64.addBits addend (LeanExe.Float64.mulBits left right)

end LeanExe.Examples.Float64Bits
