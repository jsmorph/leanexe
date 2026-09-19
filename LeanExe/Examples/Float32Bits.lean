import LeanExe.Float32

namespace LeanExe.Examples.Float32Bits

def addBits (left right : UInt32) : UInt32 := LeanExe.Float32.addBits left right
def subBits (left right : UInt32) : UInt32 := LeanExe.Float32.subBits left right
def mulBits (left right : UInt32) : UInt32 := LeanExe.Float32.mulBits left right
def divBits (left right : UInt32) : UInt32 := LeanExe.Float32.divBits left right
def sqrtBits (value : UInt32) : UInt32 := LeanExe.Float32.sqrtBits value
def toFloat64Bits (value : UInt32) : UInt64 := LeanExe.Float32.toFloat64Bits value
def ofFloat64Bits (value : UInt64) : UInt32 := LeanExe.Float32.ofFloat64Bits value

def mulThenAddBits (left right addend : UInt32) : UInt32 :=
  LeanExe.Float32.addBits (LeanExe.Float32.mulBits left right) addend

def sqrtDivBits (left right : UInt32) : UInt32 :=
  LeanExe.Float32.sqrtBits (LeanExe.Float32.divBits left right)

def roundTripBits (value : UInt32) : UInt32 :=
  LeanExe.Float32.ofFloat64Bits (LeanExe.Float32.toFloat64Bits value)

def shiftBits (values : Array UInt32) (shift : UInt32) : Array UInt32 :=
  values.map fun value => LeanExe.Float32.addBits value shift

end LeanExe.Examples.Float32Bits
