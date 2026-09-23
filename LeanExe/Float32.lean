import Init.Data.SInt.Float32

namespace LeanExe.Float32

def addBits (left right : UInt32) : UInt32 :=
  (_root_.Float32.ofBits left + _root_.Float32.ofBits right).toBits

def subBits (left right : UInt32) : UInt32 :=
  (_root_.Float32.ofBits left - _root_.Float32.ofBits right).toBits

def mulBits (left right : UInt32) : UInt32 :=
  (_root_.Float32.ofBits left * _root_.Float32.ofBits right).toBits

def divBits (left right : UInt32) : UInt32 :=
  (_root_.Float32.ofBits left / _root_.Float32.ofBits right).toBits

def sqrtBits (value : UInt32) : UInt32 :=
  (_root_.Float32.ofBits value).sqrt.toBits

def toFloat64Bits (value : UInt32) : UInt64 :=
  (_root_.Float32.ofBits value).toFloat.toBits

def ofFloat64Bits (value : UInt64) : UInt32 :=
  (Float.ofBits value).toFloat32.toBits

def ofInt32Bits (value : UInt32) : UInt32 :=
  (Int32.ofUInt32 value).toFloat32.toBits

def toInt32Bits (value : UInt32) : UInt32 :=
  (_root_.Float32.ofBits value).toInt32.toUInt32

def nearestBits (value : UInt32) : UInt32 :=
  let exponent := value.toNat / 2 ^ 23 % 256
  let fraction := value.toNat % 2 ^ 23
  if exponent == 255 then
    if fraction == 0 then value else 0x7FC00000
  else
    let magnitude := if exponent == 0 then fraction else (2 ^ 23 + fraction) * 2 ^ (exponent - 1)
    let unit := 2 ^ 149
    let whole := magnitude / unit
    let remainder := magnitude % unit
    let rounded : Nat :=
      if remainder < unit / 2 then whole
      else if unit / 2 < remainder then whole + 1
      else if whole % 2 == 0 then whole else whole + 1
    if rounded == 0 then
      if value < 0x80000000 then 0 else 0x80000000
    else
      (_root_.Float32.Model.ofInt
        (if value < 0x80000000 then (rounded : Int) else -(rounded : Int))).toBits

end LeanExe.Float32
