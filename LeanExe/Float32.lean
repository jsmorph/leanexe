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

end LeanExe.Float32
