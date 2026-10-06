namespace LeanExe.ProofKit.Float64

def addBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left + Float.ofBits right).toBits

def subBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left - Float.ofBits right).toBits

def mulBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left * Float.ofBits right).toBits

def divBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left / Float.ofBits right).toBits

def sqrtBits (value : UInt64) : UInt64 :=
  (Float.ofBits value).sqrt.toBits

end LeanExe.ProofKit.Float64
