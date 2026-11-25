module

public section

namespace LeanExe.ProofKit.Float64

@[expose] def addBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left + Float.ofBits right).toBits

@[expose] def subBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left - Float.ofBits right).toBits

@[expose] def mulBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left * Float.ofBits right).toBits

@[expose] def divBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left / Float.ofBits right).toBits

@[expose] def sqrtBits (value : UInt64) : UInt64 :=
  (Float.ofBits value).sqrt.toBits

end LeanExe.ProofKit.Float64
