namespace LeanExe.Float64

/-- Add two binary64 values represented by their `UInt64` bit patterns. -/
def addBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left + Float.ofBits right).toBits

/-- Multiply two binary64 values represented by their `UInt64` bit patterns. -/
def mulBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left * Float.ofBits right).toBits

/-- Subtract two binary64 values represented by their raw words. -/
def subBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left - Float.ofBits right).toBits

/-- Divide two binary64 values represented by their raw words. -/
def divBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left / Float.ofBits right).toBits

/-- Binary64 square root over a raw input word. -/
def sqrtBits (value : UInt64) : UInt64 :=
  (Float.ofBits value).sqrt.toBits

end LeanExe.Float64
