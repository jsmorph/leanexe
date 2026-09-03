namespace LeanExe.Float64

/-- Add two binary64 values represented by their `UInt64` bit patterns. -/
def addBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left + Float.ofBits right).toBits

/-- Multiply two binary64 values represented by their `UInt64` bit patterns. -/
def mulBits (left right : UInt64) : UInt64 :=
  (Float.ofBits left * Float.ofBits right).toBits

end LeanExe.Float64
