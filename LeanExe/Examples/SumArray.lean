namespace LeanExe.Examples.SumArray

/-- The sum of the elements modulo 2^64. -/
def sumArray (xs : Array UInt64) : UInt64 := xs.foldl (· + ·) 0

end LeanExe.Examples.SumArray
