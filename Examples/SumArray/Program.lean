namespace Examples.SumArray

/-- The sum of the elements modulo 2^64. -/
def sumArray (xs : Array UInt64) : UInt64 := xs.foldl (· + ·) 0

/-- The product of the elements modulo 2^64, from left to right, starting with 1. -/
def productArray (xs : Array UInt64) : UInt64 := xs.foldl (· * ·) 1

/-- The bitwise exclusive or of the elements, starting with 0. -/
def xorArray (xs : Array UInt64) : UInt64 := xs.foldl (· ^^^ ·) 0

end Examples.SumArray
