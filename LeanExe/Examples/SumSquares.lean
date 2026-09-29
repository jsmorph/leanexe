namespace LeanExe.Examples.SumSquares

/-- The sum of the squares of the elements, accumulated from the left in binary64. -/
def sumSquares (xs : FloatArray) : Float := xs.foldl (fun acc x => acc + x * x) 0.0

end LeanExe.Examples.SumSquares
