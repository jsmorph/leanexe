namespace LeanExe.Examples.Piecewise

/-- A piecewise function of `x` with the bounds `lo` and `hi`. -/
def piecewise (x lo hi : Float) : Float :=
  if x == lo then 0.0
  else if x < lo then -(lo - x) * 0.5
  else if hi ≤ x then (hi - x).abs + 1.5
  else max lo (min x hi)

end LeanExe.Examples.Piecewise
