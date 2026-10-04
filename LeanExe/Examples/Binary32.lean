namespace LeanExe.Examples.Binary32

/-- `a * x + y` in binary32, with two roundings. -/
def axpy32 (a x y : Float32) : Float32 := a * x + y

/-- The length of the vector `(x, y)` in binary32, with four roundings. -/
def hypot32 (x y : Float32) : Float32 := (x * x + y * y).sqrt

/-- `(a - b) / c` in binary32. -/
def ratio32 (a b c : Float32) : Float32 := (a - b) / c

end LeanExe.Examples.Binary32
