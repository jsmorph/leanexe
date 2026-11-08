/-!
Conversions between `Int64` and the floats.  `toDouble` and `toSingle` round a signed integer to
the nearest binary64 or binary32 value, ties to even, as `Int64.toFloat` and `Int64.toFloat32` do.
`ofDouble` and `ofSingle` truncate a float toward zero and saturate at the bounds of `Int64`, with 0
for NaN, as `Float.toInt64` and `Float32.toInt64` do.  `scale` applies a binary64 gain to a signed
integer and truncates the product back to `Int64`.
-/

namespace Examples.Convert

def toDouble (a : Int64) : Float := a.toFloat

def toSingle (a : Int64) : Float32 := a.toFloat32

def ofDouble (x : Float) : Int64 := x.toInt64

def ofSingle (x : Float32) : Int64 := x.toInt64

/-- `a` times the gain `k`, truncated toward zero and saturated. -/
def scale (a : Int64) (k : Float) : Int64 := (a.toFloat * k).toInt64

end Examples.Convert
