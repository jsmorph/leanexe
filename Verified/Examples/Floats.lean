import Verified.Reflect.Command

/-! The thirteenth program of the verified compiler: floats.  The programs use the arithmetic
operations, the square root, the absolute value, negation, comparisons as conditions and as
`Bool` values, `min` and `max`, and literals, and they pass floats as parameters, results,
components of pairs, and a loop's state.  The reflector rejects `=` and `≠` on floats, which
compare bit patterns, and accepts `==` and `!=`, which compare values as IEEE 754 does. -/

namespace Verified.Examples.Floats

/-- A piecewise function of `x` with pieces below `lo`, between `lo` and `hi`, and above `hi`. -/
def piecewise (x lo hi : Float) : Float :=
  if x < lo then -(lo - x) * 0.5
  else if x ≤ hi then (x - lo).abs + min x hi
  else max (x * 2) hi - 1.5

def hypot (x y s : Float) : Float := (x * x + y * y).sqrt / s

def inBand (x lo hi : Float) : Bool := (lo ≤ x && x < hi) || (x == hi && lo != hi)

def clamp (x lo hi : Float) : Float := if x < lo then lo else if x > hi then hi else x

def negate (x : Float) : Float := -x

def least (a b : Float) : Float := min a b

def most (a b : Float) : Float := max a b

def minSum (a b c : Float) : Float := min (a + b) (c * -2.0)

/-- The harmonic number of order `n`, with the term's denominator in the loop's state. -/
def harmonic (n : UInt64) : Float :=
  (LeanExe.loop n ((0.0 : Float), (1.0 : Float)) fun _ s => (s.1 + 1 / s.2, s.2 + 1)).1

/-- Parameters of each kind: a word, a float, an array, and a pair of a float and a word. -/
def mixed (n : UInt64) (x : Float) (xs : Array UInt64) (p : Float × UInt64) : Float × UInt64 :=
  (x * p.1 - 0.25, n + xs.size.toUInt64 + p.2)

def combined (x y : Float) : Float := hypot x y 2.0 + piecewise x 0.0 1.0

verified_compile compiled := [piecewise, hypot, inBand, clamp, negate, least, most, minSum,
  harmonic, mixed, combined]

end Verified.Examples.Floats
