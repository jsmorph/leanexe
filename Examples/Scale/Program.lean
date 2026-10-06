namespace Examples.Scale

/-- `a * b / c + 1` in wrapping 64-bit arithmetic.  Lean's division by zero
returns 0, so `scale a b 0 = 1`, while WASM's `i64.div_u` traps on zero. -/
def scale (a b c : UInt64) : UInt64 :=
  a * b / c + 1

end Examples.Scale
