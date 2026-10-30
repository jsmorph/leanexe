import Examples.Bools.Program
import TestSupport.Host

/-! The module cases of `bools`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Bools

open TestSupport.Host

/-- The words of the cases of `isPositive` and `mark`, and of both arguments of `same` and
`differ`, which the verified compiler's cases also use. -/
def wordArgs : List UInt64 := [0, 1, 2, 3, 7, maxU - 1, maxU]

/-- The words of the cases of `flagOf` and the first word of those of `pick`. -/
def flagArgs : List UInt64 := [0, 5, maxU]

/-- The second word of the cases of `pick`. -/
def pickArgs : List UInt64 := [0, 9, maxU]

/-- The floats of the cases of `floatSame` and `inRange`. -/
def floatArgs : List Float := specialFloats ++ [1.5, -2.25, 3.0]

/-- The bounds `(lo, hi)` of the cases of `inRange`. -/
def rangeArgs : List (Float × Float) :=
  [-1.0, 0.0, nan].flatMap fun lo => [1.0, -0.0, inf].map fun hi => (lo, hi)

/-- The arguments `(n, k)` of the cases of `anyEqual`. -/
def anyEqualArgs : List (UInt64 × UInt64) :=
  [0, 1, 3, 10].flatMap fun n => [0, 2, 9, maxU].map fun k => (n, k)

def boolsCases : IO Unit := do
  let b (x : Bool) : String := s!"i64:{if x then 1 else 0}"
  let r (x : Bool) : String := toString (if x then 1 else 0)
  let bs := [false, true]
  for x in wordArgs do
    line "bools" "isPositive" "i64" [u x] (r (isPositive x))
    line "bools" "mark" "list:i64,i64" [u x] s!"{r (mark x).flag},{(mark x).value}"
    for y in wordArgs do
      line "bools" "same" "i64" [u x, u y] (r (same x y))
      line "bools" "differ" "i64" [u x, u y] (r (differ x y))
  for a in bs do
    line "bools" "negate" "i64" [b a] (r (negate a))
    for c in bs do
      line "bools" "both" "i64" [b a, b c] (r (both a c))
      line "bools" "either" "i64" [b a, b c] (r (either a c))
      line "bools" "agree" "i64" [b a, b c] (r (agree a c))
    for x in flagArgs do
      line "bools" "flagOf" "i64" [b a, u x] (r (flagOf ⟨a, x⟩))
      for y in pickArgs do
        line "bools" "pick" "i64" [b a, u x, u y] (toString (pick a x y))
  for x in floatArgs do
    for y in floatArgs do
      line "bools" "floatSame" "i64" [fl x, fl y] (r (floatSame x y))
  for (lo, hi) in rangeArgs do
    for x in floatArgs do
      line "bools" "inRange" "i64" [fl lo, fl hi, fl x] (r (inRange lo hi x))
  for (n, k) in anyEqualArgs do
    line "bools" "anyEqual" "i64" [u n, u k] (r (anyEqual n k))

def cases : IO Unit := do
  boolsCases

end Examples.Bools
