import Examples.Bools.Program
import Examples.Host

/-! The module cases of `bools`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Bools

open Examples.Host

def boolsCases : IO Unit := do
  let b (x : Bool) : String := s!"i64:{if x then 1 else 0}"
  let r (x : Bool) : String := toString (if x then 1 else 0)
  let ws : List UInt64 := [0, 1, 2, 3, 7, maxU - 1, maxU]
  let bs := [false, true]
  for x in ws do
    line "bools" "isPositive" "i64" [u x] (r (isPositive x))
    line "bools" "mark" "list:i64,i64" [u x] s!"{r (mark x).flag},{(mark x).value}"
    for y in ws do
      line "bools" "same" "i64" [u x, u y] (r (same x y))
      line "bools" "differ" "i64" [u x, u y] (r (differ x y))
  for a in bs do
    line "bools" "negate" "i64" [b a] (r (negate a))
    for c in bs do
      line "bools" "both" "i64" [b a, b c] (r (both a c))
      line "bools" "either" "i64" [b a, b c] (r (either a c))
      line "bools" "agree" "i64" [b a, b c] (r (agree a c))
    for x in [0, 5, maxU] do
      line "bools" "flagOf" "i64" [b a, u x] (r (flagOf ⟨a, x⟩))
      for y in [0, 9, maxU] do
        line "bools" "pick" "i64" [b a, u x, u y] (toString (pick a x y))
  let fs := specialFloats ++ [1.5, -2.25, 3.0]
  for x in fs do
    for y in fs do
      line "bools" "floatSame" "i64" [fl x, fl y] (r (floatSame x y))
  for lo in [-1.0, 0.0, nan] do
    for hi in [1.0, -0.0, inf] do
      for x in fs do
        line "bools" "inRange" "i64" [fl lo, fl hi, fl x] (r (inRange lo hi x))
  for n in [0, 1, 3, 10] do
    for k in [0, 2, 9, maxU] do
      line "bools" "anyEqual" "i64" [u n, u k] (r (anyEqual n k))

def cases : IO Unit := do
  boolsCases

end Examples.Bools
