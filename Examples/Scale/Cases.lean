import Examples.Scale.Program
import TestSupport.Host

/-! The module cases of `scale`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Scale

open TestSupport.Host

/-- The inputs of the cases, which the verified compiler's cases also use. -/
def samples : List (UInt64 × UInt64 × UInt64) :=
  let chosen : List (UInt64 × UInt64 × UInt64) :=
    [(6, 7, 5), (6, 7, 0), (maxU, 2, 3), (0, 0, 1), (1, 1, 1), (4294967296, 4294967296, 1),
     (9223372036854775808, 2, 1), (maxU, maxU, maxU), (5, 0, 0)]
  let random := (List.range 40).map fun i => (rw (3 * i), rw (3 * i + 1), if i % 5 = 0 then 0 else rw (3 * i + 2) % 1000)
  chosen ++ random

def scaleCases : IO Unit := do
  for (a, b, c) in samples do
    line "scale" "scale" "i64" [u a, u b, u c] (toString (Examples.Scale.scale a b c))

def cases : IO Unit := do
  scaleCases

end Examples.Scale
