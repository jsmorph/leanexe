import Examples.Lists.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `exampleLists`. -/

namespace Examples.Lists

open TestSupport.Host

/-- The lists of the cases of `listSum`. -/
def listArgs : List (List UInt64) :=
  let chosen : List (List UInt64) :=
    [[], [0], [maxU], [maxU, 1], [1, 2, 3], [maxU, maxU, maxU], (List.range 200).map rw]
  let random := (List.range 30).map fun i => (List.range (i % 13)).map fun k => rw (13 * i + k)
  chosen ++ random

/-- The counts of the cases of `listRange` and `sumRange`. -/
def rangeArgs : List UInt64 := [0, 1, 2, 3, 7, 64, 65, 300, 1000]

end Examples.Lists
