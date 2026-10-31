import Examples.Updates.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `exampleUpdates`. -/

namespace Examples.Updates

open TestSupport.Host

/-- The arguments `(xs, a)` of `pushTwo` and `pushCopy`: each array with four values that depend on
its length. -/
def pushArgs : List (List UInt64 × UInt64) :=
  wordArrays.flatMap fun xs => ([0, 1, 2, 5] : List Nat).map fun i => (xs, rw (xs.length + i))

/-- The arguments `(xs, i, j, a)` of `setTwice` and `insertErase`: positions inside and past the
end of each array. -/
def updateArgs : List (List UInt64 × UInt64 × UInt64 × UInt64) :=
  wordArrays.flatMap fun xs => ([0, 1, 2, 5] : List UInt64).flatMap fun i =>
    ([0, 1, 3, 7] : List UInt64).map fun j => (xs, i, j, rw (xs.length + i.toNat))

end Examples.Updates
