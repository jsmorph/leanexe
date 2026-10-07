import Verified.Reflect.Command

/-! The fourth program of the verified compiler: comparisons, `Bool` operations, `Bool`-valued
`let` bindings, `if` on a `Bool` and on a comparison, and functions that take or return a
`Bool`. -/

namespace Verified.Examples.Select

/-- The middle of three words. -/
def median (a b c : UInt64) : UInt64 :=
  let ab : Bool := a ≤ b
  let bc : Bool := b ≤ c
  let ac : Bool := a ≤ c
  if (ab && bc) || (!ab && !bc) then b
  else if (ac && !bc) || (!ac && bc) then c
  else a

def inBand (x lo hi : UInt64) : Bool := (lo ≤ x && x < hi) || (x == hi && lo != hi)

def clamp (x lo hi : UInt64) : UInt64 := if x < lo then lo else if x > hi then hi else x

def pickNe (a b : UInt64) (flag : Bool) : UInt64 := if a ≠ b then (if flag then a else b) else 0

verified_compile compiled := [median, inBand, clamp, pickNe]

end Verified.Examples.Select
