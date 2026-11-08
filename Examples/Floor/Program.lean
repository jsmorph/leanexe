/-!
Floor division and the floor of the mean on `Int64`.  `floorDiv` corrects Lean's truncating
quotient by one when the remainder is nonzero and the operands' signs differ, as Python's `//`
rounds.  `average` computes the floor of the mean without overflow as the conjunction of the
operands plus half their exclusive or, with the arithmetic shift (Warren, Hacker's Delight, 2nd
edition, section 2-5).
-/

namespace Examples.Floor

/-- The quotient of `a` by `b` rounded toward negative infinity: 0 for `b = 0`, as Lean's
`Int64.div` gives, and `minValue` for `minValue` by -1, whose quotient wraps. -/
def floorDiv (a b : Int64) : Int64 :=
  let q := a / b
  if a % b != 0 && decide (a < 0) != decide (b < 0) then q - 1 else q

/-- The floor of the mean of `a` and `b`. -/
def average (a b : Int64) : Int64 := (a &&& b) + ((a ^^^ b) >>> 1)

end Examples.Floor
