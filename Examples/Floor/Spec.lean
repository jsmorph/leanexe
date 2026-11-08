/-! The specifications over the integers: the quotient rounded toward negative infinity, and the
floor of the mean. -/

namespace Examples.Floor

/-- The quotient of `a` by `b` rounded toward negative infinity. -/
def expectedDiv (a b : Int64) : Int := Int.fdiv a.toInt b.toInt

/-- The floor of the mean of `a` and `b`. -/
def expectedAverage (a b : Int64) : Int := Int.fdiv (a.toInt + b.toInt) 2

end Examples.Floor
