/-! The specifications over the integers: the quotient rounded toward negative infinity, the floor
of the mean, and the bound of a value by an interval. -/

namespace Examples.Floor

/-- The quotient of `a` by `b` rounded toward negative infinity. -/
def expectedDiv (a b : Int64) : Int := Int.fdiv a.toInt b.toInt

/-- The floor of the mean of `a` and `b`. -/
def expectedAverage (a b : Int64) : Int := Int.fdiv (a.toInt + b.toInt) 2

/-- `x` bounded below by `lo` and above by `hi`, on the integers. -/
def expectedClamp (x lo hi : Int64) : Int := max lo.toInt (min x.toInt hi.toInt)

end Examples.Floor
