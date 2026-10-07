import Verified.Reflect.Command

/-! The fifth program of the verified compiler: four functions, each of which may call the
functions before it, with a call as the argument of another call and a call that returns a
`Bool` as the test of an `if`. -/

namespace Verified.Examples.Calls

def sq (x : UInt64) : UInt64 := x * x

def sumSq (a b : UInt64) : UInt64 := sq a + sq b

def small (x : UInt64) : Bool := x < 100

def pick (a b c : UInt64) : UInt64 := if small a then sumSq (sumSq a b) c else sq (b - c)

verified_compile compiled := [sq, sumSq, small, pick]

end Verified.Examples.Calls
