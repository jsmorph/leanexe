import Verified.Reflect.Command

/-! The second program of the verified compiler: division, remainder, the bitwise operations, and
both shifts on 64-bit words, with Lean's results for a zero divisor and for shift amounts of 64
or more. -/

namespace Verified.Examples.Mix

def mix (a b c : UInt64) : UInt64 := ((a / b + a % c) ^^^ ((a &&& b) ||| (c <<< b))) - (a >>> c)

verified_compile compiled := [mix]

end Verified.Examples.Mix
