import Verified.Reflect.Command

/-! The third program of the verified compiler: `let` bindings, including one inside the operand
of a division, whose locals sit above the division's scratch locals. -/

namespace Verified.Examples.Lets

def scramble (a b : UInt64) : UInt64 :=
  let x := a ^^^ (b <<< 13)
  let y := x * 0x9e3779b97f4a7c15
  let z := y ^^^ (y >>> 29)
  (let w := b ||| 1; z / (w * w)) + z % (a + 7)

verified_compile compiled := [scramble]

end Verified.Examples.Lets
