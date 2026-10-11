import LeanExe.Dialect.Loop

/-! Marsaglia's xorshift64 generator with the shifts 13, 7, and 17: each step replaces the state
`x` with `x ^^^ (x <<< 13)`, then with `x ^^^ (x >>> 7)`, and then with `x ^^^ (x <<< 17)`.
`advance n x` applies `step` `n` times. -/

namespace Examples.Xorshift

/-- One step of xorshift64: `x ^^^ (x <<< 13)`, then `x ^^^ (x >>> 7)`, then `x ^^^ (x <<< 17)`. -/
def step (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- The state after `n` steps from `x`. -/
def advance (n x : UInt64) : UInt64 := LeanExe.loop n x fun _ s => step s

end Examples.Xorshift
