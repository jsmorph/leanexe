import LeanExe.Dialect.Loop

/-! A linear congruential generator modulo `2^64`: each step replaces the state `x` with
`a * x + c`, with arithmetic that wraps modulo `2^64`.  `step` uses the multiplier
`6364136223846793005` of Knuth's *The Art of Computer Programming*, Volume 2, Section 3.3.4, and the
increment `1442695040888963407`, the default increment of O'Neill's PCG generators.  `advance n x`
applies `step` `n` times. -/

namespace Examples.Lcg

/-- `a * x + c`, modulo `2^64`. -/
def affine (a c x : UInt64) : UInt64 := a * x + c

/-- One step of the generator: `6364136223846793005 * x + 1442695040888963407`, modulo `2^64`. -/
def step (x : UInt64) : UInt64 := affine 6364136223846793005 1442695040888963407 x

/-- The state after `n` steps from `x`. -/
def advance (n x : UInt64) : UInt64 := LeanExe.loop n x fun _ s => step s

end Examples.Lcg
