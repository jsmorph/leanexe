import LeanExe.Dialect.Loop

/-! The minimal standard generator of Park and Miller: each step replaces the state `x` with
`16807 * x % 2147483647`, where `2147483647 = 2^31 - 1`.  The state lies in `[1, 2^31 - 2]`, so the
product is below `2^46` and the program computes it with word arithmetic without overflow.
`advance n x` applies `step` `n` times, and `seed s` gives the state for the seed `s` by the rule of
the C++ standard's `linear_congruential_engine`, which `std::minstd_rand0` instantiates with these
parameters: `s % (2^31 - 1)`, or 1 when that is 0. -/

namespace Examples.ParkMiller

/-- One step of the generator: `16807 * x % 2147483647`. -/
def step (x : UInt64) : UInt64 := 16807 * x % 2147483647

/-- The state after `n` steps from `x`. -/
def advance (n x : UInt64) : UInt64 := LeanExe.loop n x fun _ s => step s

/-- The state for the seed `s`: `s % 2147483647`, or 1 when that is 0. -/
def seed (s : UInt64) : UInt64 :=
  let r := s % 2147483647
  if r = 0 then 1 else r

end Examples.ParkMiller
