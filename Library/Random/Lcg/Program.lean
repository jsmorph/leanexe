import LeanExe.Dialect.Loop

/-! A linear congruential generator modulo `2^64`: each step replaces the state `x` with
`a * x + c`, with arithmetic that wraps modulo `2^64`.  `step` uses the multiplier
`6364136223846793005` of Knuth's *The Art of Computer Programming*, Volume 2, Section 3.3.4, and the
increment `1442695040888963407`, the default increment of O'Neill's PCG generators.  `advance n x`
applies `step` `n` times, and `jump n x` computes the same state by one squaring of the affine map
per bit of `n`. -/

namespace Library.Random.Lcg

/-- `a * x + c`, modulo `2^64`. -/
def affine (a c x : UInt64) : UInt64 := a * x + c

/-- The multiplier, from Knuth's MMIX generator. -/
def multiplier : UInt64 := 6364136223846793005

/-- The increment, from O'Neill's PCG generators. -/
def increment : UInt64 := 1442695040888963407

/-- One step of the generator: `multiplier * x + increment`, modulo `2^64`. -/
def step (x : UInt64) : UInt64 := affine multiplier increment x

/-- The state after `n` steps from `x`. -/
def advance (n x : UInt64) : UInt64 := LeanExe.loop n x fun _ s => step s

/-- One pass of `jump` at bit `i` of `n`: the state holds the coefficients `(am, ap)` of
`step^[n % 2^i]` and `(cm, cp)` of `step^[2^i]`.  When bit `i` is set, the pass applies
`step^[2^i]` after `step^[n % 2^i]`, and it squares the map of `2^i` steps. -/
def jumpPass (n i : UInt64) (s : UInt64 × UInt64 × UInt64 × UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let (am, ap, cm, cp) := s
  if (n >>> i) &&& 1 != 0 then (am * cm, ap * cm + cp, cm * cm, (cm + 1) * cp)
  else (am, ap, cm * cm, (cm + 1) * cp)

/-- The state after `n` steps from `x`, by one squaring of the affine map per bit of `n`. -/
def jump (n x : UInt64) : UInt64 :=
  let (am, ap, _, _) := LeanExe.loop 64 ((1 : UInt64), (0 : UInt64), multiplier, increment)
    fun i s => jumpPass n i s
  am * x + ap

end Library.Random.Lcg
