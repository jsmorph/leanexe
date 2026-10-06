/-! SplitMix64, Sebastiano Vigna's generator (https://prng.di.unimi.it/splitmix64.c):
each step adds `0x9e3779b97f4a7c15` to a 64-bit state and mixes the new state into an
output word with two multiply-and-xor rounds and a final xor.  Arithmetic wraps modulo
`2 ^ 64`, as in the reference C code. -/

namespace Examples.Prng

/-- One SplitMix64 step: the advanced state, and the output word for it. -/
def splitMix (state : UInt64) : UInt64 × UInt64 :=
  let s := state + 0x9e3779b97f4a7c15
  let a := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let b := (a ^^^ (a >>> 27)) * 0x94d049bb133111eb
  (s, b ^^^ (b >>> 31))

/-- The top 53 bits of `x` as a float in `[0, 1)`: `(x >>> 11) / 2 ^ 53`, which is exact,
since the numerator has at most 53 bits and the divisor is a power of 2. -/
def unitFloat (x : UInt64) : Float := (x >>> 11).toFloat / 9007199254740992.0

end Examples.Prng
