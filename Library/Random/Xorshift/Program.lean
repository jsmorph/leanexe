import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop

/-! Marsaglia's xorshift64 generator with the shifts 13, 7, and 17: each step replaces the state
`x` with `x ^^^ (x <<< 13)`, then with `x ^^^ (x >>> 7)`, and then with `x ^^^ (x <<< 17)`.
`advance n x` applies `step` `n` times, and `jump n x` computes the same state from the 64 columns
of the step, the images of the powers of 2, by one squaring per bit of `n`. -/

namespace Library.Random.Xorshift

/-- One step of xorshift64: `x ^^^ (x <<< 13)`, then `x ^^^ (x >>> 7)`, then `x ^^^ (x <<< 17)`. -/
def step (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- The state after `n` steps from `x`. -/
def advance (n x : UInt64) : UInt64 := LeanExe.loop n x fun _ s => step s

/-- The xor of the words `c[i]` at the set bits `i` of `x`. -/
def applyCols (c : Array UInt64) (x : UInt64) : UInt64 :=
  LeanExe.loop 64 0 fun i acc => if (x >>> i) &&& 1 != 0 then acc ^^^ c[i.toNat]! else acc

/-- The columns of the square of the map whose columns are `c`. -/
def square (c : Array UInt64) : Array UInt64 :=
  LeanExe.build 64 fun i => applyCols c c[i.toNat]!

/-- One pass of `jump` at bit `i` of `n`: the state holds the word `step^[n % 2^i] x` and the
columns of `step^[2^i]`.  When bit `i` is set, the pass applies the columns to the word, and it
replaces the columns by those of their square. -/
def jumpPass (n i : UInt64) (s : UInt64 × Array UInt64) : UInt64 × Array UInt64 :=
  let (y, c) := s
  ((if (n >>> i) &&& 1 != 0 then applyCols c y else y), square c)

/-- The state after `n` steps from `x`, by one squaring of the step's columns per bit of `n`. -/
def jump (n x : UInt64) : UInt64 :=
  let (y, _) := LeanExe.loop 64 (x, LeanExe.build 64 fun i => step ((1 : UInt64) <<< i))
    fun i s => jumpPass n i s
  y

end Library.Random.Xorshift
