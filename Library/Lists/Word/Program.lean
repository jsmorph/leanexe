module

public import LeanExe.Dialect.Loop

@[expose] public section

namespace Library.Lists.Word

/-- The sum of the elements modulo 2^64. -/
def listSum (xs : List UInt64) : UInt64 := xs.foldl (· + ·) 0

@[inline] def range (n : UInt64) : List UInt64 :=
  LeanExe.loop n [] fun i xs => (n - 1 - i) :: xs

def sum (xs : List UInt64) (acc : UInt64) : UInt64 :=
  match xs with
  | [] => acc
  | x :: tail => sum tail (acc + x)

def reverse (xs acc : List UInt64) : List UInt64 :=
  match xs with
  | [] => acc
  | x :: tail => reverse tail (x :: acc)

def increment : List UInt64 → List UInt64
  | [] => []
  | x :: xs => (x + 1) :: increment xs

/-- Realizes the functional induction principles of `sum` and `reverse` here.  `verified_compile`
proves the termination of the loops it compiles from them with `fun_induction`, which realizes the
principles in each module that compiles them.  Lean v4.36.0 refuses to import two such modules: it
merges two realizations of a theorem only when the theorem concludes in a constant, and these
conclude in their motive. -/
theorem inductions_realized : True := by
  have := @sum.induct
  have := @sum.induct_unfolding
  have := @reverse.induct
  have := @reverse.induct_unfolding
  trivial

end Library.Lists.Word
