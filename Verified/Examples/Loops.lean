import Verified.Reflect.Command

/-! The seventh program of the verified compiler: `LeanExe.loop` over a word, over a pair, and
over a pair with a `Bool`, a loop inside a loop, a loop whose body branches, and a loop whose
body calls an earlier function.  The loop keeps its count, its index, and its state in locals and
leaves when the index reaches the count. -/

namespace Verified.Examples.Loops

def triangle (n : UInt64) : UInt64 := LeanExe.loop n 0 fun i acc => acc + i

def fib (n : UInt64) : UInt64 :=
  (LeanExe.loop n ((0 : UInt64), (1 : UInt64)) fun _ (a, b) => (b, a + b)).1

def power (x n : UInt64) : UInt64 := LeanExe.loop n 1 fun _ acc => acc * x

def collatz (x n : UInt64) : UInt64 :=
  LeanExe.loop n x fun _ y => if y % 2 == 0 then y / 2 else 3 * y + 1

def grid (n m : UInt64) : UInt64 :=
  LeanExe.loop n 0 fun i acc => LeanExe.loop m acc fun j acc => acc + (i + 1) * (j ^^^ i)

def sumPowers (x n : UInt64) : UInt64 := LeanExe.loop n 0 fun i acc => acc + power x i

def firstAbove (limit n : UInt64) : UInt64 × Bool :=
  LeanExe.loop n (0, false) fun i (found, seen) =>
    if seen then (found, seen) else if limit < i * i then (i, true) else (found, seen)

verified_compile compiled := [triangle, fib, power, collatz, grid, sumPowers, firstAbove]

end Verified.Examples.Loops
