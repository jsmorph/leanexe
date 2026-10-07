import Verified.Reflect.Command

/-! The eighteenth program of the verified compiler: `LeanExe.repeatWhile`, a loop that stops when
its condition fails.  The programs carry words, floats, pairs that hold arrays, and a structure as
the state, stop early under fuels up to `2 ^ 64 - 1`, read an owned array of the state in the
condition, and update it in place in the step.  The last five check that the theorems do not
evaluate loops whose conditions read only literal data: a pair result that holds an array,
`match` on a loop's result and on a call with literal arguments, and a closed loop. -/

namespace Verified.Examples.Repeat

/-- The number of steps of the Collatz map from `n` to 1, at most 1,000. -/
def collatzSteps (n : UInt64) : UInt64 :=
  (LeanExe.repeatWhile 1000 (n, (0 : UInt64)) (fun s => 1 < s.1)
    fun s => (if s.1 % 2 == 0 then s.1 / 2 else 3 * s.1 + 1, s.2 + 1)).2

/-- The first multiple of `k` from `start` on, under a fuel that the loop never reaches when `k`
is positive. -/
def firstMultiple (k start : UInt64) : UInt64 :=
  LeanExe.repeatWhile 18446744073709551615 start (fun x => x % k != 0) fun x => x + 1

/-- Newton's iteration for the square root of `a`, from `a`, until the residual is small. -/
def newtonSqrt (a : Float) : Float :=
  LeanExe.repeatWhile 64 a (fun x => 1e-12 * a < (x * x - a).abs) fun x => 0.5 * (x + a / x)

/-- The elements of `xs` below `limit`, in order, gathered until `count` of them are found. -/
def below (xs : Array UInt64) (limit count : UInt64) : Array UInt64 :=
  (LeanExe.repeatWhile xs.size.toUInt64 ((0 : UInt64), LeanExe.build 0 fun i => i)
    (fun s => s.2.size.toUInt64 < count)
    fun s => (s.1 + 1, if xs[s.1.toNat]! < limit then s.2.push xs[s.1.toNat]! else s.2)).2

/-- `xs` with its elements set to 0 from the start up to the first element equal to `v`, in
place. -/
def clearUntil (xs : Array UInt64) (v : UInt64) : Array UInt64 :=
  (LeanExe.repeatWhile xs.size.toUInt64 ((0 : UInt64), xs)
    (fun s => s.1 < s.2.size.toUInt64 && s.2[s.1.toNat]! != v)
    fun s => (s.1 + 1, s.2.set! s.1.toNat 0)).2

structure Fall where
  height : Float
  speed : Float
  steps : UInt64

instance : LeanExe.Pipeline.Flat Fall (Float × Float × UInt64) :=
  ⟨fun f => (f.height, f.speed, f.steps)⟩

/-- A body falling from `h0` under gravity, in steps of `dt`, until it reaches the ground. -/
def fall (h0 dt : Float) : Fall :=
  LeanExe.repeatWhile 100000 ⟨h0, 0.0, 0⟩ (fun f => 0.0 < f.height)
    fun f => ⟨f.height - f.speed * dt, f.speed + 9.81 * dt, f.steps + 1⟩

/-- `xs` and 100,000, counted up under a fuel of `2 ^ 64 - 1`: a pair result that holds an array,
from a loop whose condition reads only literal data. -/
def countUp (xs : Array UInt64) : Array UInt64 × UInt64 :=
  LeanExe.repeatWhile 18446744073709551615 (xs, (0 : UInt64)) (fun s => s.2 < 100000)
    fun s => (s.1, s.2 + 1)

/-- `k` plus the sum of the words below `100000`, taken apart from the loop's tuple with `match`. -/
def sumTo (k : UInt64) : UInt64 :=
  match LeanExe.repeatWhile 1000000 ((0 : UInt64), (0 : UInt64)) (fun s => s.1 < 100000)
      fun s => (s.1 + 1, s.2 + s.1) with
  | (_, total) => total + k

/-- The size of `xs` plus 1,000, from a `match` on a loop's result that holds an array. -/
def rest (xs : Array UInt64) : UInt64 :=
  match LeanExe.repeatWhile 18446744073709551615 (xs, (0 : UInt64)) (fun s => s.2 < 1000)
      fun s => (s.1, s.2 + 1) with
  | (ys, k) => ys.size.toUInt64 + k

/-- `k` plus the steps of a fall from 10, from a `match` on a call with literal arguments. -/
def fallSteps (k : UInt64) : UInt64 :=
  match fall 10.0 0.01 with
  | ⟨_, _, n⟩ => n + k

/-- `x` plus a closed loop, which the code computes. -/
def offset (x : UInt64) : UInt64 :=
  x + LeanExe.repeatWhile 18446744073709551615 (0 : UInt64) (· < 100000) (· + 1)

verified_compile compiled := [collatzSteps, firstMultiple, newtonSqrt, below, clearUntil, fall,
  countUp, sumTo, rest, fallSteps, offset]

end Verified.Examples.Repeat
