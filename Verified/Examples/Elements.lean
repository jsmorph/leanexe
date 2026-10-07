import Verified.Reflect.Command

/-! The fourteenth program of the verified compiler: arrays of floats and of `Bool`s.  The
programs read, build, update, and extend such arrays, take them as borrowed and as owned
parameters, and return them.  An array of floats holds each element's bit pattern in a word, and
an array of `Bool`s holds 1 or 0. -/

namespace Verified.Examples.Elements

def total (xs : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 0.0 fun i acc => acc + xs[i.toNat]!

/-- The dot product over the indices of `xs`, with `ys` read as 0 past its end. -/
def dot (xs ys : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 0.0 fun i acc => acc + xs[i.toNat]! * ys[i.toNat]!

/-- The largest element, or negative infinity for an empty array. -/
def largest (xs : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 (-(1.0 / 0.0)) fun i acc => max acc xs[i.toNat]!

/-- The points of a grid from `x0` with step `dx`. -/
def grid (n : UInt64) (x0 dx : Float) : Array Float :=
  LeanExe.build n fun i => x0 + i.toFloat * dx

/-- `a * x + y` for each element of `ys`, written in place. -/
def axpy (a : Float) (xs ys : Array Float) : Array Float :=
  LeanExe.loop ys.size.toUInt64 ys fun i acc =>
    acc.set! i.toNat (a * xs[i.toNat]! + acc[i.toNat]!)

def extend (xs : Array Float) (x : Float) : Array Float := xs.push x ++ xs

/-- Whether each element is negative. -/
def negatives (xs : Array Float) : Array Bool :=
  LeanExe.build xs.size.toUInt64 fun i => xs[i.toNat]! < 0.0

def countTrue (bs : Array Bool) : UInt64 :=
  LeanExe.loop bs.size.toUInt64 0 fun i acc => if bs[i.toNat]! then acc + 1 else acc

/-- The sum of the elements of `xs` whose flag in `bs` is true, a missing flag false. -/
def select (bs : Array Bool) (xs : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 0.0 fun i acc => if bs[i.toNat]! then acc + xs[i.toNat]! else acc

def flip (bs : Array Bool) (i : UInt64) : Array Bool := bs.set! i.toNat (!bs[i.toNat]!)

def pushFlag (bs : Array Bool) (b : Bool) : Array Bool := bs.push b

/-- The flags of the composite numbers below `n`, from a sieve of Eratosthenes. -/
def sieve (n : UInt64) : Array Bool :=
  LeanExe.loop n (LeanExe.build n fun _ => false) fun i acc =>
    if i < 2 then acc
    else LeanExe.loop n acc fun j flags =>
      if j ≥ 2 && i * j < n then flags.set! (i * j).toNat true else flags

verified_compile compiled := [total, dot, largest, grid, axpy, extend, negatives, countTrue,
  select, flip, pushFlag, sieve]

end Verified.Examples.Elements
