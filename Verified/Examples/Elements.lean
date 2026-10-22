import Library.Numerics.Reductions.Float64.Program
import Library.Numerics.LinearAlgebra.Float64.Program
import Verified.Reflect.Command

/-! The fourteenth program of the verified compiler: arrays of floats and of `Bool`s.  The
programs read, build, update, and extend such arrays, take them as borrowed and as owned
parameters, and return them.  An array of floats holds each element's bit pattern in a word, and
an array of `Bool`s holds 1 or 0. -/

namespace Verified.Examples.Elements

export Library.Numerics.Reductions.Float64 (total largest select)

export Library.Numerics.LinearAlgebra.Float64 (dot axpy grid)

def extend (xs : Array Float) (x : Float) : Array Float := xs.push x ++ xs

/-- Whether each element is negative. -/
def negatives (xs : Array Float) : Array Bool :=
  LeanExe.build xs.size.toUInt64 fun i => xs[i.toNat]! < 0.0

def countTrue (bs : Array Bool) : UInt64 :=
  LeanExe.loop bs.size.toUInt64 0 fun i acc => if bs[i.toNat]! then acc + 1 else acc

def flip (bs : Array Bool) (i : UInt64) : Array Bool := bs.set! i.toNat (!bs[i.toNat]!)

def pushFlag (bs : Array Bool) (b : Bool) : Array Bool := bs.push b

/-- The flags of the composite numbers below `n`, from a sieve of Eratosthenes. -/
def sieve (n : UInt64) : Array Bool :=
  LeanExe.loop n (LeanExe.build n fun _ => false) fun i acc =>
    if i < 2 || acc[i.toNat]! then acc
    else LeanExe.loop n acc fun j flags =>
      if j ≥ i && i * j < n then flags.set! (i * j).toNat true else flags

verified_compile compiled := [Library.Numerics.Reductions.Float64.total, Library.Numerics.LinearAlgebra.Float64.dot, Library.Numerics.Reductions.Float64.largest, Library.Numerics.LinearAlgebra.Float64.grid, Library.Numerics.LinearAlgebra.Float64.axpy, extend, negatives, countTrue,
  Library.Numerics.Reductions.Float64.select, flip, pushFlag, sieve]

end Verified.Examples.Elements
