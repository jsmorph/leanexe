import Verified.Reflect.Command

/-! The ninth program of the verified compiler: values that own arrays.  A function returns an owned
array, so a function that returns a parameter takes it owned, as `copy` does, and copies it where
the parameter is used again, as `twice` does.  A caller owns a call's array result: it moves the
result where the result's variable dies, copies it where the variable stays live, and releases it
where the variable dies without a use.  A call's array argument that is not a variable is bound with
`let` first and released after the call.  `LeanExe.build` creates an owned array; its element may
allocate and release arrays of its own, and an owned variable that only the element reads is
released after the array is complete. -/

namespace Verified.Examples.Owned

def sum (xs : Array UInt64) : UInt64 :=
  LeanExe.loop xs.size.toUInt64 0 fun i acc => acc + xs[i.toNat]!

def copy (xs : Array UInt64) : Array UInt64 := xs

def pick (b : Bool) (xs ys : Array UInt64) : Array UInt64 := if b then xs else ys

def twice (xs : Array UInt64) : Array UInt64 × Array UInt64 := (xs, xs)

def withSize (xs : Array UInt64) : Array UInt64 × UInt64 := (copy xs, xs.size.toUInt64)

def sizeOfCopy (xs : Array UInt64) : UInt64 :=
  let ys := copy xs
  ys.size.toUInt64

def sumCopy (xs : Array UInt64) : UInt64 := sum (copy xs)

def firstOfCopy (xs : Array UInt64) : UInt64 :=
  let ys := copy xs
  ys[(0 : UInt64).toNat]!

def unused (xs : Array UInt64) : UInt64 :=
  let _ys := copy xs
  7

def branch (b : Bool) (xs : Array UInt64) : UInt64 :=
  let ys := copy xs
  if b then ys.size.toUInt64 else 0

def moved (xs : Array UInt64) : Array UInt64 :=
  let ys := copy xs
  ys

def grow (xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  LeanExe.loop n (copy xs) fun i acc => if i < 2 then copy acc else acc

def swap (xs ys : Array UInt64) : Array UInt64 × Array UInt64 :=
  let p := (copy xs, copy ys)
  (p.2, p.1)

def squares (n : UInt64) : Array UInt64 := LeanExe.build n fun i => i * i

def scaled (xs : Array UInt64) (k : UInt64) : Array UInt64 :=
  LeanExe.build xs.size.toUInt64 fun i => xs[i.toNat]! * k

def sumSquares (n : UInt64) : UInt64 := sum (squares n)

def rowSums (n : UInt64) : Array UInt64 :=
  LeanExe.build n fun i => sum (LeanExe.build i fun j => j + i)

def onlyInside (xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  let ys := copy xs
  LeanExe.build n fun i => ys[i.toNat]! + ys.size.toUInt64

def bothSides (xs : Array UInt64) : Array UInt64 :=
  let ys := copy xs
  LeanExe.build ys.size.toUInt64 fun i => ys[i.toNat]! + 1

verified_compile compiled := [sum, copy, pick, twice, withSize, sizeOfCopy, sumCopy, firstOfCopy,
  unused, branch, moved, grow, swap, squares, scaled, sumSquares, rowSums, onlyInside, bothSides]

end Verified.Examples.Owned
