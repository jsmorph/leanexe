namespace LeanExe.Examples.Correctness

def shortOrSkipsTrap : UInt64 :=
  if true || ((Array.replicate 1 (0 : UInt64))[5]! == 0) then 1 else 0

def shortAndSkipsTrap : UInt64 :=
  if false && ((Array.replicate 1 (0 : UInt64))[5]! == 0) then 1 else 0

def divByZero : UInt64 :=
  (5 : UInt64) / 0

def modByZero : UInt64 :=
  (5 : UInt64) % 0

def overflow : UInt64 :=
  (18446744073709551615 : UInt64) + 1

def underflow : UInt64 :=
  (0 : UInt64) - 1

def nestedShadow (x : UInt64) : UInt64 :=
  let x := x + 1
  let y := (let x := x + 2; x * 10)
  x + y

def combine (left right : UInt64) : UInt64 :=
  left * (100 : UInt64) + right

def callArgLets (x : UInt64) : UInt64 :=
  combine (let y := x + 1; y) (let z := x + 2; z)

def arrayUpdateRead : UInt64 :=
  let a := Array.replicate 2 (0 : UInt64)
  let b := a.set! 0 1
  let c := b.set! 1 (b[0]! + a[0]!)
  c[0]! * (100 : UInt64) + c[1]! * (10 : UInt64) + a[0]!

def recLetFuel : Nat → UInt64 → UInt64 → UInt64
  | 0, _, right => right
  | fuel + 1, left, right =>
      recLetFuel fuel (let next := left + 1; next) (let next := right + 2; next)

def recLetDemo : UInt64 :=
  recLetFuel 4 1 10

def rejectProductLet : UInt64 :=
  let pair := ((1 : UInt64), (2 : UInt64))
  pair.1

def rejectNonzeroReplicate : Array UInt64 :=
  Array.replicate 2 (7 : UInt64)

def rejectHigherOrder (f : UInt64 → UInt64) : UInt64 :=
  f 1

def rejectIO : IO UInt64 :=
  pure 1

end LeanExe.Examples.Correctness
