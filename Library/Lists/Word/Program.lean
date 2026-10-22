import LeanExe.Dialect.Loop

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

end Library.Lists.Word
