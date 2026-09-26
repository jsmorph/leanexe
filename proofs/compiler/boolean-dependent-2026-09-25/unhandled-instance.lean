import LeanExe.Extract.ScalarFunc

def booleanDependentMany (x y : UInt64) : UInt64 :=
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if _h : outer && !inner then a + b * 3 - c else a - b * 5 + c
  f x y (x + 7)
