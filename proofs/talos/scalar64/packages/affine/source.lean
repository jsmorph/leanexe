namespace LeanExe.Examples.Arithmetic

def affine (x y : UInt64) : UInt64 :=
  x * 3 + y * 2 + 7

def choose (x y : UInt64) : UInt64 :=
  if x == 0 then y + 1 else x + y

end LeanExe.Examples.Arithmetic
