namespace LeanExe.Examples.ScalarHelper

def combine (left right : UInt64) : UInt64 := left * 5 + right

def caller (x y : UInt64) : UInt64 :=
  let intermediate := combine (x + 1) (y * 2)
  intermediate + x

end LeanExe.Examples.ScalarHelper
