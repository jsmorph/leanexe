namespace LeanExe.Examples.EncodingGcd

set_option backward.do.legacy true in
def gcd (a b : UInt64) : UInt64 := Id.run do
  let mut x := a
  let mut y := b
  while y != 0 do
    let r := x % y
    x := y
    y := r
  return x

end LeanExe.Examples.EncodingGcd
