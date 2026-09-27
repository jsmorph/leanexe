namespace LeanExe.Lib.NumberTheory

def gcdBinary (a b : UInt64) : UInt64 := Id.run do
  if a == 0 then return b
  if b == 0 then return a
  let mut x := a
  let mut y := b
  let mut shift : UInt64 := 0
  while (x ||| y) &&& 1 == 0 do
    x := x >>> 1
    y := y >>> 1
    shift := shift + 1
  while x &&& 1 == 0 do
    x := x >>> 1
  while y != 0 do
    while y &&& 1 == 0 do
      y := y >>> 1
    if x > y then
      let saved := x
      x := y
      y := saved
    y := y - x
  return x <<< shift

end LeanExe.Lib.NumberTheory
