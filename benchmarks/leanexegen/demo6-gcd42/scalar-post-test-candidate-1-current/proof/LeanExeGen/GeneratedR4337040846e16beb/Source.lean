namespace LeanExeGen.GeneratedR4337040846e16beb.Source

def gcdWith42 (value : UInt64) : UInt64 := Id.run do
  let mut x := value
  let mut y : UInt64 := 42
  while y != 0 do
    let remainder := x % y
    x := y
    y := remainder
  return x

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size == 1 then
    #[gcdWith42 input[0]!]
  else
    input

end LeanExeGen.GeneratedR4337040846e16beb.Source
