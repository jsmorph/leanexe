namespace LeanExe.Examples.Prng

def mix (state : UInt64) : UInt64 :=
  let z := (state ^^^ (state >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def generate (seed count modulus : UInt64) : Array UInt64 := Id.run do
  let mut state := seed
  let mut output : Array UInt64 := #[]
  for _ in [:count.toNat] do
    state := state + 0x9e3779b97f4a7c15
    output := output.push (mix state % modulus)
  return output

end LeanExe.Examples.Prng
