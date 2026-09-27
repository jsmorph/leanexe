namespace LeanExe.Lib.Polynomial

def eval (coefficients : Array UInt64) (x : UInt64) : Option UInt64 := Id.run do
  let mut value : UInt64 := 0
  let mut index := coefficients.size
  while index > 0 do
    index := index - 1
    let coefficient := coefficients[index]!
    if x != 0 && value > (18446744073709551615 - coefficient) / x then
      return none
    value := value * x + coefficient
  return some value

end LeanExe.Lib.Polynomial
