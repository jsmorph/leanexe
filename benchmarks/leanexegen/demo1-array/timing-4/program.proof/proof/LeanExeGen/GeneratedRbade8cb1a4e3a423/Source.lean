namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.Source

def countFactorsFuel : Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, remaining, _, count =>
      if remaining > 1 then count + 1 else count
  | fuel + 1, remaining, divisor, count =>
      if remaining ≤ 1 then
        count
      else if divisor > remaining / divisor then
        count + 1
      else if remaining % divisor == 0 then
        countFactorsFuel fuel (remaining / divisor) divisor (count + 1)
      else
        countFactorsFuel fuel remaining (if divisor == 2 then 3 else divisor + 2) count

def countFactors (value : UInt64) : UInt64 :=
  if value ≤ 1 then
    0
  else
    countFactorsFuel value.toNat value 2 0

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size == 1 then
    #[countFactors input[0]!]
  else
    input

end LeanExeGen.GeneratedRbade8cb1a4e3a423.Source
