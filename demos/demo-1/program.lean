namespace LeanExeGen.GeneratedRc8c2d9f87deb0758.Source

def countPrimeFactorsFuel :
    Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, count => count
  | fuel + 1, remaining, divisor, count =>
      if remaining ≤ 1 then
        count
      else if divisor > remaining / divisor then
        count + 1
      else if remaining % divisor = 0 then
        countPrimeFactorsFuel fuel (remaining / divisor) divisor (count + 1)
      else
        countPrimeFactorsFuel fuel remaining (divisor + 1) count

def compute (input : UInt64) : UInt64 :=
  countPrimeFactorsFuel input.toNat input 2 0

end LeanExeGen.GeneratedRc8c2d9f87deb0758.Source
