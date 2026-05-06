namespace LeanExe.Examples.Prime

def searchFuel : Nat :=
  100000

def compositeFuel : Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, composite => composite
  | fuel + 1, n, d, composite =>
      if d == n || composite == 1 then
        composite
      else
        compositeFuel fuel n (d + 1)
          (if n % d == 0 then 1 else composite)

def isPrimeFlag (n : UInt64) : UInt64 :=
  if n == 0 || n == 1 then
    0
  else if compositeFuel n.toNat n 2 0 == 0 then
    1
  else
    0

def nextFuel : Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, result => result
  | fuel + 1, candidate, found, result =>
      if found == 1 then
        result
      else
        nextFuel fuel (candidate + 1)
          (if isPrimeFlag candidate == 1 then 1 else found)
          (if isPrimeFlag candidate == 1 then candidate else result)

def next (n : UInt64) : UInt64 :=
  nextFuel searchFuel (n + 1) 0 0

end LeanExe.Examples.Prime
