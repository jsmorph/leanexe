namespace LeanExe.Examples.Collatz

def maxSteps : Nat :=
  10000

def next (n : UInt64) : UInt64 :=
  if n % 2 == 0 then
    n / 2
  else
    n * 3 + 1

def stepsFuel : Nat → UInt64 → UInt64 → UInt64
  | 0, _, steps => steps
  | fuel + 1, n, steps =>
      if n == 0 || n == 1 then
        steps
      else
        stepsFuel fuel (next n) (steps + 1)

def steps (n : UInt64) : UInt64 :=
  stepsFuel maxSteps n 0

def benchFuel : Nat → UInt64 → UInt64 → UInt64
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      benchFuel fuel n (acc + steps n)

def bench (n iters : UInt64) : UInt64 :=
  benchFuel iters.toNat n 0

theorem stepsFuel_one (fuel : Nat) (steps : UInt64) :
    stepsFuel fuel 1 steps = steps := by
  cases fuel <;> simp [stepsFuel]

theorem stepsFuel_zero (fuel : Nat) (steps : UInt64) :
    stepsFuel fuel 0 steps = steps := by
  cases fuel <;> simp [stepsFuel]

theorem steps_one :
    steps 1 = 0 := by
  exact stepsFuel_one maxSteps 0

theorem steps_zero :
    steps 0 = 0 := by
  exact stepsFuel_zero maxSteps 0

end LeanExe.Examples.Collatz
