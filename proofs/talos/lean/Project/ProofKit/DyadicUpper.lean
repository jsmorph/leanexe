namespace Project.ProofKit.DyadicUpper

def scale : Nat := 2 ^ 160
def ceilingDivision (numerator denominator : Nat) : Nat :=
  (numerator + denominator - 1) / denominator
def integer (n : Nat) : Nat := n * scale
def fraction (numerator denominator : Nat) : Nat := ceilingDivision (numerator * scale) denominator
def add (a b : Nat) : Nat := a + b
def mul (a b : Nat) : Nat := ceilingDivision (a * b) scale
def divNat (a denominator : Nat) : Nat := ceilingDivision a denominator
def fp32Magnitude (scaledMagnitude : Nat) : Nat := scaledMagnitude * 2 ^ 11
def roundoff (bound subtraction denominatorPower : Nat) : Nat :=
  fraction (2 ^ (bound - subtraction)) (2 ^ denominatorPower)

end Project.ProofKit.DyadicUpper
