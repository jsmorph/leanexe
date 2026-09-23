namespace Project.ProofKit.F32UniformRange

def productMagnitude (bound : Nat) : Nat := (2 ^ bound + 2 ^ (bound - 25)) / 2 ^ 149

def sumFits (count magnitude bound : Nat) : Bool :=
  bound ≤ 276 && decide (count * (magnitude + 2 ^ (bound - 25)) < 2 ^ bound)

def dotFits (count inputMagnitude weightMagnitude mulBound addBound : Nat) : Bool :=
  173 ≤ mulBound && mulBound ≤ 425 &&
    decide (inputMagnitude * weightMagnitude < 2 ^ mulBound) &&
    sumFits count (productMagnitude mulBound) addBound

def rescaleFits (inputMagnitude weightMagnitude scaleBound outputBound : Nat) : Bool :=
  173 ≤ scaleBound && scaleBound ≤ 425 && 173 ≤ outputBound && outputBound ≤ 425 &&
    decide (inputMagnitude * weightMagnitude < 2 ^ scaleBound) &&
    decide ((1032256 * 2 ^ 149) * productMagnitude scaleBound < 2 ^ outputBound)

end Project.ProofKit.F32UniformRange
