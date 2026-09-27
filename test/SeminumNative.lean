import LeanExe.Examples.Seminum

open LeanExe.Examples.Seminum

def coefficients (text : String) : Array UInt64 :=
  if text == "[]" then #[]
  else (text.splitOn ",").toArray.map fun item => item.toNat!.toUInt64

def scalarText (result : ScalarResult) : String :=
  if result.status == 0 then s!"ok {result.value}" else s!"error {result.status}"

def fractionText (result : FractionResult) : String :=
  if result.status == 0 then s!"ok {result.numerator}/{result.denominator}"
  else s!"error {result.status}"

def evaluate (text : String) : IO String := do
  match text.splitOn ":" with
  | ["gcd", a, b] =>
    let x := a.toNat!
    let y := b.toNat!
    let result := LeanExe.Lib.NumberTheory.gcd x.toUInt64 y.toUInt64
    if result.toNat != Nat.gcd x y then throw (IO.userError "GCD disagrees with Nat.gcd")
    return s!"ok {result}"
  | ["fraction", n, d] => return fractionText (fraction n.toNat!.toUInt64 d.toNat!.toUInt64)
  | ["gcd-binary", a, b] =>
    let x := a.toNat!
    let y := b.toNat!
    let result := LeanExe.Lib.NumberTheory.gcdBinary x.toUInt64 y.toUInt64
    if result.toNat != Nat.gcd x y then throw (IO.userError "Binary GCD disagrees with Nat.gcd")
    return s!"ok {result}"
  | ["fraction-binary", n, d] =>
    return fractionText (fractionBinary n.toNat!.toUInt64 d.toNat!.toUInt64)
  | ["exp-word", bits] => return scalarText (exponential bits.toNat!.toUInt64)
  | ["decay-word", bits] => return scalarText (decay bits.toNat!.toUInt64)
  | ["polynomial", x, cs] => return scalarText (polynomial x.toNat!.toUInt64 (coefficients cs))
  | ["ratio", x, ns, ds] =>
    return fractionText (ratio x.toNat!.toUInt64 (coefficients ns) (coefficients ds))
  | _ => throw (IO.userError s!"invalid test case: {text}")

def main (args : List String) : IO Unit := do
  for arg in args do
    IO.println (← evaluate arg)
