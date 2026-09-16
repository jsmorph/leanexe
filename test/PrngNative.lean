import LeanExe.Examples.Prng

def main (args : List String) : IO Unit := do
  match args with
  | [seed, count, modulus] =>
    let values := LeanExe.Examples.Prng.generate
      seed.toNat!.toUInt64 count.toNat!.toUInt64 modulus.toNat!.toUInt64
    for value in values do
      IO.println value
  | _ => throw (IO.userError "expected seed, count, and modulus")
