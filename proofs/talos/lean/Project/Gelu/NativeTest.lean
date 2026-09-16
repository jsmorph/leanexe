import Project.Gelu.Model

def main (args : List String) : IO Unit := do
  for arg in args do
    let some n := arg.toNat? | throw (IO.userError s!"invalid word: {arg}")
    if n ≥ 2^64 then throw (IO.userError s!"word out of range: {arg}")
    let result := Project.Gelu.gelu (UInt64.ofNat n)
    IO.println s!"{result.status.toNat} {result.bits.toNat}"
