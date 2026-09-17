import Project.SoftmaxWide.Model

def main (args : List String) : IO Unit := do
  if args.length % 5 != 0 then throw (IO.userError "expected groups of five words")
  let words ← args.toArray.mapM fun arg => do
    let some n := arg.toNat? | throw (IO.userError s!"invalid word: {arg}")
    if n ≥ 2^64 then throw (IO.userError s!"word out of range: {arg}")
    pure (UInt64.ofNat n)
  for i in [:words.size/5] do
    let r := Project.SoftmaxWide.compute words[5*i]! words[5*i+1]! words[5*i+2]!
      words[5*i+3]! words[5*i+4]!
    IO.println s!"{r.status.toNat} {r.p0.toNat} {r.p1.toNat} {r.p2.toNat} {r.p3.toNat}"
