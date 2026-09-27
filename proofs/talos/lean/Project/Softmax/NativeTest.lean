import Project.Softmax.Model

def main (args : List String) : IO Unit := do
  let words ← args.mapM fun text => do
    let some word := text.toNat? | throw (IO.userError "invalid input word")
    if word ≥ 2^64 then throw (IO.userError "input word exceeds UInt64")
    pure word.toUInt64
  if words.length % 5 != 0 then throw (IO.userError "expected groups of five words")
  let words := words.toArray
  for row in [0:words.size/5] do
    let k := row*5
    let r := Project.Softmax.softmax words[k]! words[k+1]! words[k+2]! words[k+3]! words[k+4]!
    IO.println s!"{r.status} {r.p0} {r.p1} {r.p2} {r.p3}"
