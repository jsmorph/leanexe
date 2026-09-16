import Project.LayerNorm.Model

def main (args : List String) : IO Unit := do
  let words ← args.mapM fun text => do
    let some word := text.toNat? | throw (IO.userError "invalid input word")
    if word ≥ 2^64 then throw (IO.userError "input word exceeds UInt64")
    pure word.toUInt64
  if words.length % 12 != 0 then throw (IO.userError "expected groups of twelve words")
  let words := words.toArray
  for row in [0:words.size/12] do
    let k := row*12
    let r := Project.LayerNorm.layerNorm words[k]! words[k+1]! words[k+2]! words[k+3]!
      words[k+4]! words[k+5]! words[k+6]! words[k+7]! words[k+8]! words[k+9]! words[k+10]! words[k+11]!
    IO.println s!"{r.status} {r.y0} {r.y1} {r.y2} {r.y3}"
