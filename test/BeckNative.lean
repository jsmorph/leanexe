import LeanExe.Examples.Beck

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then return 0
    let mut words : Array UInt64 := #[]
    for field in line.trimAscii.toString.splitOn "," do
      if field.isEmpty then continue
      match field.toNat? with
      | none => throw (IO.userError s!"invalid UInt64: {field}")
      | some n =>
        if n ≥ 2^64 then throw (IO.userError s!"UInt64 overflow: {field}")
        words := words.push n.toUInt64
    let result := LeanExe.Examples.Beck.compute words
    stdout.putStrLn ("[" ++ String.intercalate ","
      (result.toList.map (fun word => toString word.toNat)) ++ "]")
  return 0
