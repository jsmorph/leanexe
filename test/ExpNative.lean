import LeanExe.Examples.Seminum

def main (args : List String) : IO Unit := do
  let [input, output] := args | throw (IO.userError "expected input and output paths")
  let lines := (← IO.FS.readFile input).splitOn "\n"
  IO.FS.withFile output .write fun handle => do
    for line in lines do
      if !line.isEmpty then
        let some n := line.toNat? | throw (IO.userError s!"invalid input word: {line}")
        if n >= 2^64 then throw (IO.userError "input exceeds UInt64")
        let bits := n.toUInt64
        let port := LeanExe.Lib.Transcendental.exp bits
        let native := (Float.ofBits bits).exp.toBits
        handle.putStrLn s!"{port} {native}"
