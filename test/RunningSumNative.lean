import LeanExe.Examples.RunningSum

open LeanExe.Examples.RunningSum

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut total : Decimal := ⟨false, ByteArray.empty⟩
  repeat
    let text ← stdin.getLine
    if text.isEmpty then return 0
    let bytes := text.toUTF8
    let line := if bytes[bytes.size - 1]! == 10 then
      bytes.extract 0 (bytes.size - 1) else bytes
    match parse line with
    | none => return 28
    | some value =>
        total := add total value
        stdout.putStr (String.fromUTF8! (render total))
        stdout.flush
  pure 0
