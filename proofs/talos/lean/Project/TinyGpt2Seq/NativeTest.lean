import Project.TinyGpt2Seq.Inference
import Lean.Data.Json

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a fixture path")
  let fixture ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let strings ← IO.ofExcept (fixture.getObjValAs? (Array String) "weights")
  let weights ← strings.mapM fun s => do
    let some n := s.toNat? | throw (IO.userError "invalid weight word")
    if n ≥ 2^64 then throw (IO.userError "weight word out of range")
    pure (UInt64.ofNat n)
  if weights.size != Project.TinyGpt2Seq.Layout.size then
    throw (IO.userError "invalid weight count")
  let cases ← IO.ofExcept (fixture.getObjValAs? (Array Lean.Json) "cases")
  for c in cases do
    let tokens ← IO.ofExcept (c.getObjValAs? (Array Nat) "tokens")
    if tokens.isEmpty || tokens.size > 128 || tokens.any (fun t => t ≥ 256) then
      throw (IO.userError "invalid context")
    let output := Project.TinyGpt2Seq.inferChecked weights 0x4024000000000000
      (tokens.map UInt64.ofNat)
    IO.println (String.intercalate " " (output.toList.map fun x => toString x.toNat))
