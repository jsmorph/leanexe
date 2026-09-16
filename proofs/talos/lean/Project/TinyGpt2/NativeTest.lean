import Project.TinyGpt2.Model
import Lean.Data.Json

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the initialization fixture path")
  let fixture ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let strings ← IO.ofExcept (fixture.getObjValAs? (Array String) "weights")
  let weights ← strings.mapM fun s => do
    let some n := s.toNat? | throw (IO.userError "invalid weight word")
    if n ≥ 2^64 then throw (IO.userError "weight word out of range")
    pure (UInt64.ofNat n)
  if weights.size != Project.TinyGpt2.Layout.size then throw (IO.userError "invalid weight count")
  let cases ← IO.ofExcept (fixture.getObjValAs? (Array Lean.Json) "cases")
  for c in cases do
    let tokens ← IO.ofExcept (c.getObjValAs? (Array Nat) "tokens")
    let position ← IO.ofExcept (c.getObjValAs? Nat "position")
    if tokens.size != 4 || tokens.any (fun t => t ≥ 256) || position ≥ 4 then
      throw (IO.userError "invalid context")
    let r := Project.TinyGpt2.hidden weights (UInt64.ofNat tokens[0]!)
      (UInt64.ofNat tokens[1]!) (UInt64.ofNat tokens[2]!) (UInt64.ofNat tokens[3]!)
      (UInt64.ofNat position)
    let logits := [0, 32, 65, 255].map fun t => (Project.TinyGpt2.logit weights r t).toNat
    IO.println (s!"{r.x0.toNat} {r.x1.toNat} {r.x2.toNat} {r.x3.toNat} " ++
      String.intercalate " " (logits.map toString))
