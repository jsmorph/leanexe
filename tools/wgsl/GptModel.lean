import Project.WGSL.GptHeadCheckpoint

open Project.TinyGpt2 Project.WGSL

/-- Evaluate the pure integer floating-point models for conformance tests.
The printed words are observations, not replacements for the execution proof. -/
def main (args : List String) : IO Unit := do
  unless args.length = 4 do throw (IO.userError "expected four byte tokens")
  let tokens ← args.mapM fun text => do
    let some n := text.toNat? | throw (IO.userError "invalid byte token")
    unless n < 256 do throw (IO.userError "token exceeds byte range")
    pure (UInt64.ofNat n)
  let row := hidden Checkpoint.words tokens[0]! tokens[1]! tokens[2]! tokens[3]! 3
  let hiddenWords := [row.x0, row.x1, row.x2, row.x3].map (fun w => toString w.toNat)
  let logits := (List.finRange 256).map fun j => toString (GptHead.separateResult Checkpoint.words row j).toNat
  IO.println (Lean.Json.mkObj [("hidden", Lean.toJson hiddenWords), ("logits", Lean.toJson logits)]).compress
