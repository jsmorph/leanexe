import LeanExe.WGSL.Examples.Body

open LeanExe.WGSL.Examples.Body

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Prepare.lean OUTPUT_DIRECTORY")
  let directory : System.FilePath := directory
  let mut manifest : List Lean.Json := []
  for (name, _, shape) in cases do
    let lines := ["import LeanExe.WGSL.Examples.Body", "open LeanExe.WGSL.Examples.Body",
      s!"#compile_wgsl {name} {shape.rows} {shape.cols} {shape.elementsA} {shape.elementsB} {reprStr (directory / name).toString}",
      s!"#print axioms {name}.wgslSourceCorrect", s!"#print axioms {name}.wgslShaderParsed",
      s!"#print axioms {name}.wgslExecutionCorrect"]
    IO.FS.writeFile (directory / s!"{name}.lean") (String.intercalate "\n" lines ++ "\n")
    manifest := manifest ++ [Lean.Json.mkObj [("name", Lean.toJson name), ("shape", Lean.toJson shape)]]
  IO.FS.writeFile (directory / "cases.json") (Lean.toJson manifest).pretty
