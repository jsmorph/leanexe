import Project.Artifact.Binary.Decode

open Wasm.Binary

private def checkFile (path : String) : IO Bool := do
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error error =>
      IO.eprintln s!"{path}:{error.offset}: {repr error.kind}"
      pure false
  | .ok module_ =>
      IO.println s!"decoded {path}: {module_.codes.length} functions, {bytes.size} bytes"
      pure true

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: DecodeFile <program.wasm>..."
    pure 2
  else
    let results ← args.mapM checkFile
    pure (if results.all id then 0 else 1)
