import Project.Artifact.Binary.Translate

open Wasm.Binary

private def checkFile (path : String) : IO Bool := do
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error error =>
      IO.eprintln s!"{path}:{error.offset}: decode: {repr error.kind}"
      pure false
  | .ok raw =>
      match validate raw with
      | .error error =>
          IO.eprintln s!"{path}: validation: {repr error}"
          pure false
      | .ok validated =>
          let module_ := validated.toTalos
          IO.println s!"translated {path}: {module_.funcs.length} functions, {module_.exports.length} function exports"
          pure true

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: TranslateFile <program.wasm>..."
    pure 2
  else
    let results ← args.mapM checkFile
    pure (if results.all id then 0 else 1)
