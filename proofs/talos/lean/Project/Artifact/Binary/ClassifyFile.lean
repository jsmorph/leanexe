import Project.Artifact.Binary.Validate

open Wasm.Binary

private def classifyFile (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error error =>
      IO.println s!"{path}\tdecode\t{repr error.kind}"
  | .ok raw =>
      match validate raw with
      | .error error =>
          IO.println s!"{path}\tvalidation\t{repr error.kind}"
      | .ok _ =>
          IO.println s!"{path}\taccepted\t-"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: ClassifyFile <program.wasm>..."
    pure 2
  else
    args.forM classifyFile
    pure 0
