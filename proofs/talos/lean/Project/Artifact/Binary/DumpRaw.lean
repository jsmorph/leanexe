import Project.Artifact.Binary.Decode

open Wasm.Binary

def main (args : List String) : IO UInt32 := do
  let some path := args.head?
    | IO.eprintln "usage: DumpRaw <program.wasm>"
      pure 2
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error error =>
      IO.eprintln s!"{path}:{error.offset}: {repr error.kind}"
      pure 1
  | .ok raw =>
      IO.println (repr raw)
      pure 0
