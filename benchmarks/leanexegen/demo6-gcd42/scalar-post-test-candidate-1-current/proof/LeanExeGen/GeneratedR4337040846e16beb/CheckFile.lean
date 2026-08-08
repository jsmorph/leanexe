import LeanExeGen.GeneratedR4337040846e16beb.ArtifactBytes

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: CheckFile <program.wasm>"
      return 2
  let found ← IO.FS.readBinFile file
  if found == LeanExeGen.GeneratedR4337040846e16beb.Artifact.artifactBytes then
    IO.println s!"embedded bytes matched: {found.size} bytes"
    return 0
  IO.eprintln s!"embedded bytes differ: {file}"
  return 1
