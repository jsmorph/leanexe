import LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactBytes

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: CheckFile <program.wasm>"
      return 2
  let found ← IO.FS.readBinFile file
  if found == LeanExeGen.GeneratedRa8e90ffc5781d113.Artifact.artifactBytes then
    IO.println s!"embedded bytes matched: {found.size} bytes"
    return 0
  IO.eprintln s!"embedded bytes differ: {file}"
  return 1
