import Project.ByteIO.Binary
import Project.RunningSum.ArtifactBytes

def main : IO Unit := do
  match Project.ByteIO.Binary.decode Project.RunningSum.Artifact.bytes with
  | .error error => throw (IO.userError (reprStr error))
  | .ok raw =>
    IO.println "import Project.ByteIO.Binary\n\nnamespace Project.RunningSum.Artifact\n\nset_option maxRecDepth 131072\n"
    IO.println ("def raw : Project.ByteIO.Binary.Raw :=\n" ++ reprStr raw)
    IO.println "\nend Project.RunningSum.Artifact"
