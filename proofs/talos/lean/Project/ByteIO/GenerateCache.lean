import Project.ByteIO.Binary
import Project.ByteIO.ArtifactBytes

/-- Untrusted cache generation; the resulting definition is checked by the
separate exact decoding theorem. This command supplies no proof evidence. -/
def main : IO Unit := do
  match Project.ByteIO.Binary.decode Project.ByteIO.Artifact.bytes with
  | .error e => throw (IO.userError (reprStr e))
  | .ok raw =>
    IO.println "import Project.ByteIO.Binary\n\nnamespace Project.ByteIO.Artifact\n"
    IO.println ("def raw : Binary.Raw :=\n" ++ reprStr raw)
    IO.println "\nend Project.ByteIO.Artifact"
