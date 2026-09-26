import Project.RunningSum.ArtifactDecode
import Project.RunningSum.ArtifactValidation
import Project.ByteIO.Wasi

namespace Project.RunningSum.Artifact

def module : Wasm.Module := raw.toTalos

set_option maxRecDepth 32768

theorem imports_exact : module.imports = Project.ByteIO.wasiImports := by rfl

theorem exports_exact : module.exports = [{ name := "_start", funcIdx := 17 }] := by rfl

#print axioms decoded
#print axioms encoded
#print axioms validated
#print axioms valid
#print axioms imports_exact
#print axioms exports_exact

end Project.RunningSum.Artifact
