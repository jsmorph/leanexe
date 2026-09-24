import Project.ByteIO.ArtifactCache
import Project.ByteIO.Wasi

namespace Project.ByteIO.Artifact

def module : Wasm.Module := raw.toTalos

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem imports_exact : module.imports = wasiImports := by rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem exports_exact : module.exports = [{ name := "_start", funcIdx := 9 }] := by rfl

#print axioms imports_exact
#print axioms exports_exact

end Project.ByteIO.Artifact
