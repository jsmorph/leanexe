import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Decode
import Lean.Elab.Tactic.Cbv

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

set_option maxRecDepth 131072 in
theorem code0_decoded :
    code { bytes := artifactBytes, pos := 1294, limit := 21767 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 1313, limit := 21767 }) := by
  cbv

#print axioms code0_decoded

end Project.EulerRiemann.Artifact
