import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Decode
import Lean.Elab.Tactic.Cbv

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

set_option maxRecDepth 131072 in
set_option cbv.maxSteps 1000000 in
theorem code99_decoded :
    code { bytes := artifactBytes, pos := 18034, limit := 21767 } =
      .ok (Cache.raw.codes[99]!, { bytes := artifactBytes, pos := 20820, limit := 21767 }) := by
  cbv

#print axioms code99_decoded

end Project.EulerRiemann.Artifact
