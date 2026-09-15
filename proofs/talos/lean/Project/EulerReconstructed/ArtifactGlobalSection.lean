import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerReconstructed.ArtifactTypeItems
import Project.EulerReconstructed.ArtifactExportItems

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 1811, limit := 30726 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 1844, limit := 30726 }) := by cbv

#print axioms globals_section_decoded

end Project.EulerReconstructed.Artifact
