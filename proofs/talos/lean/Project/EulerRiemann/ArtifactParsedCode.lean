import Project.EulerRiemann.ArtifactParsedStates
import Project.Artifact.Binary.SectionParts

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072

theorem sections_from5 :
    sectionLoop 21754 5 afterExports { bytes := artifactBytes, pos := 1289, limit := 21767 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine sectionLoop_eq_step (fuel := 21753) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 1290, limit := 21767 }) (next := { bytes := artifactBytes, pos := 21767, limit := 21767 })
    (parsed := { afterExports with codes := Cache.raw.codes })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

#print axioms sections_from5

end Project.EulerRiemann.Artifact
