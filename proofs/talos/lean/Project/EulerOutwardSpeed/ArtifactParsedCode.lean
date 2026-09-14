import Project.EulerOutwardSpeed.ArtifactParsedStates

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072

theorem sections_from5 :
    sectionLoop 4923 5 afterExports { bytes := artifactBytes, pos := 484, limit := 4936 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  refine sectionLoop_eq_step (fuel := 4922) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 485, limit := 4936 }) (next := { bytes := artifactBytes, pos := 4936, limit := 4936 })
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

end Project.EulerOutwardSpeed.Artifact
