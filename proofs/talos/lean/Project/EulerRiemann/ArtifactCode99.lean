import Project.EulerRiemann.ArtifactCode99Part0

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072 in
theorem code99_decoded :
    code { bytes := artifactBytes, pos := 18034, limit := 21767 } =
      .ok (Cache.raw.codes[99]!, { bytes := artifactBytes, pos := 20820, limit := 21767 }) := by
  refine code_eq_of_parts (size := 2784)
    (payload := { bytes := artifactBytes, pos := 18036, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 18039, limit := 20820 })
    (bodyFinish := { bytes := artifactBytes, pos := 20820, limit := 20820 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code99_tail0_decoded
  · rfl

#print axioms code99_decoded

end Project.EulerRiemann.Artifact
