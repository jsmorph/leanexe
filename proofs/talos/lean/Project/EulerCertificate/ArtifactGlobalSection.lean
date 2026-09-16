import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactGlobalSectionItems

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem globals_tail6_decoded :
    Internal.vectorLoop global 0 { bytes := artifactBytes, pos := 2877, limit := 2877 } =
      .ok (Cache.raw.globals.drop 6, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by rfl

theorem globals_tail5_decoded :
    Internal.vectorLoop global 1 { bytes := artifactBytes, pos := 2872, limit := 2877 } =
      .ok (Cache.raw.globals.drop 5, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by
  exact vectorLoop_eq_cons global5_decoded globals_tail6_decoded

theorem globals_tail4_decoded :
    Internal.vectorLoop global 2 { bytes := artifactBytes, pos := 2867, limit := 2877 } =
      .ok (Cache.raw.globals.drop 4, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by
  exact vectorLoop_eq_cons global4_decoded globals_tail5_decoded

theorem globals_tail3_decoded :
    Internal.vectorLoop global 3 { bytes := artifactBytes, pos := 2862, limit := 2877 } =
      .ok (Cache.raw.globals.drop 3, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by
  exact vectorLoop_eq_cons global3_decoded globals_tail4_decoded

theorem globals_tail2_decoded :
    Internal.vectorLoop global 4 { bytes := artifactBytes, pos := 2857, limit := 2877 } =
      .ok (Cache.raw.globals.drop 2, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by
  exact vectorLoop_eq_cons global2_decoded globals_tail3_decoded

theorem globals_tail1_decoded :
    Internal.vectorLoop global 5 { bytes := artifactBytes, pos := 2852, limit := 2877 } =
      .ok (Cache.raw.globals.drop 1, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by
  exact vectorLoop_eq_cons global1_decoded globals_tail2_decoded

theorem globals_tail0_decoded :
    Internal.vectorLoop global 6 { bytes := artifactBytes, pos := 2846, limit := 2877 } =
      .ok (Cache.raw.globals.drop 0, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by
  exact vectorLoop_eq_cons global0_decoded globals_tail1_decoded

theorem globals_vector_decoded :
    vector global { bytes := artifactBytes, pos := 2845, limit := 2877 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by
  refine vector_eq_of_parts (length := 6)
    (itemsStart := { bytes := artifactBytes, pos := 2846, limit := 2877 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact globals_tail0_decoded

#print axioms globals_vector_decoded

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 2844, limit := 45644 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 2877, limit := 45644 }) := by
  refine sized_eq_of_parts (size := 32)
    (payload := { bytes := artifactBytes, pos := 2845, limit := 45644 }) (finish := { bytes := artifactBytes, pos := 2877, limit := 2877 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact globals_vector_decoded
  · rfl

#print axioms globals_section_decoded

end Project.EulerCertificate.Artifact
