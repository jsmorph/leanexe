import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem global0_decoded :
    global { bytes := artifactBytes, pos := 396, limit := 427 } =
      .ok (Cache.raw.globals[0]!, { bytes := artifactBytes, pos := 402, limit := 427 }) := by cbv

theorem global1_decoded :
    global { bytes := artifactBytes, pos := 402, limit := 427 } =
      .ok (Cache.raw.globals[1]!, { bytes := artifactBytes, pos := 407, limit := 427 }) := by cbv

theorem global2_decoded :
    global { bytes := artifactBytes, pos := 407, limit := 427 } =
      .ok (Cache.raw.globals[2]!, { bytes := artifactBytes, pos := 412, limit := 427 }) := by cbv

theorem global3_decoded :
    global { bytes := artifactBytes, pos := 412, limit := 427 } =
      .ok (Cache.raw.globals[3]!, { bytes := artifactBytes, pos := 417, limit := 427 }) := by cbv

theorem global4_decoded :
    global { bytes := artifactBytes, pos := 417, limit := 427 } =
      .ok (Cache.raw.globals[4]!, { bytes := artifactBytes, pos := 422, limit := 427 }) := by cbv

theorem global5_decoded :
    global { bytes := artifactBytes, pos := 422, limit := 427 } =
      .ok (Cache.raw.globals[5]!, { bytes := artifactBytes, pos := 427, limit := 427 }) := by cbv

theorem globals_tail6 :
    Internal.vectorLoop global 0 { bytes := artifactBytes, pos := 427, limit := 427 } =
      .ok (Cache.raw.globals.drop 6, { bytes := artifactBytes, pos := 427, limit := 427 }) := by rfl

theorem globals_tail5 :
    Internal.vectorLoop global 1 { bytes := artifactBytes, pos := 422, limit := 427 } =
      .ok (Cache.raw.globals.drop 5, { bytes := artifactBytes, pos := 427, limit := 427 }) := by
  exact vectorLoop_eq_cons global5_decoded globals_tail6

theorem globals_tail4 :
    Internal.vectorLoop global 2 { bytes := artifactBytes, pos := 417, limit := 427 } =
      .ok (Cache.raw.globals.drop 4, { bytes := artifactBytes, pos := 427, limit := 427 }) := by
  exact vectorLoop_eq_cons global4_decoded globals_tail5

theorem globals_tail3 :
    Internal.vectorLoop global 3 { bytes := artifactBytes, pos := 412, limit := 427 } =
      .ok (Cache.raw.globals.drop 3, { bytes := artifactBytes, pos := 427, limit := 427 }) := by
  exact vectorLoop_eq_cons global3_decoded globals_tail4

theorem globals_tail2 :
    Internal.vectorLoop global 4 { bytes := artifactBytes, pos := 407, limit := 427 } =
      .ok (Cache.raw.globals.drop 2, { bytes := artifactBytes, pos := 427, limit := 427 }) := by
  exact vectorLoop_eq_cons global2_decoded globals_tail3

theorem globals_tail1 :
    Internal.vectorLoop global 5 { bytes := artifactBytes, pos := 402, limit := 427 } =
      .ok (Cache.raw.globals.drop 1, { bytes := artifactBytes, pos := 427, limit := 427 }) := by
  exact vectorLoop_eq_cons global1_decoded globals_tail2

theorem globals_tail0 :
    Internal.vectorLoop global 6 { bytes := artifactBytes, pos := 396, limit := 427 } =
      .ok (Cache.raw.globals.drop 0, { bytes := artifactBytes, pos := 427, limit := 427 }) := by
  exact vectorLoop_eq_cons global0_decoded globals_tail1

theorem globals_vector_decoded :
    vector global { bytes := artifactBytes, pos := 395, limit := 427 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 427, limit := 427 }) := by
  refine vector_eq_of_parts (length := 6)
    (itemsStart := { bytes := artifactBytes, pos := 396, limit := 427 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact globals_tail0

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 394, limit := 19083 } = .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 427, limit := 19083 }) := by
  refine sized_eq_of_parts (size := 32)
    (payload := { bytes := artifactBytes, pos := 395, limit := 19083 }) (finish := { bytes := artifactBytes, pos := 427, limit := 427 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact globals_vector_decoded
  · rfl

#print axioms globals_section_decoded

end Project.Gpt2CachedStep.Artifact
