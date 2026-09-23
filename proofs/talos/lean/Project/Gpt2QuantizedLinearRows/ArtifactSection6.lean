import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem global0_decoded :
    global { bytes := artifactBytes, pos := 149, limit := 180 } =
      .ok (Cache.raw.globals[0]!, { bytes := artifactBytes, pos := 155, limit := 180 }) := by cbv

theorem global1_decoded :
    global { bytes := artifactBytes, pos := 155, limit := 180 } =
      .ok (Cache.raw.globals[1]!, { bytes := artifactBytes, pos := 160, limit := 180 }) := by cbv

theorem global2_decoded :
    global { bytes := artifactBytes, pos := 160, limit := 180 } =
      .ok (Cache.raw.globals[2]!, { bytes := artifactBytes, pos := 165, limit := 180 }) := by cbv

theorem global3_decoded :
    global { bytes := artifactBytes, pos := 165, limit := 180 } =
      .ok (Cache.raw.globals[3]!, { bytes := artifactBytes, pos := 170, limit := 180 }) := by cbv

theorem global4_decoded :
    global { bytes := artifactBytes, pos := 170, limit := 180 } =
      .ok (Cache.raw.globals[4]!, { bytes := artifactBytes, pos := 175, limit := 180 }) := by cbv

theorem global5_decoded :
    global { bytes := artifactBytes, pos := 175, limit := 180 } =
      .ok (Cache.raw.globals[5]!, { bytes := artifactBytes, pos := 180, limit := 180 }) := by cbv

theorem globals_tail6 :
    Internal.vectorLoop global 0 { bytes := artifactBytes, pos := 180, limit := 180 } =
      .ok (Cache.raw.globals.drop 6, { bytes := artifactBytes, pos := 180, limit := 180 }) := by rfl

theorem globals_tail5 :
    Internal.vectorLoop global 1 { bytes := artifactBytes, pos := 175, limit := 180 } =
      .ok (Cache.raw.globals.drop 5, { bytes := artifactBytes, pos := 180, limit := 180 }) := by
  exact vectorLoop_eq_cons global5_decoded globals_tail6

theorem globals_tail4 :
    Internal.vectorLoop global 2 { bytes := artifactBytes, pos := 170, limit := 180 } =
      .ok (Cache.raw.globals.drop 4, { bytes := artifactBytes, pos := 180, limit := 180 }) := by
  exact vectorLoop_eq_cons global4_decoded globals_tail5

theorem globals_tail3 :
    Internal.vectorLoop global 3 { bytes := artifactBytes, pos := 165, limit := 180 } =
      .ok (Cache.raw.globals.drop 3, { bytes := artifactBytes, pos := 180, limit := 180 }) := by
  exact vectorLoop_eq_cons global3_decoded globals_tail4

theorem globals_tail2 :
    Internal.vectorLoop global 4 { bytes := artifactBytes, pos := 160, limit := 180 } =
      .ok (Cache.raw.globals.drop 2, { bytes := artifactBytes, pos := 180, limit := 180 }) := by
  exact vectorLoop_eq_cons global2_decoded globals_tail3

theorem globals_tail1 :
    Internal.vectorLoop global 5 { bytes := artifactBytes, pos := 155, limit := 180 } =
      .ok (Cache.raw.globals.drop 1, { bytes := artifactBytes, pos := 180, limit := 180 }) := by
  exact vectorLoop_eq_cons global1_decoded globals_tail2

theorem globals_tail0 :
    Internal.vectorLoop global 6 { bytes := artifactBytes, pos := 149, limit := 180 } =
      .ok (Cache.raw.globals.drop 0, { bytes := artifactBytes, pos := 180, limit := 180 }) := by
  exact vectorLoop_eq_cons global0_decoded globals_tail1

theorem globals_vector_decoded :
    vector global { bytes := artifactBytes, pos := 148, limit := 180 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 180, limit := 180 }) := by
  refine vector_eq_of_parts (length := 6)
    (itemsStart := { bytes := artifactBytes, pos := 149, limit := 180 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact globals_tail0

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 147, limit := 4757 } = .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 180, limit := 4757 }) := by
  refine sized_eq_of_parts (size := 32)
    (payload := { bytes := artifactBytes, pos := 148, limit := 4757 }) (finish := { bytes := artifactBytes, pos := 180, limit := 180 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact globals_vector_decoded
  · rfl

#print axioms globals_section_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
