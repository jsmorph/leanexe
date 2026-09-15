import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardFaceStep.ArtifactParsedCode

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from4 :
    sectionLoop 9065 4 afterGlobals { bytes := artifactBytes, pos := 766, limit := 9077 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine sectionLoop_eq_step (fuel := 9064) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 767, limit := 9077 }) (next := { bytes := artifactBytes, pos := 897, limit := 9077 })
    (parsed := { afterGlobals with exports := Cache.raw.exports })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_export_eq exports_section_decoded
  · exact sections_from5

theorem sections_from3 :
    sectionLoop 9066 3 afterMemory { bytes := artifactBytes, pos := 732, limit := 9077 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine sectionLoop_eq_step (fuel := 9065) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 733, limit := 9077 }) (next := { bytes := artifactBytes, pos := 766, limit := 9077 })
    (parsed := { afterMemory with globals := Cache.raw.globals })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_global_eq globals_section_decoded
  · exact sections_from4

theorem sections_from2 :
    sectionLoop 9067 2 afterFunctions { bytes := artifactBytes, pos := 727, limit := 9077 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine sectionLoop_eq_step (fuel := 9066) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 728, limit := 9077 }) (next := { bytes := artifactBytes, pos := 732, limit := 9077 })
    (parsed := { afterFunctions with memories := Cache.raw.memories })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_memory_eq memories_section_decoded
  · exact sections_from3

theorem sections_from1 :
    sectionLoop 9068 1 afterTypes { bytes := artifactBytes, pos := 649, limit := 9077 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine sectionLoop_eq_step (fuel := 9067) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 650, limit := 9077 }) (next := { bytes := artifactBytes, pos := 727, limit := 9077 })
    (parsed := { afterTypes with functionTypeIndices := Cache.raw.functionTypeIndices })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_function_eq functionTypeIndices_section_decoded
  · exact sections_from2

theorem sections_from0 :
    sectionLoop 9069 0 (default : RawModule) { bytes := artifactBytes, pos := 8, limit := 9077 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine sectionLoop_eq_step (fuel := 9068) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 9077 }) (next := { bytes := artifactBytes, pos := 649, limit := 9077 })
    (parsed := { (default : RawModule) with types := Cache.raw.types })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_type_eq types_section_decoded
  · exact sections_from1

#print axioms sections_from0

end Project.EulerOutwardFaceStep.Artifact
