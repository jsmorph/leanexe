import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardGrid.ArtifactParsedCode

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from4 :
    sectionLoop 5716 4 afterGlobals { bytes := artifactBytes, pos := 456, limit := 5728 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine sectionLoop_eq_step (fuel := 5715) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 457, limit := 5728 }) (next := { bytes := artifactBytes, pos := 576, limit := 5728 })
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
    sectionLoop 5717 3 afterMemory { bytes := artifactBytes, pos := 422, limit := 5728 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine sectionLoop_eq_step (fuel := 5716) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 423, limit := 5728 }) (next := { bytes := artifactBytes, pos := 456, limit := 5728 })
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
    sectionLoop 5718 2 afterFunctions { bytes := artifactBytes, pos := 417, limit := 5728 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine sectionLoop_eq_step (fuel := 5717) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 418, limit := 5728 }) (next := { bytes := artifactBytes, pos := 422, limit := 5728 })
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
    sectionLoop 5719 1 afterTypes { bytes := artifactBytes, pos := 364, limit := 5728 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine sectionLoop_eq_step (fuel := 5718) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 365, limit := 5728 }) (next := { bytes := artifactBytes, pos := 417, limit := 5728 })
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
    sectionLoop 5720 0 (default : RawModule) { bytes := artifactBytes, pos := 8, limit := 5728 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine sectionLoop_eq_step (fuel := 5719) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 5728 }) (next := { bytes := artifactBytes, pos := 364, limit := 5728 })
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

end Project.EulerOutwardGrid.Artifact
