import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardMaximum.ArtifactParsedCode

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from4 :
    sectionLoop 5248 4 afterGlobals { bytes := artifactBytes, pos := 423, limit := 5260 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  refine sectionLoop_eq_step (fuel := 5247) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 424, limit := 5260 }) (next := { bytes := artifactBytes, pos := 548, limit := 5260 })
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
    sectionLoop 5249 3 afterMemory { bytes := artifactBytes, pos := 389, limit := 5260 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  refine sectionLoop_eq_step (fuel := 5248) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 390, limit := 5260 }) (next := { bytes := artifactBytes, pos := 423, limit := 5260 })
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
    sectionLoop 5250 2 afterFunctions { bytes := artifactBytes, pos := 384, limit := 5260 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  refine sectionLoop_eq_step (fuel := 5249) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 385, limit := 5260 }) (next := { bytes := artifactBytes, pos := 389, limit := 5260 })
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
    sectionLoop 5251 1 afterTypes { bytes := artifactBytes, pos := 334, limit := 5260 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  refine sectionLoop_eq_step (fuel := 5250) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 335, limit := 5260 }) (next := { bytes := artifactBytes, pos := 384, limit := 5260 })
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
    sectionLoop 5252 0 (default : RawModule) { bytes := artifactBytes, pos := 8, limit := 5260 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  refine sectionLoop_eq_step (fuel := 5251) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 5260 }) (next := { bytes := artifactBytes, pos := 334, limit := 5260 })
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

end Project.EulerOutwardMaximum.Artifact
