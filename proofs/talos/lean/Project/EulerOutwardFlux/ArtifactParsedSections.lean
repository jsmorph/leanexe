import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardFlux.ArtifactParsedCode

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from4 :
    sectionLoop 7163 4 afterGlobals { bytes := artifactBytes, pos := 557, limit := 7175 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  refine sectionLoop_eq_step (fuel := 7162) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 558, limit := 7175 }) (next := { bytes := artifactBytes, pos := 683, limit := 7175 })
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
    sectionLoop 7164 3 afterMemory { bytes := artifactBytes, pos := 523, limit := 7175 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  refine sectionLoop_eq_step (fuel := 7163) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 524, limit := 7175 }) (next := { bytes := artifactBytes, pos := 557, limit := 7175 })
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
    sectionLoop 7165 2 afterFunctions { bytes := artifactBytes, pos := 518, limit := 7175 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  refine sectionLoop_eq_step (fuel := 7164) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 519, limit := 7175 }) (next := { bytes := artifactBytes, pos := 523, limit := 7175 })
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
    sectionLoop 7166 1 afterTypes { bytes := artifactBytes, pos := 456, limit := 7175 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  refine sectionLoop_eq_step (fuel := 7165) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 457, limit := 7175 }) (next := { bytes := artifactBytes, pos := 518, limit := 7175 })
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
    sectionLoop 7167 0 (default : RawModule) { bytes := artifactBytes, pos := 8, limit := 7175 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  refine sectionLoop_eq_step (fuel := 7166) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 7175 }) (next := { bytes := artifactBytes, pos := 456, limit := 7175 })
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

end Project.EulerOutwardFlux.Artifact
