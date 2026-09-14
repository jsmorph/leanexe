import Project.EulerOutwardSpeed.ArtifactParsedCode

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072

theorem sections_from4 :
    sectionLoop 4924 4 afterGlobals { bytes := artifactBytes, pos := 363, limit := 4936 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  refine sectionLoop_eq_step (fuel := 4923) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 364, limit := 4936 }) (next := { bytes := artifactBytes, pos := 484, limit := 4936 })
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
    sectionLoop 4925 3 afterMemory { bytes := artifactBytes, pos := 329, limit := 4936 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  refine sectionLoop_eq_step (fuel := 4924) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 330, limit := 4936 }) (next := { bytes := artifactBytes, pos := 363, limit := 4936 })
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
    sectionLoop 4926 2 afterFunctions { bytes := artifactBytes, pos := 324, limit := 4936 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  refine sectionLoop_eq_step (fuel := 4925) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 325, limit := 4936 }) (next := { bytes := artifactBytes, pos := 329, limit := 4936 })
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
    sectionLoop 4927 1 afterTypes { bytes := artifactBytes, pos := 280, limit := 4936 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  refine sectionLoop_eq_step (fuel := 4926) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 281, limit := 4936 }) (next := { bytes := artifactBytes, pos := 324, limit := 4936 })
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
    sectionLoop 4928 0 (default : RawModule) { bytes := artifactBytes, pos := 8, limit := 4936 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  refine sectionLoop_eq_step (fuel := 4927) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 4936 }) (next := { bytes := artifactBytes, pos := 280, limit := 4936 })
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

end Project.EulerOutwardSpeed.Artifact
