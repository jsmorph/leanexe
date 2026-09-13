import Project.EulerRiemann.ArtifactParsedCode

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072

theorem sections_from4 :
    sectionLoop 21755 4 afterGlobals { bytes := artifactBytes, pos := 1173, limit := 21767 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine sectionLoop_eq_step (fuel := 21754) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 1174, limit := 21767 }) (next := { bytes := artifactBytes, pos := 1289, limit := 21767 })
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
    sectionLoop 21756 3 afterMemory { bytes := artifactBytes, pos := 1139, limit := 21767 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine sectionLoop_eq_step (fuel := 21755) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 1140, limit := 21767 }) (next := { bytes := artifactBytes, pos := 1173, limit := 21767 })
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
    sectionLoop 21757 2 afterFunctions { bytes := artifactBytes, pos := 1134, limit := 21767 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine sectionLoop_eq_step (fuel := 21756) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 1135, limit := 21767 }) (next := { bytes := artifactBytes, pos := 1139, limit := 21767 })
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
    sectionLoop 21758 1 afterTypes { bytes := artifactBytes, pos := 1023, limit := 21767 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine sectionLoop_eq_step (fuel := 21757) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 1024, limit := 21767 }) (next := { bytes := artifactBytes, pos := 1134, limit := 21767 })
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
    sectionLoop 21759 0 (default : RawModule) { bytes := artifactBytes, pos := 8, limit := 21767 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine sectionLoop_eq_step (fuel := 21758) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 21767 }) (next := { bytes := artifactBytes, pos := 1023, limit := 21767 })
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

end Project.EulerRiemann.Artifact
