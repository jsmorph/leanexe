import Project.EulerOutwardCfl.ArtifactByteLookup
import Project.EulerOutwardCfl.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardCfl.ArtifactParsedCode

namespace Project.EulerOutwardCfl.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from4 :
    sectionLoop 2545 4 afterGlobals { bytes := artifactBytes, pos := 188, limit := 2557 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine sectionLoop_eq_step (fuel := 2544) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 189, limit := 2557 }) (next := { bytes := artifactBytes, pos := 315, limit := 2557 })
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
    sectionLoop 2546 3 afterMemory { bytes := artifactBytes, pos := 154, limit := 2557 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine sectionLoop_eq_step (fuel := 2545) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 155, limit := 2557 }) (next := { bytes := artifactBytes, pos := 188, limit := 2557 })
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
    sectionLoop 2547 2 afterFunctions { bytes := artifactBytes, pos := 149, limit := 2557 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine sectionLoop_eq_step (fuel := 2546) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 150, limit := 2557 }) (next := { bytes := artifactBytes, pos := 154, limit := 2557 })
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
    sectionLoop 2548 1 afterTypes { bytes := artifactBytes, pos := 126, limit := 2557 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine sectionLoop_eq_step (fuel := 2547) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 127, limit := 2557 }) (next := { bytes := artifactBytes, pos := 149, limit := 2557 })
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
    sectionLoop 2549 0 (default : RawModule) { bytes := artifactBytes, pos := 8, limit := 2557 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine sectionLoop_eq_step (fuel := 2548) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 2557 }) (next := { bytes := artifactBytes, pos := 126, limit := 2557 })
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

end Project.EulerOutwardCfl.Artifact
