import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactSection1
import Project.Beck.ArtifactSection3
import Project.Beck.ArtifactSection5
import Project.Beck.ArtifactSection6
import Project.Beck.ArtifactSection7
import Project.Beck.ArtifactSection10
import Project.Artifact.Binary.SectionParts

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

def state0 : RawModule := default

def state1 : RawModule :=
  { state0 with types := Cache.raw.types, sections := [.type] }

def state2 : RawModule :=
  { state1 with functionTypeIndices := Cache.raw.functionTypeIndices, sections := [.type, .function] }

def state3 : RawModule :=
  { state2 with memories := Cache.raw.memories, sections := [.type, .function, .memory] }

def state4 : RawModule :=
  { state3 with globals := Cache.raw.globals, sections := [.type, .function, .memory, .global] }

def state5 : RawModule :=
  { state4 with exports := Cache.raw.exports, sections := [.type, .function, .memory, .global, .export] }

def state6 : RawModule :=
  { state5 with codes := Cache.raw.codes, sections := [.type, .function, .memory, .global, .export, .code] }

theorem sections_from6 :
    sectionLoop 27054 6 state6 { bytes := artifactBytes, pos := 27068, limit := 27068 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by rfl

theorem sections_from5 :
    sectionLoop 27055 5 state5 { bytes := artifactBytes, pos := 619, limit := 27068 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  refine sectionLoop_eq_step (fuel := 27054) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 620, limit := 27068 }) (next := { bytes := artifactBytes, pos := 27068, limit := 27068 })
    (parsed := { state5 with codes := Cache.raw.codes }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

theorem sections_from4 :
    sectionLoop 27056 4 state4 { bytes := artifactBytes, pos := 501, limit := 27068 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  refine sectionLoop_eq_step (fuel := 27055) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 502, limit := 27068 }) (next := { bytes := artifactBytes, pos := 619, limit := 27068 })
    (parsed := { state4 with exports := Cache.raw.exports }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_export_eq exports_section_decoded
  · exact sections_from5

theorem sections_from3 :
    sectionLoop 27057 3 state3 { bytes := artifactBytes, pos := 467, limit := 27068 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  refine sectionLoop_eq_step (fuel := 27056) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 468, limit := 27068 }) (next := { bytes := artifactBytes, pos := 501, limit := 27068 })
    (parsed := { state3 with globals := Cache.raw.globals }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_global_eq globals_section_decoded
  · exact sections_from4

theorem sections_from2 :
    sectionLoop 27058 2 state2 { bytes := artifactBytes, pos := 462, limit := 27068 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  refine sectionLoop_eq_step (fuel := 27057) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 463, limit := 27068 }) (next := { bytes := artifactBytes, pos := 467, limit := 27068 })
    (parsed := { state2 with memories := Cache.raw.memories }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_memory_eq memories_section_decoded
  · exact sections_from3

theorem sections_from1 :
    sectionLoop 27059 1 state1 { bytes := artifactBytes, pos := 419, limit := 27068 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  refine sectionLoop_eq_step (fuel := 27058) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 420, limit := 27068 }) (next := { bytes := artifactBytes, pos := 462, limit := 27068 })
    (parsed := { state1 with functionTypeIndices := Cache.raw.functionTypeIndices }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_function_eq functionTypeIndices_section_decoded
  · exact sections_from2

theorem sections_from0 :
    sectionLoop 27060 0 state0 { bytes := artifactBytes, pos := 8, limit := 27068 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  refine sectionLoop_eq_step (fuel := 27059) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 27068 }) (next := { bytes := artifactBytes, pos := 419, limit := 27068 })
    (parsed := { state0 with types := Cache.raw.types }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_type_eq types_section_decoded
  · exact sections_from1

theorem decode_eq_cache_parts : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := { bytes := artifactBytes, pos := 4, limit := 27068 })
    (sectionsStart := { bytes := artifactBytes, pos := 8, limit := 27068 }) (finish := { bytes := artifactBytes, pos := 27068, limit := 27068 }) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · exact sections_from0
  · rfl

#print axioms decode_eq_cache_parts

end Project.Beck.Artifact
