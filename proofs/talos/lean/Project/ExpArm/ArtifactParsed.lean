import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactSection1
import Project.ExpArm.ArtifactSection3
import Project.ExpArm.ArtifactSection5
import Project.ExpArm.ArtifactSection6
import Project.ExpArm.ArtifactSection7
import Project.ExpArm.ArtifactSection10
import Project.ExpArm.ArtifactSection11
import Project.Artifact.Binary.SectionParts

namespace Project.ExpArm.Artifact
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

def state7 : RawModule :=
  { state6 with data := Cache.raw.data, sections := [.type, .function, .memory, .global, .export, .code, .data] }

theorem sections_from7 :
    sectionLoop 12718 7 state7 { bytes := artifactBytes, pos := 12733, limit := 12733 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by rfl

theorem sections_from6 :
    sectionLoop 12719 6 state6 { bytes := artifactBytes, pos := 10666, limit := 12733 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine sectionLoop_eq_step (fuel := 12718) (rawId := 11) (id := .data) (rank := 7)
    (payload := { bytes := artifactBytes, pos := 10667, limit := 12733 }) (next := { bytes := artifactBytes, pos := 12733, limit := 12733 })
    (parsed := { state6 with data := Cache.raw.data }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_data_eq data_section_decoded
  · exact sections_from7

theorem sections_from5 :
    sectionLoop 12720 5 state5 { bytes := artifactBytes, pos := 208, limit := 12733 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine sectionLoop_eq_step (fuel := 12719) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 209, limit := 12733 }) (next := { bytes := artifactBytes, pos := 10666, limit := 12733 })
    (parsed := { state5 with codes := Cache.raw.codes }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

theorem sections_from4 :
    sectionLoop 12721 4 state4 { bytes := artifactBytes, pos := 94, limit := 12733 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine sectionLoop_eq_step (fuel := 12720) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 95, limit := 12733 }) (next := { bytes := artifactBytes, pos := 208, limit := 12733 })
    (parsed := { state4 with exports := Cache.raw.exports }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_export_eq exports_section_decoded
  · exact sections_from5

theorem sections_from3 :
    sectionLoop 12722 3 state3 { bytes := artifactBytes, pos := 60, limit := 12733 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine sectionLoop_eq_step (fuel := 12721) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 61, limit := 12733 }) (next := { bytes := artifactBytes, pos := 94, limit := 12733 })
    (parsed := { state3 with globals := Cache.raw.globals }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_global_eq globals_section_decoded
  · exact sections_from4

theorem sections_from2 :
    sectionLoop 12723 2 state2 { bytes := artifactBytes, pos := 55, limit := 12733 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine sectionLoop_eq_step (fuel := 12722) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 56, limit := 12733 }) (next := { bytes := artifactBytes, pos := 60, limit := 12733 })
    (parsed := { state2 with memories := Cache.raw.memories }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_memory_eq memories_section_decoded
  · exact sections_from3

theorem sections_from1 :
    sectionLoop 12724 1 state1 { bytes := artifactBytes, pos := 45, limit := 12733 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine sectionLoop_eq_step (fuel := 12723) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 46, limit := 12733 }) (next := { bytes := artifactBytes, pos := 55, limit := 12733 })
    (parsed := { state1 with functionTypeIndices := Cache.raw.functionTypeIndices }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_function_eq functionTypeIndices_section_decoded
  · exact sections_from2

theorem sections_from0 :
    sectionLoop 12725 0 state0 { bytes := artifactBytes, pos := 8, limit := 12733 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine sectionLoop_eq_step (fuel := 12724) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 12733 }) (next := { bytes := artifactBytes, pos := 45, limit := 12733 })
    (parsed := { state0 with types := Cache.raw.types }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_type_eq types_section_decoded
  · exact sections_from1

theorem decode_eq_cache_parts : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := { bytes := artifactBytes, pos := 4, limit := 12733 })
    (sectionsStart := { bytes := artifactBytes, pos := 8, limit := 12733 }) (finish := { bytes := artifactBytes, pos := 12733, limit := 12733 }) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · exact sections_from0
  · rfl

#print axioms decode_eq_cache_parts

end Project.ExpArm.Artifact
