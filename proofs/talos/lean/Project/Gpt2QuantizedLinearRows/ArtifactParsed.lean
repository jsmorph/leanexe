import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedLinearRows.ArtifactSection1
import Project.Gpt2QuantizedLinearRows.ArtifactSection3
import Project.Gpt2QuantizedLinearRows.ArtifactSection5
import Project.Gpt2QuantizedLinearRows.ArtifactSection6
import Project.Gpt2QuantizedLinearRows.ArtifactSection7
import Project.Gpt2QuantizedLinearRows.ArtifactSection10
import Project.Artifact.Binary.SectionParts

namespace Project.Gpt2QuantizedLinearRows.Artifact
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
    sectionLoop 4727 6 state6 { bytes := artifactBytes, pos := 4741, limit := 4741 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4741, limit := 4741 }) := by rfl

theorem sections_from5 :
    sectionLoop 4728 5 state5 { bytes := artifactBytes, pos := 301, limit := 4741 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4741, limit := 4741 }) := by
  refine sectionLoop_eq_step (fuel := 4727) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 302, limit := 4741 }) (next := { bytes := artifactBytes, pos := 4741, limit := 4741 })
    (parsed := { state5 with codes := Cache.raw.codes }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

theorem sections_from4 :
    sectionLoop 4729 4 state4 { bytes := artifactBytes, pos := 180, limit := 4741 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4741, limit := 4741 }) := by
  refine sectionLoop_eq_step (fuel := 4728) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 181, limit := 4741 }) (next := { bytes := artifactBytes, pos := 301, limit := 4741 })
    (parsed := { state4 with exports := Cache.raw.exports }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_export_eq exports_section_decoded
  · exact sections_from5

theorem sections_from3 :
    sectionLoop 4730 3 state3 { bytes := artifactBytes, pos := 146, limit := 4741 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4741, limit := 4741 }) := by
  refine sectionLoop_eq_step (fuel := 4729) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 147, limit := 4741 }) (next := { bytes := artifactBytes, pos := 180, limit := 4741 })
    (parsed := { state3 with globals := Cache.raw.globals }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_global_eq globals_section_decoded
  · exact sections_from4

theorem sections_from2 :
    sectionLoop 4731 2 state2 { bytes := artifactBytes, pos := 141, limit := 4741 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4741, limit := 4741 }) := by
  refine sectionLoop_eq_step (fuel := 4730) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 142, limit := 4741 }) (next := { bytes := artifactBytes, pos := 146, limit := 4741 })
    (parsed := { state2 with memories := Cache.raw.memories }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_memory_eq memories_section_decoded
  · exact sections_from3

theorem sections_from1 :
    sectionLoop 4732 1 state1 { bytes := artifactBytes, pos := 125, limit := 4741 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4741, limit := 4741 }) := by
  refine sectionLoop_eq_step (fuel := 4731) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 126, limit := 4741 }) (next := { bytes := artifactBytes, pos := 141, limit := 4741 })
    (parsed := { state1 with functionTypeIndices := Cache.raw.functionTypeIndices }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_function_eq functionTypeIndices_section_decoded
  · exact sections_from2

theorem sections_from0 :
    sectionLoop 4733 0 state0 { bytes := artifactBytes, pos := 8, limit := 4741 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 4741, limit := 4741 }) := by
  refine sectionLoop_eq_step (fuel := 4732) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 4741 }) (next := { bytes := artifactBytes, pos := 125, limit := 4741 })
    (parsed := { state0 with types := Cache.raw.types }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_type_eq types_section_decoded
  · exact sections_from1

theorem decode_eq_cache_parts : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := { bytes := artifactBytes, pos := 4, limit := 4741 })
    (sectionsStart := { bytes := artifactBytes, pos := 8, limit := 4741 }) (finish := { bytes := artifactBytes, pos := 4741, limit := 4741 }) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · exact sections_from0
  · rfl

#print axioms decode_eq_cache_parts

end Project.Gpt2QuantizedLinearRows.Artifact
