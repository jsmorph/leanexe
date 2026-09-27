import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2CachedStep.ArtifactSection1
import Project.Gpt2CachedStep.ArtifactSection3
import Project.Gpt2CachedStep.ArtifactSection5
import Project.Gpt2CachedStep.ArtifactSection6
import Project.Gpt2CachedStep.ArtifactSection7
import Project.Gpt2CachedStep.ArtifactSection10
import Project.Artifact.Binary.SectionParts

namespace Project.Gpt2CachedStep.Artifact
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
    sectionLoop 19069 6 state6 { bytes := artifactBytes, pos := 19083, limit := 19083 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by rfl

theorem sections_from5 :
    sectionLoop 19070 5 state5 { bytes := artifactBytes, pos := 548, limit := 19083 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine sectionLoop_eq_step (fuel := 19069) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 549, limit := 19083 }) (next := { bytes := artifactBytes, pos := 19083, limit := 19083 })
    (parsed := { state5 with codes := Cache.raw.codes }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

theorem sections_from4 :
    sectionLoop 19071 4 state4 { bytes := artifactBytes, pos := 427, limit := 19083 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine sectionLoop_eq_step (fuel := 19070) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 428, limit := 19083 }) (next := { bytes := artifactBytes, pos := 548, limit := 19083 })
    (parsed := { state4 with exports := Cache.raw.exports }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_export_eq exports_section_decoded
  · exact sections_from5

theorem sections_from3 :
    sectionLoop 19072 3 state3 { bytes := artifactBytes, pos := 393, limit := 19083 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine sectionLoop_eq_step (fuel := 19071) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 394, limit := 19083 }) (next := { bytes := artifactBytes, pos := 427, limit := 19083 })
    (parsed := { state3 with globals := Cache.raw.globals }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_global_eq globals_section_decoded
  · exact sections_from4

theorem sections_from2 :
    sectionLoop 19073 2 state2 { bytes := artifactBytes, pos := 388, limit := 19083 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine sectionLoop_eq_step (fuel := 19072) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 389, limit := 19083 }) (next := { bytes := artifactBytes, pos := 393, limit := 19083 })
    (parsed := { state2 with memories := Cache.raw.memories }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_memory_eq memories_section_decoded
  · exact sections_from3

theorem sections_from1 :
    sectionLoop 19074 1 state1 { bytes := artifactBytes, pos := 342, limit := 19083 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine sectionLoop_eq_step (fuel := 19073) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 343, limit := 19083 }) (next := { bytes := artifactBytes, pos := 388, limit := 19083 })
    (parsed := { state1 with functionTypeIndices := Cache.raw.functionTypeIndices }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_function_eq functionTypeIndices_section_decoded
  · exact sections_from2

theorem sections_from0 :
    sectionLoop 19075 0 state0 { bytes := artifactBytes, pos := 8, limit := 19083 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine sectionLoop_eq_step (fuel := 19074) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 19083 }) (next := { bytes := artifactBytes, pos := 342, limit := 19083 })
    (parsed := { state0 with types := Cache.raw.types }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_type_eq types_section_decoded
  · exact sections_from1

theorem decode_eq_cache_parts : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := { bytes := artifactBytes, pos := 4, limit := 19083 })
    (sectionsStart := { bytes := artifactBytes, pos := 8, limit := 19083 }) (finish := { bytes := artifactBytes, pos := 19083, limit := 19083 }) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · exact sections_from0
  · rfl

#print axioms decode_eq_cache_parts

end Project.Gpt2CachedStep.Artifact
