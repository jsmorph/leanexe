import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactSection1
import Project.Gpt2QuantizedCached.ArtifactSection3
import Project.Gpt2QuantizedCached.ArtifactSection5
import Project.Gpt2QuantizedCached.ArtifactSection6
import Project.Gpt2QuantizedCached.ArtifactSection7
import Project.Gpt2QuantizedCached.ArtifactSection10
import Project.Artifact.Binary.SectionParts

namespace Project.Gpt2QuantizedCached.Artifact
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
    sectionLoop 28301 6 state6 { bytes := artifactBytes, pos := 28315, limit := 28315 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by rfl

theorem sections_from5 :
    sectionLoop 28302 5 state5 { bytes := artifactBytes, pos := 780, limit := 28315 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  refine sectionLoop_eq_step (fuel := 28301) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 781, limit := 28315 }) (next := { bytes := artifactBytes, pos := 28315, limit := 28315 })
    (parsed := { state5 with codes := Cache.raw.codes }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

theorem sections_from4 :
    sectionLoop 28303 4 state4 { bytes := artifactBytes, pos := 642, limit := 28315 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  refine sectionLoop_eq_step (fuel := 28302) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 643, limit := 28315 }) (next := { bytes := artifactBytes, pos := 780, limit := 28315 })
    (parsed := { state4 with exports := Cache.raw.exports }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_export_eq exports_section_decoded
  · exact sections_from5

theorem sections_from3 :
    sectionLoop 28304 3 state3 { bytes := artifactBytes, pos := 608, limit := 28315 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  refine sectionLoop_eq_step (fuel := 28303) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 609, limit := 28315 }) (next := { bytes := artifactBytes, pos := 642, limit := 28315 })
    (parsed := { state3 with globals := Cache.raw.globals }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_global_eq globals_section_decoded
  · exact sections_from4

theorem sections_from2 :
    sectionLoop 28305 2 state2 { bytes := artifactBytes, pos := 603, limit := 28315 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  refine sectionLoop_eq_step (fuel := 28304) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 604, limit := 28315 }) (next := { bytes := artifactBytes, pos := 608, limit := 28315 })
    (parsed := { state2 with memories := Cache.raw.memories }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_memory_eq memories_section_decoded
  · exact sections_from3

theorem sections_from1 :
    sectionLoop 28306 1 state1 { bytes := artifactBytes, pos := 534, limit := 28315 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  refine sectionLoop_eq_step (fuel := 28305) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 535, limit := 28315 }) (next := { bytes := artifactBytes, pos := 603, limit := 28315 })
    (parsed := { state1 with functionTypeIndices := Cache.raw.functionTypeIndices }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_function_eq functionTypeIndices_section_decoded
  · exact sections_from2

theorem sections_from0 :
    sectionLoop 28307 0 state0 { bytes := artifactBytes, pos := 8, limit := 28315 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  refine sectionLoop_eq_step (fuel := 28306) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 28315 }) (next := { bytes := artifactBytes, pos := 534, limit := 28315 })
    (parsed := { state0 with types := Cache.raw.types }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_type_eq types_section_decoded
  · exact sections_from1

theorem decode_eq_cache_parts : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := { bytes := artifactBytes, pos := 4, limit := 28315 })
    (sectionsStart := { bytes := artifactBytes, pos := 8, limit := 28315 }) (finish := { bytes := artifactBytes, pos := 28315, limit := 28315 }) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · exact sections_from0
  · rfl

#print axioms decode_eq_cache_parts

end Project.Gpt2QuantizedCached.Artifact
