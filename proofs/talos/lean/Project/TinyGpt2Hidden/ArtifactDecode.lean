import Project.TinyGpt2Hidden.ArtifactSection1
import Project.TinyGpt2Hidden.ArtifactSection3
import Project.TinyGpt2Hidden.ArtifactSection5
import Project.TinyGpt2Hidden.ArtifactSection6
import Project.TinyGpt2Hidden.ArtifactSection7
import Project.TinyGpt2Hidden.ArtifactSection10
import Project.Artifact.Binary.SectionParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

def state1 : RawModule :=
  { (default : RawModule) with
    types := Cache.raw.types,
    sections := [.type] }

def state2 : RawModule :=
  { (default : RawModule) with
    types := Cache.raw.types,
    functionTypeIndices := Cache.raw.functionTypeIndices,
    sections := [.type, .function] }

def state3 : RawModule :=
  { (default : RawModule) with
    types := Cache.raw.types,
    functionTypeIndices := Cache.raw.functionTypeIndices,
    memories := Cache.raw.memories,
    sections := [.type, .function, .memory] }

def state4 : RawModule :=
  { (default : RawModule) with
    types := Cache.raw.types,
    functionTypeIndices := Cache.raw.functionTypeIndices,
    memories := Cache.raw.memories,
    globals := Cache.raw.globals,
    sections := [.type, .function, .memory, .global] }

def state5 : RawModule :=
  { (default : RawModule) with
    types := Cache.raw.types,
    functionTypeIndices := Cache.raw.functionTypeIndices,
    memories := Cache.raw.memories,
    globals := Cache.raw.globals,
    exports := Cache.raw.exports,
    sections := [.type, .function, .memory, .global, .export] }

theorem sections_from6 :
    sectionLoop 15992 6 Cache.raw { bytes := artifactBytes, pos := 16006, limit := 16006 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by rfl

theorem sections_from5 :
    sectionLoop 15993 5 state5 { bytes := artifactBytes, pos := 1057, limit := 16006 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  refine sectionLoop_eq_step (fuel := 15992) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 1058, limit := 16006 }) (next := { bytes := artifactBytes, pos := 16006, limit := 16006 })
    (parsed := { state5 with codes := Cache.raw.codes }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

theorem sections_from4 :
    sectionLoop 15994 4 state4 { bytes := artifactBytes, pos := 940, limit := 16006 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  refine sectionLoop_eq_step (fuel := 15993) (rawId := 7) (id := .export) (rank := 5)
    (payload := { bytes := artifactBytes, pos := 941, limit := 16006 }) (next := { bytes := artifactBytes, pos := 1057, limit := 16006 })
    (parsed := { state4 with exports := Cache.raw.exports }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_export_eq exports_section_decoded
  · exact sections_from5

theorem sections_from3 :
    sectionLoop 15995 3 state3 { bytes := artifactBytes, pos := 906, limit := 16006 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  refine sectionLoop_eq_step (fuel := 15994) (rawId := 6) (id := .global) (rank := 4)
    (payload := { bytes := artifactBytes, pos := 907, limit := 16006 }) (next := { bytes := artifactBytes, pos := 940, limit := 16006 })
    (parsed := { state3 with globals := Cache.raw.globals }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_global_eq globals_section_decoded
  · exact sections_from4

theorem sections_from2 :
    sectionLoop 15996 2 state2 { bytes := artifactBytes, pos := 901, limit := 16006 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  refine sectionLoop_eq_step (fuel := 15995) (rawId := 5) (id := .memory) (rank := 3)
    (payload := { bytes := artifactBytes, pos := 902, limit := 16006 }) (next := { bytes := artifactBytes, pos := 906, limit := 16006 })
    (parsed := { state2 with memories := Cache.raw.memories }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_memory_eq memories_section_decoded
  · exact sections_from3

theorem sections_from1 :
    sectionLoop 15997 1 state1 { bytes := artifactBytes, pos := 819, limit := 16006 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  refine sectionLoop_eq_step (fuel := 15996) (rawId := 3) (id := .function) (rank := 2)
    (payload := { bytes := artifactBytes, pos := 820, limit := 16006 }) (next := { bytes := artifactBytes, pos := 901, limit := 16006 })
    (parsed := { state1 with functionTypeIndices := Cache.raw.functionTypeIndices }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_function_eq functionTypeIndices_section_decoded
  · exact sections_from2

theorem sections_from0 :
    sectionLoop 15998 0 (default : RawModule) { bytes := artifactBytes, pos := 8, limit := 16006 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  refine sectionLoop_eq_step (fuel := 15997) (rawId := 1) (id := .type) (rank := 1)
    (payload := { bytes := artifactBytes, pos := 9, limit := 16006 }) (next := { bytes := artifactBytes, pos := 819, limit := 16006 })
    (parsed := { (default : RawModule) with types := Cache.raw.types }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_type_eq types_section_decoded
  · exact sections_from1

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := { bytes := artifactBytes, pos := 4, limit := 16006 }) (sectionsStart := { bytes := artifactBytes, pos := 8, limit := 16006 })
    (finish := { bytes := artifactBytes, pos := 16006, limit := 16006 }) ?_ ?_ sections_from0 rfl
  · cbv
  · cbv

#print axioms decode_eq_cache
end Project.TinyGpt2Hidden.Artifact
