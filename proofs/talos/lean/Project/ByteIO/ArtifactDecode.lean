import Project.ByteIO.ArtifactSections
import Project.ByteIO.ArtifactSection10
import Project.ByteIO.BinaryParts

namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes
set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_parsed :
    Binary.parseSection 10 code { bytes, pos := 368, limit := 2082 } =
      .ok (raw.core.codes, { bytes, pos := 2082, limit := 2082 }) := by
  refine Binary.parseSection_eq_of_parts
    (payload := { bytes, pos := 369, limit := 2082 }) ?_ codes_section_decoded
  cbv

attribute [local cbv_eval] types_parsed imports_parsed functions_parsed
  memories_parsed globals_parsed exports_parsed codes_parsed
attribute [local cbv_opaque] Binary.parseSection

theorem decoded : Binary.decode bytes = .ok raw := by cbv

theorem encoded : Binary.Grammar.ModuleBytes bytes.data.toList raw :=
  Binary.decode_sound decoded

#print axioms decoded
#print axioms encoded

end Project.ByteIO.Artifact
