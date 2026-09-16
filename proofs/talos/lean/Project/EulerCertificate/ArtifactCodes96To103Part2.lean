import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes96To103Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code101_seq_101_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 23699, limit := 23778 } =
      .ok ((((Cache.raw.codes[101]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23778, limit := 23778 }) := by
  cbv

theorem code101_decoded :
    code { bytes := artifactBytes, pos := 23695, limit := 45644 } =
      .ok (Cache.raw.codes[101]!, { bytes := artifactBytes, pos := 23778, limit := 45644 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 23696, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 23699, limit := 23778 })
    (bodyFinish := { bytes := artifactBytes, pos := 23778, limit := 23778 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code101_seq_101_tail0_decoded
  · rfl

#print axioms code101_decoded

@[cbv_eval] theorem code102_seq_102_tail0_decoded :
    instructionSequenceAt 104 false { bytes := artifactBytes, pos := 23782, limit := 23886 } =
      .ok ((((Cache.raw.codes[102]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23886, limit := 23886 }) := by
  cbv

theorem code102_decoded :
    code { bytes := artifactBytes, pos := 23778, limit := 45644 } =
      .ok (Cache.raw.codes[102]!, { bytes := artifactBytes, pos := 23886, limit := 45644 }) := by
  refine code_eq_of_parts (size := 107)
    (payload := { bytes := artifactBytes, pos := 23779, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 23782, limit := 23886 })
    (bodyFinish := { bytes := artifactBytes, pos := 23886, limit := 23886 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code102_seq_102_tail0_decoded
  · rfl

#print axioms code102_decoded

@[cbv_eval] theorem code103_seq_103_tail0_decoded :
    instructionSequenceAt 89 false { bytes := artifactBytes, pos := 23890, limit := 23979 } =
      .ok ((((Cache.raw.codes[103]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23979, limit := 23979 }) := by
  cbv

theorem code103_decoded :
    code { bytes := artifactBytes, pos := 23886, limit := 45644 } =
      .ok (Cache.raw.codes[103]!, { bytes := artifactBytes, pos := 23979, limit := 45644 }) := by
  refine code_eq_of_parts (size := 92)
    (payload := { bytes := artifactBytes, pos := 23887, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 23890, limit := 23979 })
    (bodyFinish := { bytes := artifactBytes, pos := 23979, limit := 23979 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code103_seq_103_tail0_decoded
  · rfl

#print axioms code103_decoded

end Project.EulerCertificate.Artifact
