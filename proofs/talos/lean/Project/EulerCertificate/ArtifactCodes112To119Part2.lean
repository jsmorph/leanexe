import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes112To119Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code117_seq_117_tail0_decoded :
    instructionSequenceAt 663 false { bytes := artifactBytes, pos := 26230, limit := 26893 } =
      .ok ((((Cache.raw.codes[117]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26893, limit := 26893 }) := by
  cbv

theorem code117_decoded :
    code { bytes := artifactBytes, pos := 26225, limit := 45644 } =
      .ok (Cache.raw.codes[117]!, { bytes := artifactBytes, pos := 26893, limit := 45644 }) := by
  refine code_eq_of_parts (size := 666)
    (payload := { bytes := artifactBytes, pos := 26227, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 26230, limit := 26893 })
    (bodyFinish := { bytes := artifactBytes, pos := 26893, limit := 26893 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code117_seq_117_tail0_decoded
  · rfl

#print axioms code117_decoded

@[cbv_eval] theorem code118_seq_118_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 26897, limit := 26904 } =
      .ok ((((Cache.raw.codes[118]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26904, limit := 26904 }) := by
  cbv

theorem code118_decoded :
    code { bytes := artifactBytes, pos := 26893, limit := 45644 } =
      .ok (Cache.raw.codes[118]!, { bytes := artifactBytes, pos := 26904, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 26894, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 26897, limit := 26904 })
    (bodyFinish := { bytes := artifactBytes, pos := 26904, limit := 26904 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code118_seq_118_tail0_decoded
  · rfl

#print axioms code118_decoded

@[cbv_eval] theorem code119_seq_119_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 26908, limit := 26946 } =
      .ok ((((Cache.raw.codes[119]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26946, limit := 26946 }) := by
  cbv

theorem code119_decoded :
    code { bytes := artifactBytes, pos := 26904, limit := 45644 } =
      .ok (Cache.raw.codes[119]!, { bytes := artifactBytes, pos := 26946, limit := 45644 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 26905, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 26908, limit := 26946 })
    (bodyFinish := { bytes := artifactBytes, pos := 26946, limit := 26946 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code119_seq_119_tail0_decoded
  · rfl

#print axioms code119_decoded

end Project.EulerCertificate.Artifact
