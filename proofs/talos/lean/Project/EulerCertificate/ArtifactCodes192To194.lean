import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code192_seq_192_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 45182, limit := 45208 } =
      .ok ((((Cache.raw.codes[192]!).body).drop 0, .end), { bytes := artifactBytes, pos := 45208, limit := 45208 }) := by
  cbv

theorem code192_decoded :
    code { bytes := artifactBytes, pos := 45180, limit := 45644 } =
      .ok (Cache.raw.codes[192]!, { bytes := artifactBytes, pos := 45208, limit := 45644 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 45181, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 45182, limit := 45208 })
    (bodyFinish := { bytes := artifactBytes, pos := 45208, limit := 45208 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code192_seq_192_tail0_decoded
  · rfl

#print axioms code192_decoded

@[cbv_eval] theorem code193_seq_193_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 45212, limit := 45289 } =
      .ok ((((Cache.raw.codes[193]!).body).drop 0, .end), { bytes := artifactBytes, pos := 45289, limit := 45289 }) := by
  cbv

theorem code193_decoded :
    code { bytes := artifactBytes, pos := 45208, limit := 45644 } =
      .ok (Cache.raw.codes[193]!, { bytes := artifactBytes, pos := 45289, limit := 45644 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 45209, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 45212, limit := 45289 })
    (bodyFinish := { bytes := artifactBytes, pos := 45289, limit := 45289 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code193_seq_193_tail0_decoded
  · rfl

#print axioms code193_decoded

@[cbv_eval] theorem code194_seq_194_tail43_decoded :
    instructionSequenceAt 307 false { bytes := artifactBytes, pos := 45483, limit := 45644 } =
      .ok ((((Cache.raw.codes[194]!).body).drop 43, .end), { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  cbv

@[cbv_eval] theorem code194_seq_194_tail26_decoded :
    instructionSequenceAt 324 false { bytes := artifactBytes, pos := 45355, limit := 45644 } =
      .ok ((((Cache.raw.codes[194]!).body).drop 26, .end), { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  cbv

@[cbv_eval] theorem code194_seq_194_tail0_decoded :
    instructionSequenceAt 350 false { bytes := artifactBytes, pos := 45294, limit := 45644 } =
      .ok ((((Cache.raw.codes[194]!).body).drop 0, .end), { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  cbv

theorem code194_decoded :
    code { bytes := artifactBytes, pos := 45289, limit := 45644 } =
      .ok (Cache.raw.codes[194]!, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  refine code_eq_of_parts (size := 353)
    (payload := { bytes := artifactBytes, pos := 45291, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 45294, limit := 45644 })
    (bodyFinish := { bytes := artifactBytes, pos := 45644, limit := 45644 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code194_seq_194_tail0_decoded
  · rfl

#print axioms code194_decoded

end Project.EulerCertificate.Artifact
