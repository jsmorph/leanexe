import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code72_seq_72_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 8617, limit := 8643 } =
      .ok ((((Cache.raw.codes[72]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8643, limit := 8643 }) := by
  cbv

theorem code72_decoded :
    code { bytes := artifactBytes, pos := 8615, limit := 9077 } =
      .ok (Cache.raw.codes[72]!, { bytes := artifactBytes, pos := 8643, limit := 9077 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 8616, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 8617, limit := 8643 })
    (bodyFinish := { bytes := artifactBytes, pos := 8643, limit := 8643 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code72_seq_72_tail0_decoded
  · rfl

#print axioms code72_decoded

@[cbv_eval] theorem code73_seq_73_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 8647, limit := 8724 } =
      .ok ((((Cache.raw.codes[73]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8724, limit := 8724 }) := by
  cbv

theorem code73_decoded :
    code { bytes := artifactBytes, pos := 8643, limit := 9077 } =
      .ok (Cache.raw.codes[73]!, { bytes := artifactBytes, pos := 8724, limit := 9077 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 8644, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 8647, limit := 8724 })
    (bodyFinish := { bytes := artifactBytes, pos := 8724, limit := 8724 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code73_seq_73_tail0_decoded
  · rfl

#print axioms code73_decoded

@[cbv_eval] theorem code74_seq_74_tail44_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 9043, limit := 9077 } =
      .ok ((((Cache.raw.codes[74]!).body).drop 44, .end), { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_tail42_decoded :
    instructionSequenceAt 306 false { bytes := artifactBytes, pos := 8916, limit := 9077 } =
      .ok ((((Cache.raw.codes[74]!).body).drop 42, .end), { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_tail25_decoded :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 8788, limit := 9077 } =
      .ok ((((Cache.raw.codes[74]!).body).drop 25, .end), { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_tail0_decoded :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 8729, limit := 9077 } =
      .ok ((((Cache.raw.codes[74]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  cbv

theorem code74_decoded :
    code { bytes := artifactBytes, pos := 8724, limit := 9077 } =
      .ok (Cache.raw.codes[74]!, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 8726, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 8729, limit := 9077 })
    (bodyFinish := { bytes := artifactBytes, pos := 9077, limit := 9077 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code74_seq_74_tail0_decoded
  · rfl

#print axioms code74_decoded


end Project.EulerOutwardFaceStep.Artifact
