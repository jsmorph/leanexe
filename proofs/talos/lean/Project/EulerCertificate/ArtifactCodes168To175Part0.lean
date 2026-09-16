import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code168_seq_168_tail91_decoded :
    instructionSequenceAt 229 false { bytes := artifactBytes, pos := 34769, limit := 34897 } =
      .ok ((((Cache.raw.codes[168]!).body).drop 91, .end), { bytes := artifactBytes, pos := 34897, limit := 34897 }) := by
  cbv

@[cbv_eval] theorem code168_seq_168_tail28_decoded :
    instructionSequenceAt 292 false { bytes := artifactBytes, pos := 34633, limit := 34897 } =
      .ok ((((Cache.raw.codes[168]!).body).drop 28, .end), { bytes := artifactBytes, pos := 34897, limit := 34897 }) := by
  cbv

@[cbv_eval] theorem code168_seq_168_tail0_decoded :
    instructionSequenceAt 320 false { bytes := artifactBytes, pos := 34577, limit := 34897 } =
      .ok ((((Cache.raw.codes[168]!).body).drop 0, .end), { bytes := artifactBytes, pos := 34897, limit := 34897 }) := by
  cbv

theorem code168_decoded :
    code { bytes := artifactBytes, pos := 34572, limit := 45644 } =
      .ok (Cache.raw.codes[168]!, { bytes := artifactBytes, pos := 34897, limit := 45644 }) := by
  refine code_eq_of_parts (size := 323)
    (payload := { bytes := artifactBytes, pos := 34574, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 34577, limit := 34897 })
    (bodyFinish := { bytes := artifactBytes, pos := 34897, limit := 34897 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code168_seq_168_tail0_decoded
  · rfl

#print axioms code168_decoded

@[cbv_eval] theorem code169_seq_169_tail195_decoded :
    instructionSequenceAt 328 false { bytes := artifactBytes, pos := 35296, limit := 35425 } =
      .ok ((((Cache.raw.codes[169]!).body).drop 195, .end), { bytes := artifactBytes, pos := 35425, limit := 35425 }) := by
  cbv

@[cbv_eval] theorem code169_seq_169_tail131_decoded :
    instructionSequenceAt 392 false { bytes := artifactBytes, pos := 35167, limit := 35425 } =
      .ok ((((Cache.raw.codes[169]!).body).drop 131, .end), { bytes := artifactBytes, pos := 35425, limit := 35425 }) := by
  cbv

@[cbv_eval] theorem code169_seq_169_tail67_decoded :
    instructionSequenceAt 456 false { bytes := artifactBytes, pos := 35038, limit := 35425 } =
      .ok ((((Cache.raw.codes[169]!).body).drop 67, .end), { bytes := artifactBytes, pos := 35425, limit := 35425 }) := by
  cbv

@[cbv_eval] theorem code169_seq_169_tail4_decoded :
    instructionSequenceAt 519 false { bytes := artifactBytes, pos := 34910, limit := 35425 } =
      .ok ((((Cache.raw.codes[169]!).body).drop 4, .end), { bytes := artifactBytes, pos := 35425, limit := 35425 }) := by
  cbv

@[cbv_eval] theorem code169_seq_169_tail0_decoded :
    instructionSequenceAt 523 false { bytes := artifactBytes, pos := 34902, limit := 35425 } =
      .ok ((((Cache.raw.codes[169]!).body).drop 0, .end), { bytes := artifactBytes, pos := 35425, limit := 35425 }) := by
  cbv

theorem code169_decoded :
    code { bytes := artifactBytes, pos := 34897, limit := 45644 } =
      .ok (Cache.raw.codes[169]!, { bytes := artifactBytes, pos := 35425, limit := 45644 }) := by
  refine code_eq_of_parts (size := 526)
    (payload := { bytes := artifactBytes, pos := 34899, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 34902, limit := 35425 })
    (bodyFinish := { bytes := artifactBytes, pos := 35425, limit := 35425 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code169_seq_169_tail0_decoded
  · rfl

#print axioms code169_decoded

@[cbv_eval] theorem code170_seq_170_tail388_decoded :
    instructionSequenceAt 634 false { bytes := artifactBytes, pos := 36323, limit := 36453 } =
      .ok ((((Cache.raw.codes[170]!).body).drop 388, .end), { bytes := artifactBytes, pos := 36453, limit := 36453 }) := by
  cbv

@[cbv_eval] theorem code170_seq_170_tail345_decoded :
    instructionSequenceAt 677 false { bytes := artifactBytes, pos := 36194, limit := 36453 } =
      .ok ((((Cache.raw.codes[170]!).body).drop 345, .end), { bytes := artifactBytes, pos := 36453, limit := 36453 }) := by
  cbv

@[cbv_eval] theorem code170_seq_170_tail298_decoded :
    instructionSequenceAt 724 false { bytes := artifactBytes, pos := 36065, limit := 36453 } =
      .ok ((((Cache.raw.codes[170]!).body).drop 298, .end), { bytes := artifactBytes, pos := 36453, limit := 36453 }) := by
  cbv

@[cbv_eval] theorem code170_seq_170_tail236_decoded :
    instructionSequenceAt 786 false { bytes := artifactBytes, pos := 35937, limit := 36453 } =
      .ok ((((Cache.raw.codes[170]!).body).drop 236, .end), { bytes := artifactBytes, pos := 36453, limit := 36453 }) := by
  cbv

@[cbv_eval] theorem code170_seq_170_tail172_decoded :
    instructionSequenceAt 850 false { bytes := artifactBytes, pos := 35809, limit := 36453 } =
      .ok ((((Cache.raw.codes[170]!).body).drop 172, .end), { bytes := artifactBytes, pos := 36453, limit := 36453 }) := by
  cbv

@[cbv_eval] theorem code170_seq_170_tail113_decoded :
    instructionSequenceAt 909 false { bytes := artifactBytes, pos := 35680, limit := 36453 } =
      .ok ((((Cache.raw.codes[170]!).body).drop 113, .end), { bytes := artifactBytes, pos := 36453, limit := 36453 }) := by
  cbv

end Project.EulerCertificate.Artifact
