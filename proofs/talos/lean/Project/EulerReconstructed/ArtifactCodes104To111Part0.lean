import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code104_seq_104_16_t_17_t_31_t_93_t_tail18_decoded :
    instructionSequenceAt 689 true { bytes := artifactBytes, pos := 14772, limit := 15125 } =
      .ok ((((((((((((Cache.raw.codes[104]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false)[93]!).childBody false).drop 18, .otherwise), { bytes := artifactBytes, pos := 14901, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_17_t_31_t_93_t_tail0_decoded :
    instructionSequenceAt 707 true { bytes := artifactBytes, pos := 14736, limit := 15125 } =
      .ok ((((((((((((Cache.raw.codes[104]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false)[93]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 14901, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_17_t_31_t_tail93_decoded :
    instructionSequenceAt 709 true { bytes := artifactBytes, pos := 14734, limit := 15125 } =
      .ok ((((((((((Cache.raw.codes[104]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 93, .otherwise), { bytes := artifactBytes, pos := 14953, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_17_t_31_t_tail66_decoded :
    instructionSequenceAt 736 true { bytes := artifactBytes, pos := 14605, limit := 15125 } =
      .ok ((((((((((Cache.raw.codes[104]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 66, .otherwise), { bytes := artifactBytes, pos := 14953, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_17_t_31_t_tail2_decoded :
    instructionSequenceAt 800 true { bytes := artifactBytes, pos := 14477, limit := 15125 } =
      .ok ((((((((((Cache.raw.codes[104]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 2, .otherwise), { bytes := artifactBytes, pos := 14953, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_17_t_31_t_tail0_decoded :
    instructionSequenceAt 802 true { bytes := artifactBytes, pos := 14473, limit := 15125 } =
      .ok ((((((((((Cache.raw.codes[104]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 14953, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_17_t_tail31_decoded :
    instructionSequenceAt 804 true { bytes := artifactBytes, pos := 14471, limit := 15125 } =
      .ok ((((((((Cache.raw.codes[104]!).body)[16]!).childBody false)[17]!).childBody false).drop 31, .otherwise), { bytes := artifactBytes, pos := 15005, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_17_t_tail0_decoded :
    instructionSequenceAt 835 true { bytes := artifactBytes, pos := 14380, limit := 15125 } =
      .ok ((((((((Cache.raw.codes[104]!).body)[16]!).childBody false)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 15005, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_tail17_decoded :
    instructionSequenceAt 837 true { bytes := artifactBytes, pos := 14378, limit := 15125 } =
      .ok ((((((Cache.raw.codes[104]!).body)[16]!).childBody false).drop 17, .otherwise), { bytes := artifactBytes, pos := 15057, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_16_t_tail0_decoded :
    instructionSequenceAt 854 true { bytes := artifactBytes, pos := 14336, limit := 15125 } =
      .ok ((((((Cache.raw.codes[104]!).body)[16]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 15057, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_tail16_decoded :
    instructionSequenceAt 856 false { bytes := artifactBytes, pos := 14334, limit := 15125 } =
      .ok ((((Cache.raw.codes[104]!).body).drop 16, .end), { bytes := artifactBytes, pos := 15125, limit := 15125 }) := by
  cbv

@[cbv_eval] theorem code104_seq_104_tail0_decoded :
    instructionSequenceAt 872 false { bytes := artifactBytes, pos := 14253, limit := 15125 } =
      .ok ((((Cache.raw.codes[104]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15125, limit := 15125 }) := by
  cbv

theorem code104_decoded :
    code { bytes := artifactBytes, pos := 14248, limit := 30726 } =
      .ok (Cache.raw.codes[104]!, { bytes := artifactBytes, pos := 15125, limit := 30726 }) := by
  refine code_eq_of_parts (size := 875)
    (payload := { bytes := artifactBytes, pos := 14250, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 14253, limit := 15125 })
    (bodyFinish := { bytes := artifactBytes, pos := 15125, limit := 15125 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code104_seq_104_tail0_decoded
  · rfl

#print axioms code104_decoded

@[cbv_eval] theorem code105_seq_105_tail106_decoded :
    instructionSequenceAt 235 false { bytes := artifactBytes, pos := 15342, limit := 15471 } =
      .ok ((((Cache.raw.codes[105]!).body).drop 106, .end), { bytes := artifactBytes, pos := 15471, limit := 15471 }) := by
  cbv

@[cbv_eval] theorem code105_seq_105_tail42_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 15214, limit := 15471 } =
      .ok ((((Cache.raw.codes[105]!).body).drop 42, .end), { bytes := artifactBytes, pos := 15471, limit := 15471 }) := by
  cbv

@[cbv_eval] theorem code105_seq_105_tail0_decoded :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 15130, limit := 15471 } =
      .ok ((((Cache.raw.codes[105]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15471, limit := 15471 }) := by
  cbv


end Project.EulerReconstructed.Artifact
