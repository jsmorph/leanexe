import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_37_42_t_0_t_24_t_0_t_tail39 :
    instructionSequenceAt 601 false { bytes := artifactBytes, pos := 17494, limit := 17671 } =
      .ok ((((((((((((Cache.raw.codes[37]!).body)[42]!).childBody false)[0]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 17622, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_42_t_0_t_24_t_0_t_tail0 :
    instructionSequenceAt 640 false { bytes := artifactBytes, pos := 17421, limit := 17671 } =
      .ok ((((((((((((Cache.raw.codes[37]!).body)[42]!).childBody false)[0]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17622, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_42_t_0_t_24_t_tail0 :
    instructionSequenceAt 642 false { bytes := artifactBytes, pos := 17419, limit := 17671 } =
      .ok ((((((((((Cache.raw.codes[37]!).body)[42]!).childBody false)[0]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17623, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_29_t_0_t_tail18 :
    instructionSequenceAt 663 false { bytes := artifactBytes, pos := 17074, limit := 17671 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 17202, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_29_t_0_t_tail0 :
    instructionSequenceAt 681 false { bytes := artifactBytes, pos := 17043, limit := 17671 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17202, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_42_t_0_t_tail24 :
    instructionSequenceAt 644 false { bytes := artifactBytes, pos := 17417, limit := 17671 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[42]!).childBody false)[0]!).childBody false).drop 24, .end), { bytes := artifactBytes, pos := 17647, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_42_t_0_t_tail0 :
    instructionSequenceAt 668 false { bytes := artifactBytes, pos := 17373, limit := 17671 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[42]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17647, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_29_t_tail0 :
    instructionSequenceAt 683 false { bytes := artifactBytes, pos := 17041, limit := 17671 } =
      .ok ((((((Cache.raw.codes[37]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17203, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_33_t_tail8 :
    instructionSequenceAt 671 true { bytes := artifactBytes, pos := 17223, limit := 17671 } =
      .ok ((((((Cache.raw.codes[37]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 17354, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_33_t_tail0 :
    instructionSequenceAt 679 true { bytes := artifactBytes, pos := 17210, limit := 17671 } =
      .ok ((((((Cache.raw.codes[37]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17354, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_42_t_tail0 :
    instructionSequenceAt 670 false { bytes := artifactBytes, pos := 17371, limit := 17671 } =
      .ok ((((((Cache.raw.codes[37]!).body)[42]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17648, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail42 :
    instructionSequenceAt 672 false { bytes := artifactBytes, pos := 17369, limit := 17671 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 42, .end), { bytes := artifactBytes, pos := 17671, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail33 :
    instructionSequenceAt 681 false { bytes := artifactBytes, pos := 17208, limit := 17671 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 33, .end), { bytes := artifactBytes, pos := 17671, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail29 :
    instructionSequenceAt 685 false { bytes := artifactBytes, pos := 17039, limit := 17671 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 29, .end), { bytes := artifactBytes, pos := 17671, limit := 17671 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail0 :
    instructionSequenceAt 714 false { bytes := artifactBytes, pos := 16957, limit := 17671 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17671, limit := 17671 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 16952, limit := 19083 } = .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 17671, limit := 19083 }) := by
  refine code_eq_of_parts (size := 717)
    (payload := { bytes := artifactBytes, pos := 16954, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 16957, limit := 17671 })
    (bodyFinish := { bytes := artifactBytes, pos := 17671, limit := 17671 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_37_tail0
  · rfl

#print axioms code37_decoded

end Project.Gpt2CachedStep.Artifact
