import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_28_21_e_39_e_14_t_0_t_tail156 :
    instructionSequenceAt 744 false { bytes := artifactBytes, pos := 5416, limit := 5603 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[14]!).childBody false)[0]!).childBody false).drop 156, .end), { bytes := artifactBytes, pos := 5562, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_14_t_0_t_tail107 :
    instructionSequenceAt 793 false { bytes := artifactBytes, pos := 5282, limit := 5603 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[14]!).childBody false)[0]!).childBody false).drop 107, .end), { bytes := artifactBytes, pos := 5562, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_14_t_0_t_tail60 :
    instructionSequenceAt 840 false { bytes := artifactBytes, pos := 5153, limit := 5603 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[14]!).childBody false)[0]!).childBody false).drop 60, .end), { bytes := artifactBytes, pos := 5562, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_14_t_0_t_tail14 :
    instructionSequenceAt 886 false { bytes := artifactBytes, pos := 5025, limit := 5603 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[14]!).childBody false)[0]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 5562, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_14_t_0_t_tail0 :
    instructionSequenceAt 900 false { bytes := artifactBytes, pos := 4998, limit := 5603 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[14]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5562, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_14_t_tail0 :
    instructionSequenceAt 902 false { bytes := artifactBytes, pos := 4996, limit := 5603 } =
      .ok ((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[14]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5563, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_tail14 :
    instructionSequenceAt 904 false { bytes := artifactBytes, pos := 4994, limit := 5603 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true).drop 14, .end), { bytes := artifactBytes, pos := 5599, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_tail0 :
    instructionSequenceAt 918 false { bytes := artifactBytes, pos := 4966, limit := 5603 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 5599, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_tail39 :
    instructionSequenceAt 920 false { bytes := artifactBytes, pos := 4959, limit := 5603 } =
      .ok ((((((Cache.raw.codes[28]!).body)[21]!).childBody true).drop 39, .end), { bytes := artifactBytes, pos := 5600, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_tail30 :
    instructionSequenceAt 929 false { bytes := artifactBytes, pos := 4804, limit := 5603 } =
      .ok ((((((Cache.raw.codes[28]!).body)[21]!).childBody true).drop 30, .end), { bytes := artifactBytes, pos := 5600, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_tail0 :
    instructionSequenceAt 959 false { bytes := artifactBytes, pos := 4676, limit := 5603 } =
      .ok ((((((Cache.raw.codes[28]!).body)[21]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 5600, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_tail21 :
    instructionSequenceAt 961 false { bytes := artifactBytes, pos := 4669, limit := 5603 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 21, .end), { bytes := artifactBytes, pos := 5603, limit := 5603 }) := by
  cbv

@[cbv_eval] theorem sequence_28_tail0 :
    instructionSequenceAt 982 false { bytes := artifactBytes, pos := 4621, limit := 5603 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5603, limit := 5603 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 4616, limit := 28315 } = .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 5603, limit := 28315 }) := by
  refine code_eq_of_parts (size := 985)
    (payload := { bytes := artifactBytes, pos := 4618, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 4621, limit := 5603 })
    (bodyFinish := { bytes := artifactBytes, pos := 5603, limit := 5603 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_28_tail0
  · rfl

#print axioms code28_decoded

end Project.Gpt2QuantizedCached.Artifact
