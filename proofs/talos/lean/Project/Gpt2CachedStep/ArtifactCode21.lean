import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_21_49_t_0_t_42_t_0_t_tail63 :
    instructionSequenceAt 788 false { bytes := artifactBytes, pos := 4818, limit := 5051 } =
      .ok ((((((((((((Cache.raw.codes[21]!).body)[49]!).childBody false)[0]!).childBody false)[42]!).childBody false)[0]!).childBody false).drop 63, .end), { bytes := artifactBytes, pos := 4946, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_49_t_0_t_42_t_0_t_tail21 :
    instructionSequenceAt 830 false { bytes := artifactBytes, pos := 4689, limit := 5051 } =
      .ok ((((((((((((Cache.raw.codes[21]!).body)[49]!).childBody false)[0]!).childBody false)[42]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 4946, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_49_t_0_t_42_t_0_t_tail0 :
    instructionSequenceAt 851 false { bytes := artifactBytes, pos := 4649, limit := 5051 } =
      .ok ((((((((((((Cache.raw.codes[21]!).body)[49]!).childBody false)[0]!).childBody false)[42]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4946, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_49_t_0_t_42_t_tail0 :
    instructionSequenceAt 853 false { bytes := artifactBytes, pos := 4647, limit := 5051 } =
      .ok ((((((((((Cache.raw.codes[21]!).body)[49]!).childBody false)[0]!).childBody false)[42]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4947, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_36_t_0_t_tail18 :
    instructionSequenceAt 892 false { bytes := artifactBytes, pos := 4251, limit := 5051 } =
      .ok ((((((((Cache.raw.codes[21]!).body)[36]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4379, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_36_t_0_t_tail0 :
    instructionSequenceAt 910 false { bytes := artifactBytes, pos := 4220, limit := 5051 } =
      .ok ((((((((Cache.raw.codes[21]!).body)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4379, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_49_t_0_t_tail42 :
    instructionSequenceAt 855 false { bytes := artifactBytes, pos := 4645, limit := 5051 } =
      .ok ((((((((Cache.raw.codes[21]!).body)[49]!).childBody false)[0]!).childBody false).drop 42, .end), { bytes := artifactBytes, pos := 5027, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_49_t_0_t_tail0 :
    instructionSequenceAt 897 false { bytes := artifactBytes, pos := 4550, limit := 5051 } =
      .ok ((((((((Cache.raw.codes[21]!).body)[49]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5027, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_36_t_tail0 :
    instructionSequenceAt 912 false { bytes := artifactBytes, pos := 4218, limit := 5051 } =
      .ok ((((((Cache.raw.codes[21]!).body)[36]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4380, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_40_t_tail8 :
    instructionSequenceAt 900 true { bytes := artifactBytes, pos := 4400, limit := 5051 } =
      .ok ((((((Cache.raw.codes[21]!).body)[40]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4531, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_40_t_tail0 :
    instructionSequenceAt 908 true { bytes := artifactBytes, pos := 4387, limit := 5051 } =
      .ok ((((((Cache.raw.codes[21]!).body)[40]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4531, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_49_t_tail0 :
    instructionSequenceAt 899 false { bytes := artifactBytes, pos := 4548, limit := 5051 } =
      .ok ((((((Cache.raw.codes[21]!).body)[49]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5028, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_tail49 :
    instructionSequenceAt 901 false { bytes := artifactBytes, pos := 4546, limit := 5051 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 49, .end), { bytes := artifactBytes, pos := 5051, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_tail40 :
    instructionSequenceAt 910 false { bytes := artifactBytes, pos := 4385, limit := 5051 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 40, .end), { bytes := artifactBytes, pos := 5051, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_tail36 :
    instructionSequenceAt 914 false { bytes := artifactBytes, pos := 4216, limit := 5051 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 36, .end), { bytes := artifactBytes, pos := 5051, limit := 5051 }) := by
  cbv

@[cbv_eval] theorem sequence_21_tail0 :
    instructionSequenceAt 950 false { bytes := artifactBytes, pos := 4101, limit := 5051 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5051, limit := 5051 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 4096, limit := 19083 } = .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 5051, limit := 19083 }) := by
  refine code_eq_of_parts (size := 953)
    (payload := { bytes := artifactBytes, pos := 4098, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 4101, limit := 5051 })
    (bodyFinish := { bytes := artifactBytes, pos := 5051, limit := 5051 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_21_tail0
  · rfl

#print axioms code21_decoded

end Project.Gpt2CachedStep.Artifact
