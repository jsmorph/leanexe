import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code0_seq_0_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3009, limit := 3016 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3016, limit := 3016 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 3005, limit := 45644 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 3016, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3006, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 3009, limit := 3016 })
    (bodyFinish := { bytes := artifactBytes, pos := 3016, limit := 3016 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code0_seq_0_tail0_decoded
  · rfl

#print axioms code0_decoded

@[cbv_eval] theorem code1_seq_1_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 3020, limit := 3045 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3045, limit := 3045 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 3016, limit := 45644 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 3045, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 3017, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 3020, limit := 3045 })
    (bodyFinish := { bytes := artifactBytes, pos := 3045, limit := 3045 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_seq_1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_seq_2_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3049, limit := 3056 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3056, limit := 3056 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 3045, limit := 45644 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 3056, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3046, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 3049, limit := 3056 })
    (bodyFinish := { bytes := artifactBytes, pos := 3056, limit := 3056 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_seq_2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_seq_3_30_t_0_t_tail18_decoded :
    instructionSequenceAt 2732 false { bytes := artifactBytes, pos := 3154, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[30]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 3282, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_30_t_0_t_tail0_decoded :
    instructionSequenceAt 2750 false { bytes := artifactBytes, pos := 3123, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[30]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3282, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_47_t_0_t_tail29_decoded :
    instructionSequenceAt 2704 false { bytes := artifactBytes, pos := 3510, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[47]!).childBody false)[0]!).childBody false).drop 29, .end), { bytes := artifactBytes, pos := 3638, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_47_t_0_t_tail0_decoded :
    instructionSequenceAt 2733 false { bytes := artifactBytes, pos := 3461, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[47]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3638, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_82_t_0_t_tail18_decoded :
    instructionSequenceAt 2680 false { bytes := artifactBytes, pos := 3740, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[82]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 3868, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_82_t_0_t_tail0_decoded :
    instructionSequenceAt 2698 false { bytes := artifactBytes, pos := 3709, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[82]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3868, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_99_t_0_t_tail29_decoded :
    instructionSequenceAt 2652 false { bytes := artifactBytes, pos := 4096, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[99]!).childBody false)[0]!).childBody false).drop 29, .end), { bytes := artifactBytes, pos := 4224, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_99_t_0_t_tail0_decoded :
    instructionSequenceAt 2681 false { bytes := artifactBytes, pos := 4047, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[99]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4224, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_152_t_0_t_tail18_decoded :
    instructionSequenceAt 2610 false { bytes := artifactBytes, pos := 4359, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[152]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4487, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_152_t_0_t_tail0_decoded :
    instructionSequenceAt 2628 false { bytes := artifactBytes, pos := 4328, limit := 5845 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[152]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4487, limit := 5845 }) := by
  cbv

end Project.EulerCertificate.Artifact
