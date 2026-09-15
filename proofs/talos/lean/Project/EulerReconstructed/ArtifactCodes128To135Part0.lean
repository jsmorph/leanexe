import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code128_seq_128_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 19671, limit := 19684 } =
      .ok ((((Cache.raw.codes[128]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19684, limit := 19684 }) := by
  cbv

theorem code128_decoded :
    code { bytes := artifactBytes, pos := 19667, limit := 30726 } =
      .ok (Cache.raw.codes[128]!, { bytes := artifactBytes, pos := 19684, limit := 30726 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 19668, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 19671, limit := 19684 })
    (bodyFinish := { bytes := artifactBytes, pos := 19684, limit := 19684 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code128_seq_128_tail0_decoded
  · rfl

#print axioms code128_decoded

@[cbv_eval] theorem code129_seq_129_4_t_0_t_19_e_23_t_tail70_decoded :
    instructionSequenceAt 401 true { bytes := artifactBytes, pos := 19983, limit := 20214 } =
      .ok ((((((((((((Cache.raw.codes[129]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false).drop 70, .otherwise), { bytes := artifactBytes, pos := 20116, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_4_t_0_t_19_e_23_t_tail11_decoded :
    instructionSequenceAt 460 true { bytes := artifactBytes, pos := 19854, limit := 20214 } =
      .ok ((((((((((((Cache.raw.codes[129]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false).drop 11, .otherwise), { bytes := artifactBytes, pos := 20116, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_4_t_0_t_19_e_23_t_tail0_decoded :
    instructionSequenceAt 471 true { bytes := artifactBytes, pos := 19832, limit := 20214 } =
      .ok ((((((((((((Cache.raw.codes[129]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 20116, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_4_t_0_t_19_e_tail23_decoded :
    instructionSequenceAt 473 false { bytes := artifactBytes, pos := 19830, limit := 20214 } =
      .ok ((((((((((Cache.raw.codes[129]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 23, .end), { bytes := artifactBytes, pos := 20138, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_4_t_0_t_19_e_tail0_decoded :
    instructionSequenceAt 496 false { bytes := artifactBytes, pos := 19776, limit := 20214 } =
      .ok ((((((((((Cache.raw.codes[129]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 20138, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_4_t_0_t_tail19_decoded :
    instructionSequenceAt 498 false { bytes := artifactBytes, pos := 19753, limit := 20214 } =
      .ok ((((((((Cache.raw.codes[129]!).body)[4]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 20141, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_4_t_0_t_tail0_decoded :
    instructionSequenceAt 517 false { bytes := artifactBytes, pos := 19701, limit := 20214 } =
      .ok ((((((((Cache.raw.codes[129]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20141, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_4_t_tail0_decoded :
    instructionSequenceAt 519 false { bytes := artifactBytes, pos := 19699, limit := 20214 } =
      .ok ((((((Cache.raw.codes[129]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20142, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_tail4_decoded :
    instructionSequenceAt 521 false { bytes := artifactBytes, pos := 19697, limit := 20214 } =
      .ok ((((Cache.raw.codes[129]!).body).drop 4, .end), { bytes := artifactBytes, pos := 20214, limit := 20214 }) := by
  cbv

@[cbv_eval] theorem code129_seq_129_tail0_decoded :
    instructionSequenceAt 525 false { bytes := artifactBytes, pos := 19689, limit := 20214 } =
      .ok ((((Cache.raw.codes[129]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20214, limit := 20214 }) := by
  cbv

theorem code129_decoded :
    code { bytes := artifactBytes, pos := 19684, limit := 30726 } =
      .ok (Cache.raw.codes[129]!, { bytes := artifactBytes, pos := 20214, limit := 30726 }) := by
  refine code_eq_of_parts (size := 528)
    (payload := { bytes := artifactBytes, pos := 19686, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 19689, limit := 20214 })
    (bodyFinish := { bytes := artifactBytes, pos := 20214, limit := 20214 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code129_seq_129_tail0_decoded
  · rfl

#print axioms code129_decoded

@[cbv_eval] theorem code130_seq_130_7_e_tail3_decoded :
    instructionSequenceAt 150 false { bytes := artifactBytes, pos := 20246, limit := 20381 } =
      .ok ((((((Cache.raw.codes[130]!).body)[7]!).childBody true).drop 3, .end), { bytes := artifactBytes, pos := 20376, limit := 20381 }) := by
  cbv

@[cbv_eval] theorem code130_seq_130_7_e_tail0_decoded :
    instructionSequenceAt 153 false { bytes := artifactBytes, pos := 20241, limit := 20381 } =
      .ok ((((((Cache.raw.codes[130]!).body)[7]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 20376, limit := 20381 }) := by
  cbv

@[cbv_eval] theorem code130_seq_130_tail7_decoded :
    instructionSequenceAt 155 false { bytes := artifactBytes, pos := 20236, limit := 20381 } =
      .ok ((((Cache.raw.codes[130]!).body).drop 7, .end), { bytes := artifactBytes, pos := 20381, limit := 20381 }) := by
  cbv


end Project.EulerReconstructed.Artifact
