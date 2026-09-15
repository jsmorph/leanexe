import Project.EulerReconstructed.ArtifactCodes136To143Part0
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code138_seq_138_tail0_decoded :
    instructionSequenceAt 836 false { bytes := artifactBytes, pos := 21350, limit := 22186 } =
      .ok ((((Cache.raw.codes[138]!).body).drop 0, .end), { bytes := artifactBytes, pos := 22186, limit := 22186 }) := by
  cbv

theorem code138_decoded :
    code { bytes := artifactBytes, pos := 21345, limit := 30726 } =
      .ok (Cache.raw.codes[138]!, { bytes := artifactBytes, pos := 22186, limit := 30726 }) := by
  refine code_eq_of_parts (size := 839)
    (payload := { bytes := artifactBytes, pos := 21347, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 21350, limit := 22186 })
    (bodyFinish := { bytes := artifactBytes, pos := 22186, limit := 22186 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code138_seq_138_tail0_decoded
  · rfl

#print axioms code138_decoded

@[cbv_eval] theorem code139_seq_139_tail68_decoded :
    instructionSequenceAt 551 false { bytes := artifactBytes, pos := 22681, limit := 22810 } =
      .ok ((((Cache.raw.codes[139]!).body).drop 68, .end), { bytes := artifactBytes, pos := 22810, limit := 22810 }) := by
  cbv

@[cbv_eval] theorem code139_seq_139_tail64_decoded :
    instructionSequenceAt 555 false { bytes := artifactBytes, pos := 22553, limit := 22810 } =
      .ok ((((Cache.raw.codes[139]!).body).drop 64, .end), { bytes := artifactBytes, pos := 22810, limit := 22810 }) := by
  cbv

@[cbv_eval] theorem code139_seq_139_tail31_decoded :
    instructionSequenceAt 588 false { bytes := artifactBytes, pos := 22310, limit := 22810 } =
      .ok ((((Cache.raw.codes[139]!).body).drop 31, .end), { bytes := artifactBytes, pos := 22810, limit := 22810 }) := by
  cbv

@[cbv_eval] theorem code139_seq_139_tail0_decoded :
    instructionSequenceAt 619 false { bytes := artifactBytes, pos := 22191, limit := 22810 } =
      .ok ((((Cache.raw.codes[139]!).body).drop 0, .end), { bytes := artifactBytes, pos := 22810, limit := 22810 }) := by
  cbv

theorem code139_decoded :
    code { bytes := artifactBytes, pos := 22186, limit := 30726 } =
      .ok (Cache.raw.codes[139]!, { bytes := artifactBytes, pos := 22810, limit := 30726 }) := by
  refine code_eq_of_parts (size := 622)
    (payload := { bytes := artifactBytes, pos := 22188, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 22191, limit := 22810 })
    (bodyFinish := { bytes := artifactBytes, pos := 22810, limit := 22810 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code139_seq_139_tail0_decoded
  · rfl

#print axioms code139_decoded

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_t_52_t_0_t_tail18_decoded :
    instructionSequenceAt 2437 false { bytes := artifactBytes, pos := 23010, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[52]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 23138, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_t_52_t_0_t_tail0_decoded :
    instructionSequenceAt 2455 false { bytes := artifactBytes, pos := 22979, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[52]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23138, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_36_t_0_t_tail18_decoded :
    instructionSequenceAt 2453 false { bytes := artifactBytes, pos := 23490, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[36]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 23618, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_36_t_0_t_tail0_decoded :
    instructionSequenceAt 2471 false { bytes := artifactBytes, pos := 23459, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23618, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_53_t_0_t_tail139_decoded :
    instructionSequenceAt 2315 false { bytes := artifactBytes, pos := 24046, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false)[0]!).childBody false).drop 139, .end), { bytes := artifactBytes, pos := 24174, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_53_t_0_t_tail73_decoded :
    instructionSequenceAt 2381 false { bytes := artifactBytes, pos := 23918, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false)[0]!).childBody false).drop 73, .end), { bytes := artifactBytes, pos := 24174, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_53_t_0_t_tail0_decoded :
    instructionSequenceAt 2454 false { bytes := artifactBytes, pos := 23797, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24174, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_110_t_0_t_tail18_decoded :
    instructionSequenceAt 2379 false { bytes := artifactBytes, pos := 24317, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[110]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 24445, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_4_t_0_t_14_e_110_t_0_t_tail0_decoded :
    instructionSequenceAt 2397 false { bytes := artifactBytes, pos := 24286, limit := 25350 } =
      .ok ((((((((((((((Cache.raw.codes[140]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[110]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24445, limit := 25350 }) := by
  cbv


end Project.EulerReconstructed.Artifact
