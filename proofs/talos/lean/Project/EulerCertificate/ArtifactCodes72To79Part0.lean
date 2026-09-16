import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code72_seq_72_tail24_decoded :
    instructionSequenceAt 153 false { bytes := artifactBytes, pos := 17313, limit := 17442 } =
      .ok ((((Cache.raw.codes[72]!).body).drop 24, .end), { bytes := artifactBytes, pos := 17442, limit := 17442 }) := by
  cbv

@[cbv_eval] theorem code72_seq_72_tail0_decoded :
    instructionSequenceAt 177 false { bytes := artifactBytes, pos := 17265, limit := 17442 } =
      .ok ((((Cache.raw.codes[72]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17442, limit := 17442 }) := by
  cbv

theorem code72_decoded :
    code { bytes := artifactBytes, pos := 17260, limit := 45644 } =
      .ok (Cache.raw.codes[72]!, { bytes := artifactBytes, pos := 17442, limit := 45644 }) := by
  refine code_eq_of_parts (size := 180)
    (payload := { bytes := artifactBytes, pos := 17262, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 17265, limit := 17442 })
    (bodyFinish := { bytes := artifactBytes, pos := 17442, limit := 17442 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code72_seq_72_tail0_decoded
  · rfl

#print axioms code72_decoded

@[cbv_eval] theorem code73_seq_73_tail82_decoded :
    instructionSequenceAt 211 false { bytes := artifactBytes, pos := 17611, limit := 17740 } =
      .ok ((((Cache.raw.codes[73]!).body).drop 82, .end), { bytes := artifactBytes, pos := 17740, limit := 17740 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_tail18_decoded :
    instructionSequenceAt 275 false { bytes := artifactBytes, pos := 17483, limit := 17740 } =
      .ok ((((Cache.raw.codes[73]!).body).drop 18, .end), { bytes := artifactBytes, pos := 17740, limit := 17740 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_tail0_decoded :
    instructionSequenceAt 293 false { bytes := artifactBytes, pos := 17447, limit := 17740 } =
      .ok ((((Cache.raw.codes[73]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17740, limit := 17740 }) := by
  cbv

theorem code73_decoded :
    code { bytes := artifactBytes, pos := 17442, limit := 45644 } =
      .ok (Cache.raw.codes[73]!, { bytes := artifactBytes, pos := 17740, limit := 45644 }) := by
  refine code_eq_of_parts (size := 296)
    (payload := { bytes := artifactBytes, pos := 17444, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 17447, limit := 17740 })
    (bodyFinish := { bytes := artifactBytes, pos := 17740, limit := 17740 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code73_seq_73_tail0_decoded
  · rfl

#print axioms code73_decoded

@[cbv_eval] theorem code74_seq_74_82_t_0_t_tail178_decoded :
    instructionSequenceAt 439 false { bytes := artifactBytes, pos := 18245, limit := 18448 } =
      .ok ((((((((Cache.raw.codes[74]!).body)[82]!).childBody false)[0]!).childBody false).drop 178, .end), { bytes := artifactBytes, pos := 18374, limit := 18448 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_82_t_0_t_tail114_decoded :
    instructionSequenceAt 503 false { bytes := artifactBytes, pos := 18117, limit := 18448 } =
      .ok ((((((((Cache.raw.codes[74]!).body)[82]!).childBody false)[0]!).childBody false).drop 114, .end), { bytes := artifactBytes, pos := 18374, limit := 18448 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_82_t_0_t_tail42_decoded :
    instructionSequenceAt 575 false { bytes := artifactBytes, pos := 17989, limit := 18448 } =
      .ok ((((((((Cache.raw.codes[74]!).body)[82]!).childBody false)[0]!).childBody false).drop 42, .end), { bytes := artifactBytes, pos := 18374, limit := 18448 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_82_t_0_t_tail0_decoded :
    instructionSequenceAt 617 false { bytes := artifactBytes, pos := 17918, limit := 18448 } =
      .ok ((((((((Cache.raw.codes[74]!).body)[82]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18374, limit := 18448 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_82_t_tail0_decoded :
    instructionSequenceAt 619 false { bytes := artifactBytes, pos := 17916, limit := 18448 } =
      .ok ((((((Cache.raw.codes[74]!).body)[82]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18375, limit := 18448 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_tail82_decoded :
    instructionSequenceAt 621 false { bytes := artifactBytes, pos := 17914, limit := 18448 } =
      .ok ((((Cache.raw.codes[74]!).body).drop 82, .end), { bytes := artifactBytes, pos := 18448, limit := 18448 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_tail20_decoded :
    instructionSequenceAt 683 false { bytes := artifactBytes, pos := 17785, limit := 18448 } =
      .ok ((((Cache.raw.codes[74]!).body).drop 20, .end), { bytes := artifactBytes, pos := 18448, limit := 18448 }) := by
  cbv

@[cbv_eval] theorem code74_seq_74_tail0_decoded :
    instructionSequenceAt 703 false { bytes := artifactBytes, pos := 17745, limit := 18448 } =
      .ok ((((Cache.raw.codes[74]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18448, limit := 18448 }) := by
  cbv

theorem code74_decoded :
    code { bytes := artifactBytes, pos := 17740, limit := 45644 } =
      .ok (Cache.raw.codes[74]!, { bytes := artifactBytes, pos := 18448, limit := 45644 }) := by
  refine code_eq_of_parts (size := 706)
    (payload := { bytes := artifactBytes, pos := 17742, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 17745, limit := 18448 })
    (bodyFinish := { bytes := artifactBytes, pos := 18448, limit := 18448 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code74_seq_74_tail0_decoded
  · rfl

#print axioms code74_decoded

end Project.EulerCertificate.Artifact
