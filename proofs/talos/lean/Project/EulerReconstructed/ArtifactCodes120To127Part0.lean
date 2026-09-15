import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code120_seq_120_tail166_decoded :
    instructionSequenceAt 295 false { bytes := artifactBytes, pos := 16876, limit := 17005 } =
      .ok ((((Cache.raw.codes[120]!).body).drop 166, .end), { bytes := artifactBytes, pos := 17005, limit := 17005 }) := by
  cbv

@[cbv_eval] theorem code120_seq_120_tail102_decoded :
    instructionSequenceAt 359 false { bytes := artifactBytes, pos := 16748, limit := 17005 } =
      .ok ((((Cache.raw.codes[120]!).body).drop 102, .end), { bytes := artifactBytes, pos := 17005, limit := 17005 }) := by
  cbv

@[cbv_eval] theorem code120_seq_120_tail38_decoded :
    instructionSequenceAt 423 false { bytes := artifactBytes, pos := 16620, limit := 17005 } =
      .ok ((((Cache.raw.codes[120]!).body).drop 38, .end), { bytes := artifactBytes, pos := 17005, limit := 17005 }) := by
  cbv

@[cbv_eval] theorem code120_seq_120_tail0_decoded :
    instructionSequenceAt 461 false { bytes := artifactBytes, pos := 16544, limit := 17005 } =
      .ok ((((Cache.raw.codes[120]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17005, limit := 17005 }) := by
  cbv

theorem code120_decoded :
    code { bytes := artifactBytes, pos := 16539, limit := 30726 } =
      .ok (Cache.raw.codes[120]!, { bytes := artifactBytes, pos := 17005, limit := 30726 }) := by
  refine code_eq_of_parts (size := 464)
    (payload := { bytes := artifactBytes, pos := 16541, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16544, limit := 17005 })
    (bodyFinish := { bytes := artifactBytes, pos := 17005, limit := 17005 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code120_seq_120_tail0_decoded
  · rfl

#print axioms code120_decoded

@[cbv_eval] theorem code121_seq_121_30_t_0_t_tail18_decoded :
    instructionSequenceAt 785 false { bytes := artifactBytes, pos := 17103, limit := 17847 } =
      .ok ((((((((Cache.raw.codes[121]!).body)[30]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 17231, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_30_t_0_t_tail0_decoded :
    instructionSequenceAt 803 false { bytes := artifactBytes, pos := 17072, limit := 17847 } =
      .ok ((((((((Cache.raw.codes[121]!).body)[30]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17231, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_47_t_0_t_tail162_decoded :
    instructionSequenceAt 624 false { bytes := artifactBytes, pos := 17701, limit := 17847 } =
      .ok ((((((((Cache.raw.codes[121]!).body)[47]!).childBody false)[0]!).childBody false).drop 162, .end), { bytes := artifactBytes, pos := 17829, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_47_t_0_t_tail96_decoded :
    instructionSequenceAt 690 false { bytes := artifactBytes, pos := 17573, limit := 17847 } =
      .ok ((((((((Cache.raw.codes[121]!).body)[47]!).childBody false)[0]!).childBody false).drop 96, .end), { bytes := artifactBytes, pos := 17829, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_47_t_0_t_tail20_decoded :
    instructionSequenceAt 766 false { bytes := artifactBytes, pos := 17444, limit := 17847 } =
      .ok ((((((((Cache.raw.codes[121]!).body)[47]!).childBody false)[0]!).childBody false).drop 20, .end), { bytes := artifactBytes, pos := 17829, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_47_t_0_t_tail0_decoded :
    instructionSequenceAt 786 false { bytes := artifactBytes, pos := 17410, limit := 17847 } =
      .ok ((((((((Cache.raw.codes[121]!).body)[47]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17829, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_30_t_tail0_decoded :
    instructionSequenceAt 805 false { bytes := artifactBytes, pos := 17070, limit := 17847 } =
      .ok ((((((Cache.raw.codes[121]!).body)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17232, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_34_t_tail8_decoded :
    instructionSequenceAt 793 true { bytes := artifactBytes, pos := 17252, limit := 17847 } =
      .ok ((((((Cache.raw.codes[121]!).body)[34]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 17383, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_34_t_tail0_decoded :
    instructionSequenceAt 801 true { bytes := artifactBytes, pos := 17239, limit := 17847 } =
      .ok ((((((Cache.raw.codes[121]!).body)[34]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17383, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_47_t_tail0_decoded :
    instructionSequenceAt 788 false { bytes := artifactBytes, pos := 17408, limit := 17847 } =
      .ok ((((((Cache.raw.codes[121]!).body)[47]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17830, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_tail47_decoded :
    instructionSequenceAt 790 false { bytes := artifactBytes, pos := 17406, limit := 17847 } =
      .ok ((((Cache.raw.codes[121]!).body).drop 47, .end), { bytes := artifactBytes, pos := 17847, limit := 17847 }) := by
  cbv


end Project.EulerReconstructed.Artifact
