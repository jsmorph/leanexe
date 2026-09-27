import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_74_t_0_t_tail18 :
    instructionSequenceAt 1953 false { bytes := artifactBytes, pos := 21188, limit := 21750 } =
      .ok ((((((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false)[74]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 21316, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_74_t_0_t_tail0 :
    instructionSequenceAt 1971 false { bytes := artifactBytes, pos := 21157, limit := 21750 } =
      .ok ((((((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false)[74]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 21316, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_74_t_tail0 :
    instructionSequenceAt 1973 false { bytes := artifactBytes, pos := 21155, limit := 21750 } =
      .ok ((((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false)[74]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 21317, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_78_t_tail8 :
    instructionSequenceAt 1961 true { bytes := artifactBytes, pos := 21337, limit := 21750 } =
      .ok ((((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false)[78]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 21468, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_78_t_tail0 :
    instructionSequenceAt 1969 true { bytes := artifactBytes, pos := 21324, limit := 21750 } =
      .ok ((((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false)[78]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 21468, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_t_26_t_0_t_tail18 :
    instructionSequenceAt 2064 false { bytes := artifactBytes, pos := 20242, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 20370, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_t_26_t_0_t_tail0 :
    instructionSequenceAt 2082 false { bytes := artifactBytes, pos := 20211, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20370, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_28_t_0_t_tail18 :
    instructionSequenceAt 2062 false { bytes := artifactBytes, pos := 20638, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 20766, limit := 21750 }) := by
  cbv


end Project.Beck.Artifact
