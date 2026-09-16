import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_23_t_106_t_tail180_decoded :
    instructionSequenceAt 931 true { bytes := artifactBytes, pos := 42316, limit := 42734 } =
      .ok ((((((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false)[106]!).childBody false).drop 180, .otherwise), { bytes := artifactBytes, pos := 42444, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_23_t_106_t_tail140_decoded :
    instructionSequenceAt 971 true { bytes := artifactBytes, pos := 42186, limit := 42734 } =
      .ok ((((((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false)[106]!).childBody false).drop 140, .otherwise), { bytes := artifactBytes, pos := 42444, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_23_t_106_t_tail86_decoded :
    instructionSequenceAt 1025 true { bytes := artifactBytes, pos := 42057, limit := 42734 } =
      .ok ((((((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false)[106]!).childBody false).drop 86, .otherwise), { bytes := artifactBytes, pos := 42444, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_23_t_106_t_tail22_decoded :
    instructionSequenceAt 1089 true { bytes := artifactBytes, pos := 41929, limit := 42734 } =
      .ok ((((((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false)[106]!).childBody false).drop 22, .otherwise), { bytes := artifactBytes, pos := 42444, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_23_t_106_t_tail0_decoded :
    instructionSequenceAt 1111 true { bytes := artifactBytes, pos := 41885, limit := 42734 } =
      .ok ((((((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false)[106]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 42444, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_23_t_tail106_decoded :
    instructionSequenceAt 1113 true { bytes := artifactBytes, pos := 41883, limit := 42734 } =
      .ok ((((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false).drop 106, .otherwise), { bytes := artifactBytes, pos := 42514, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_23_t_tail46_decoded :
    instructionSequenceAt 1173 true { bytes := artifactBytes, pos := 41754, limit := 42734 } =
      .ok ((((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false).drop 46, .otherwise), { bytes := artifactBytes, pos := 42514, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_23_t_tail0_decoded :
    instructionSequenceAt 1219 true { bytes := artifactBytes, pos := 41652, limit := 42734 } =
      .ok ((((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 42514, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_tail23_decoded :
    instructionSequenceAt 1221 false { bytes := artifactBytes, pos := 41650, limit := 42734 } =
      .ok ((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 23, .end), { bytes := artifactBytes, pos := 42584, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_19_e_tail0_decoded :
    instructionSequenceAt 1244 false { bytes := artifactBytes, pos := 41596, limit := 42734 } =
      .ok ((((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 42584, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_tail19_decoded :
    instructionSequenceAt 1246 false { bytes := artifactBytes, pos := 41525, limit := 42734 } =
      .ok ((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 42587, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_0_t_tail0_decoded :
    instructionSequenceAt 1265 false { bytes := artifactBytes, pos := 41473, limit := 42734 } =
      .ok ((((((((Cache.raw.codes[184]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 42587, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_4_t_tail0_decoded :
    instructionSequenceAt 1267 false { bytes := artifactBytes, pos := 41471, limit := 42734 } =
      .ok ((((((Cache.raw.codes[184]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 42588, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_tail8_decoded :
    instructionSequenceAt 1265 false { bytes := artifactBytes, pos := 42593, limit := 42734 } =
      .ok ((((Cache.raw.codes[184]!).body).drop 8, .end), { bytes := artifactBytes, pos := 42734, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_tail4_decoded :
    instructionSequenceAt 1269 false { bytes := artifactBytes, pos := 41469, limit := 42734 } =
      .ok ((((Cache.raw.codes[184]!).body).drop 4, .end), { bytes := artifactBytes, pos := 42734, limit := 42734 }) := by
  cbv

@[cbv_eval] theorem code184_seq_184_tail0_decoded :
    instructionSequenceAt 1273 false { bytes := artifactBytes, pos := 41461, limit := 42734 } =
      .ok ((((Cache.raw.codes[184]!).body).drop 0, .end), { bytes := artifactBytes, pos := 42734, limit := 42734 }) := by
  cbv

end Project.EulerCertificate.Artifact
