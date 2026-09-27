import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_74_t_0_t_tail18 :
    instructionSequenceAt 1347 false { bytes := artifactBytes, pos := 6968, limit := 7717 } =
      .ok ((((((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false)[74]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 7096, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_74_t_0_t_tail0 :
    instructionSequenceAt 1365 false { bytes := artifactBytes, pos := 6937, limit := 7717 } =
      .ok ((((((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false)[74]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7096, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_74_t_tail0 :
    instructionSequenceAt 1367 false { bytes := artifactBytes, pos := 6935, limit := 7717 } =
      .ok ((((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false)[74]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7097, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_78_t_tail8 :
    instructionSequenceAt 1355 true { bytes := artifactBytes, pos := 7117, limit := 7717 } =
      .ok ((((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false)[78]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 7248, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_78_t_tail0 :
    instructionSequenceAt 1363 true { bytes := artifactBytes, pos := 7104, limit := 7717 } =
      .ok ((((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false)[78]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7248, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_tail91 :
    instructionSequenceAt 1352 false { bytes := artifactBytes, pos := 7271, limit := 7717 } =
      .ok ((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 91, .end), { bytes := artifactBytes, pos := 7440, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_tail78 :
    instructionSequenceAt 1365 false { bytes := artifactBytes, pos := 7102, limit := 7717 } =
      .ok ((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 78, .end), { bytes := artifactBytes, pos := 7440, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_tail74 :
    instructionSequenceAt 1369 false { bytes := artifactBytes, pos := 6933, limit := 7717 } =
      .ok ((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 74, .end), { bytes := artifactBytes, pos := 7440, limit := 7717 }) := by
  cbv


end Project.Beck.Artifact
