import Project.EulerReconstructed.ArtifactCodes144To151Part0
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code144_seq_144_34_t_tail0_decoded :
    instructionSequenceAt 2748 true { bytes := artifactBytes, pos := 27214, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[34]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27358, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_47_t_tail0_decoded :
    instructionSequenceAt 2735 false { bytes := artifactBytes, pos := 27383, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[47]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27563, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_82_t_tail0_decoded :
    instructionSequenceAt 2700 false { bytes := artifactBytes, pos := 27631, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[82]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27793, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_86_t_tail8_decoded :
    instructionSequenceAt 2688 true { bytes := artifactBytes, pos := 27813, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[86]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 27944, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_86_t_tail0_decoded :
    instructionSequenceAt 2696 true { bytes := artifactBytes, pos := 27800, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[86]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27944, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_99_t_tail0_decoded :
    instructionSequenceAt 2683 false { bytes := artifactBytes, pos := 27969, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[99]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 28149, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_152_t_tail0_decoded :
    instructionSequenceAt 2630 false { bytes := artifactBytes, pos := 28250, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[152]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 28412, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_156_t_tail8_decoded :
    instructionSequenceAt 2618 true { bytes := artifactBytes, pos := 28432, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[156]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 28563, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_156_t_tail0_decoded :
    instructionSequenceAt 2626 true { bytes := artifactBytes, pos := 28419, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[156]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 28563, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_209_t_tail0_decoded :
    instructionSequenceAt 2573 false { bytes := artifactBytes, pos := 28771, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[209]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 28933, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_213_t_tail8_decoded :
    instructionSequenceAt 2561 true { bytes := artifactBytes, pos := 28953, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[213]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 29084, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_213_t_tail0_decoded :
    instructionSequenceAt 2569 true { bytes := artifactBytes, pos := 28940, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[213]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 29084, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_328_t_tail0_decoded :
    instructionSequenceAt 2454 false { bytes := artifactBytes, pos := 29292, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[328]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 29454, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_332_t_tail8_decoded :
    instructionSequenceAt 2442 true { bytes := artifactBytes, pos := 29474, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[332]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 29605, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_332_t_tail0_decoded :
    instructionSequenceAt 2450 true { bytes := artifactBytes, pos := 29461, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[332]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 29605, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail345_decoded :
    instructionSequenceAt 2439 false { bytes := artifactBytes, pos := 29628, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 345, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv


end Project.EulerReconstructed.Artifact
