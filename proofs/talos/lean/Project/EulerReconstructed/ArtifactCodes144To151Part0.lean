import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code144_seq_144_30_t_0_t_tail18_decoded :
    instructionSequenceAt 2732 false { bytes := artifactBytes, pos := 27078, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[30]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 27206, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_30_t_0_t_tail0_decoded :
    instructionSequenceAt 2750 false { bytes := artifactBytes, pos := 27047, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[30]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27206, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_47_t_0_t_tail29_decoded :
    instructionSequenceAt 2704 false { bytes := artifactBytes, pos := 27434, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[47]!).childBody false)[0]!).childBody false).drop 29, .end), { bytes := artifactBytes, pos := 27562, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_47_t_0_t_tail0_decoded :
    instructionSequenceAt 2733 false { bytes := artifactBytes, pos := 27385, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[47]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27562, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_82_t_0_t_tail18_decoded :
    instructionSequenceAt 2680 false { bytes := artifactBytes, pos := 27664, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[82]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 27792, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_82_t_0_t_tail0_decoded :
    instructionSequenceAt 2698 false { bytes := artifactBytes, pos := 27633, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[82]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27792, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_99_t_0_t_tail29_decoded :
    instructionSequenceAt 2652 false { bytes := artifactBytes, pos := 28020, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[99]!).childBody false)[0]!).childBody false).drop 29, .end), { bytes := artifactBytes, pos := 28148, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_99_t_0_t_tail0_decoded :
    instructionSequenceAt 2681 false { bytes := artifactBytes, pos := 27971, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[99]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 28148, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_152_t_0_t_tail18_decoded :
    instructionSequenceAt 2610 false { bytes := artifactBytes, pos := 28283, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[152]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 28411, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_152_t_0_t_tail0_decoded :
    instructionSequenceAt 2628 false { bytes := artifactBytes, pos := 28252, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[152]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 28411, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_209_t_0_t_tail18_decoded :
    instructionSequenceAt 2553 false { bytes := artifactBytes, pos := 28804, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[209]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 28932, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_209_t_0_t_tail0_decoded :
    instructionSequenceAt 2571 false { bytes := artifactBytes, pos := 28773, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[209]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 28932, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_328_t_0_t_tail18_decoded :
    instructionSequenceAt 2434 false { bytes := artifactBytes, pos := 29325, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[328]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 29453, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_328_t_0_t_tail0_decoded :
    instructionSequenceAt 2452 false { bytes := artifactBytes, pos := 29294, limit := 29769 } =
      .ok ((((((((Cache.raw.codes[144]!).body)[328]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 29453, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_30_t_tail0_decoded :
    instructionSequenceAt 2752 false { bytes := artifactBytes, pos := 27045, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27207, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_34_t_tail8_decoded :
    instructionSequenceAt 2740 true { bytes := artifactBytes, pos := 27227, limit := 29769 } =
      .ok ((((((Cache.raw.codes[144]!).body)[34]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 27358, limit := 29769 }) := by
  cbv


end Project.EulerReconstructed.Artifact
