import Project.EulerReconstructed.ArtifactCodes144To151Part1
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code144_seq_144_tail332_decoded :
    instructionSequenceAt 2452 false { bytes := artifactBytes, pos := 29459, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 332, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail328_decoded :
    instructionSequenceAt 2456 false { bytes := artifactBytes, pos := 29290, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 328, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail258_decoded :
    instructionSequenceAt 2526 false { bytes := artifactBytes, pos := 29162, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 258, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail213_decoded :
    instructionSequenceAt 2571 false { bytes := artifactBytes, pos := 28938, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 213, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail209_decoded :
    instructionSequenceAt 2575 false { bytes := artifactBytes, pos := 28769, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 209, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail171_decoded :
    instructionSequenceAt 2613 false { bytes := artifactBytes, pos := 28640, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 171, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail156_decoded :
    instructionSequenceAt 2628 false { bytes := artifactBytes, pos := 28417, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 156, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail152_decoded :
    instructionSequenceAt 2632 false { bytes := artifactBytes, pos := 28248, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 152, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail99_decoded :
    instructionSequenceAt 2685 false { bytes := artifactBytes, pos := 27967, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 99, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail86_decoded :
    instructionSequenceAt 2698 false { bytes := artifactBytes, pos := 27798, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 86, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail82_decoded :
    instructionSequenceAt 2702 false { bytes := artifactBytes, pos := 27629, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 82, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail47_decoded :
    instructionSequenceAt 2737 false { bytes := artifactBytes, pos := 27381, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 47, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail34_decoded :
    instructionSequenceAt 2750 false { bytes := artifactBytes, pos := 27212, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 34, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail30_decoded :
    instructionSequenceAt 2754 false { bytes := artifactBytes, pos := 27043, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 30, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

@[cbv_eval] theorem code144_seq_144_tail0_decoded :
    instructionSequenceAt 2784 false { bytes := artifactBytes, pos := 26985, limit := 29769 } =
      .ok ((((Cache.raw.codes[144]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29769, limit := 29769 }) := by
  cbv

theorem code144_decoded :
    code { bytes := artifactBytes, pos := 26980, limit := 30726 } =
      .ok (Cache.raw.codes[144]!, { bytes := artifactBytes, pos := 29769, limit := 30726 }) := by
  refine code_eq_of_parts (size := 2787)
    (payload := { bytes := artifactBytes, pos := 26982, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 26985, limit := 29769 })
    (bodyFinish := { bytes := artifactBytes, pos := 29769, limit := 29769 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code144_seq_144_tail0_decoded
  · rfl

#print axioms code144_decoded


end Project.EulerReconstructed.Artifact
