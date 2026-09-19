import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_513_t_0_t_tail23 :
    instructionSequenceAt 1624 false { bytes := artifactBytes, pos := 13726, limit := 14558 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[513]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := artifactBytes, pos := 13861, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_513_t_0_t_tail0 :
    instructionSequenceAt 1647 false { bytes := artifactBytes, pos := 13677, limit := 14558 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[513]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13861, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_513_t_tail0 :
    instructionSequenceAt 1649 false { bytes := artifactBytes, pos := 13675, limit := 14558 } =
      .ok ((((((Cache.raw.codes[33]!).body)[513]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13862, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_517_t_tail14 :
    instructionSequenceAt 1631 true { bytes := artifactBytes, pos := 13900, limit := 14558 } =
      .ok ((((((Cache.raw.codes[33]!).body)[517]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 14029, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_517_t_tail0 :
    instructionSequenceAt 1645 true { bytes := artifactBytes, pos := 13870, limit := 14558 } =
      .ok ((((((Cache.raw.codes[33]!).body)[517]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14029, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail579 :
    instructionSequenceAt 1585 false { bytes := artifactBytes, pos := 14425, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 579, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail553 :
    instructionSequenceAt 1611 false { bytes := artifactBytes, pos := 14291, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 553, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail529 :
    instructionSequenceAt 1635 false { bytes := artifactBytes, pos := 14163, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 529, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail521 :
    instructionSequenceAt 1643 false { bytes := artifactBytes, pos := 14034, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 521, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail517 :
    instructionSequenceAt 1647 false { bytes := artifactBytes, pos := 13868, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 517, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail513 :
    instructionSequenceAt 1651 false { bytes := artifactBytes, pos := 13673, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 513, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail473 :
    instructionSequenceAt 1691 false { bytes := artifactBytes, pos := 13543, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 473, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail428 :
    instructionSequenceAt 1736 false { bytes := artifactBytes, pos := 13413, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 428, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail377 :
    instructionSequenceAt 1787 false { bytes := artifactBytes, pos := 13284, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 377, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail324 :
    instructionSequenceAt 1840 false { bytes := artifactBytes, pos := 13156, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 324, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail269 :
    instructionSequenceAt 1895 false { bytes := artifactBytes, pos := 13027, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 269, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail205 :
    instructionSequenceAt 1959 false { bytes := artifactBytes, pos := 12898, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 205, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail152 :
    instructionSequenceAt 2012 false { bytes := artifactBytes, pos := 12770, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 152, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail93 :
    instructionSequenceAt 2071 false { bytes := artifactBytes, pos := 12641, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 93, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail38 :
    instructionSequenceAt 2126 false { bytes := artifactBytes, pos := 12512, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 38, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail0 :
    instructionSequenceAt 2164 false { bytes := artifactBytes, pos := 12394, limit := 14558 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14558, limit := 14558 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 12388, limit := 19083 } = .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 14558, limit := 19083 }) := by
  refine code_eq_of_parts (size := 2168)
    (payload := { bytes := artifactBytes, pos := 12390, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 12394, limit := 14558 })
    (bodyFinish := { bytes := artifactBytes, pos := 14558, limit := 14558 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_33_tail0
  · rfl

#print axioms code33_decoded

end Project.Gpt2CachedStep.Artifact
