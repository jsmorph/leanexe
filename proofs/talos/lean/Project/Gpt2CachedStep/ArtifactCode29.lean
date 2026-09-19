import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_29_320_t_0_t_33_t_0_t_tail62 :
    instructionSequenceAt 3291 false { bytes := artifactBytes, pos := 10758, limit := 11065 } =
      .ok ((((((((((((Cache.raw.codes[29]!).body)[320]!).childBody false)[0]!).childBody false)[33]!).childBody false)[0]!).childBody false).drop 62, .end), { bytes := artifactBytes, pos := 10886, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_320_t_0_t_33_t_0_t_tail10 :
    instructionSequenceAt 3343 false { bytes := artifactBytes, pos := 10629, limit := 11065 } =
      .ok ((((((((((((Cache.raw.codes[29]!).body)[320]!).childBody false)[0]!).childBody false)[33]!).childBody false)[0]!).childBody false).drop 10, .end), { bytes := artifactBytes, pos := 10886, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_320_t_0_t_33_t_0_t_tail0 :
    instructionSequenceAt 3353 false { bytes := artifactBytes, pos := 10610, limit := 11065 } =
      .ok ((((((((((((Cache.raw.codes[29]!).body)[320]!).childBody false)[0]!).childBody false)[33]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10886, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_320_t_0_t_33_t_tail0 :
    instructionSequenceAt 3355 false { bytes := artifactBytes, pos := 10608, limit := 11065 } =
      .ok ((((((((((Cache.raw.codes[29]!).body)[320]!).childBody false)[0]!).childBody false)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10887, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_48_t_0_t_tail18 :
    instructionSequenceAt 3644 false { bytes := artifactBytes, pos := 7528, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[48]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 7656, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_48_t_0_t_tail0 :
    instructionSequenceAt 3662 false { bytes := artifactBytes, pos := 7497, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[48]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7656, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_61_t_0_t_tail6 :
    instructionSequenceAt 3643 false { bytes := artifactBytes, pos := 7837, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[61]!).childBody false)[0]!).childBody false).drop 6, .end), { bytes := artifactBytes, pos := 7966, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_61_t_0_t_tail0 :
    instructionSequenceAt 3649 false { bytes := artifactBytes, pos := 7827, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[61]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7966, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_97_t_0_t_tail18 :
    instructionSequenceAt 3595 false { bytes := artifactBytes, pos := 8094, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[97]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 8222, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_97_t_0_t_tail0 :
    instructionSequenceAt 3613 false { bytes := artifactBytes, pos := 8063, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[97]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8222, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_153_t_0_t_tail18 :
    instructionSequenceAt 3539 false { bytes := artifactBytes, pos := 8621, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[153]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 8749, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_153_t_0_t_tail0 :
    instructionSequenceAt 3557 false { bytes := artifactBytes, pos := 8590, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[153]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8749, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_202_t_0_t_tail18 :
    instructionSequenceAt 3490 false { bytes := artifactBytes, pos := 9168, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[202]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 9296, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_202_t_0_t_tail0 :
    instructionSequenceAt 3508 false { bytes := artifactBytes, pos := 9137, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[202]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9296, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_258_t_0_t_tail18 :
    instructionSequenceAt 3434 false { bytes := artifactBytes, pos := 9695, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[258]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 9823, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_258_t_0_t_tail0 :
    instructionSequenceAt 3452 false { bytes := artifactBytes, pos := 9664, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[258]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9823, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_307_t_0_t_tail18 :
    instructionSequenceAt 3385 false { bytes := artifactBytes, pos := 10237, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[307]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 10365, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_307_t_0_t_tail0 :
    instructionSequenceAt 3403 false { bytes := artifactBytes, pos := 10206, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[307]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10365, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_320_t_0_t_tail33 :
    instructionSequenceAt 3357 false { bytes := artifactBytes, pos := 10606, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[320]!).childBody false)[0]!).childBody false).drop 33, .end), { bytes := artifactBytes, pos := 10911, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_320_t_0_t_tail0 :
    instructionSequenceAt 3390 false { bytes := artifactBytes, pos := 10536, limit := 11065 } =
      .ok ((((((((Cache.raw.codes[29]!).body)[320]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10911, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_48_t_tail0 :
    instructionSequenceAt 3664 false { bytes := artifactBytes, pos := 7495, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[48]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7657, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_52_t_tail8 :
    instructionSequenceAt 3652 true { bytes := artifactBytes, pos := 7677, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[52]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 7808, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_52_t_tail0 :
    instructionSequenceAt 3660 true { bytes := artifactBytes, pos := 7664, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[52]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7808, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_61_t_tail0 :
    instructionSequenceAt 3651 false { bytes := artifactBytes, pos := 7825, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[61]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7967, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_97_t_tail0 :
    instructionSequenceAt 3615 false { bytes := artifactBytes, pos := 8061, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[97]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8223, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_101_t_tail8 :
    instructionSequenceAt 3603 true { bytes := artifactBytes, pos := 8243, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[101]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 8374, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_101_t_tail0 :
    instructionSequenceAt 3611 true { bytes := artifactBytes, pos := 8230, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[101]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8374, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_153_t_tail0 :
    instructionSequenceAt 3559 false { bytes := artifactBytes, pos := 8588, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[153]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8750, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_157_t_tail8 :
    instructionSequenceAt 3547 true { bytes := artifactBytes, pos := 8770, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[157]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 8901, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_157_t_tail0 :
    instructionSequenceAt 3555 true { bytes := artifactBytes, pos := 8757, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[157]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8901, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_202_t_tail0 :
    instructionSequenceAt 3510 false { bytes := artifactBytes, pos := 9135, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[202]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9297, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_206_t_tail8 :
    instructionSequenceAt 3498 true { bytes := artifactBytes, pos := 9317, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[206]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 9448, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_206_t_tail0 :
    instructionSequenceAt 3506 true { bytes := artifactBytes, pos := 9304, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[206]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9448, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_258_t_tail0 :
    instructionSequenceAt 3454 false { bytes := artifactBytes, pos := 9662, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[258]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9824, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_262_t_tail8 :
    instructionSequenceAt 3442 true { bytes := artifactBytes, pos := 9844, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[262]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 9975, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_262_t_tail0 :
    instructionSequenceAt 3450 true { bytes := artifactBytes, pos := 9831, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[262]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9975, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_307_t_tail0 :
    instructionSequenceAt 3405 false { bytes := artifactBytes, pos := 10204, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[307]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10366, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_311_t_tail8 :
    instructionSequenceAt 3393 true { bytes := artifactBytes, pos := 10386, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[311]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 10517, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_311_t_tail0 :
    instructionSequenceAt 3401 true { bytes := artifactBytes, pos := 10373, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[311]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10517, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_320_t_tail0 :
    instructionSequenceAt 3392 false { bytes := artifactBytes, pos := 10534, limit := 11065 } =
      .ok ((((((Cache.raw.codes[29]!).body)[320]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10912, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail333 :
    instructionSequenceAt 3381 false { bytes := artifactBytes, pos := 10934, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 333, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail320 :
    instructionSequenceAt 3394 false { bytes := artifactBytes, pos := 10532, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 320, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail311 :
    instructionSequenceAt 3403 false { bytes := artifactBytes, pos := 10371, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 311, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail307 :
    instructionSequenceAt 3407 false { bytes := artifactBytes, pos := 10202, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 307, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail271 :
    instructionSequenceAt 3443 false { bytes := artifactBytes, pos := 9990, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 271, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail262 :
    instructionSequenceAt 3452 false { bytes := artifactBytes, pos := 9829, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 262, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail258 :
    instructionSequenceAt 3456 false { bytes := artifactBytes, pos := 9660, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 258, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail215 :
    instructionSequenceAt 3499 false { bytes := artifactBytes, pos := 9463, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 215, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail206 :
    instructionSequenceAt 3508 false { bytes := artifactBytes, pos := 9302, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 206, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail202 :
    instructionSequenceAt 3512 false { bytes := artifactBytes, pos := 9133, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 202, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail166 :
    instructionSequenceAt 3548 false { bytes := artifactBytes, pos := 8916, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 166, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail157 :
    instructionSequenceAt 3557 false { bytes := artifactBytes, pos := 8755, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 157, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail153 :
    instructionSequenceAt 3561 false { bytes := artifactBytes, pos := 8586, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 153, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail110 :
    instructionSequenceAt 3604 false { bytes := artifactBytes, pos := 8389, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 110, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail101 :
    instructionSequenceAt 3613 false { bytes := artifactBytes, pos := 8228, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 101, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail97 :
    instructionSequenceAt 3617 false { bytes := artifactBytes, pos := 8059, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 97, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail61 :
    instructionSequenceAt 3653 false { bytes := artifactBytes, pos := 7823, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 61, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail52 :
    instructionSequenceAt 3662 false { bytes := artifactBytes, pos := 7662, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 52, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail48 :
    instructionSequenceAt 3666 false { bytes := artifactBytes, pos := 7493, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 48, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail7 :
    instructionSequenceAt 3707 false { bytes := artifactBytes, pos := 7364, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 7, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

@[cbv_eval] theorem sequence_29_tail0 :
    instructionSequenceAt 3714 false { bytes := artifactBytes, pos := 7351, limit := 11065 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11065, limit := 11065 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 7346, limit := 19083 } = .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 11065, limit := 19083 }) := by
  refine code_eq_of_parts (size := 3717)
    (payload := { bytes := artifactBytes, pos := 7348, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 7351, limit := 11065 })
    (bodyFinish := { bytes := artifactBytes, pos := 11065, limit := 11065 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_29_tail0
  · rfl

#print axioms code29_decoded

end Project.Gpt2CachedStep.Artifact
