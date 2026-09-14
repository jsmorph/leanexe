import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code48_seq_48_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5598, limit := 5605 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5605, limit := 5605 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 5594, limit := 7175 } =
      .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 5605, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5595, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5598, limit := 5605 })
    (bodyFinish := { bytes := artifactBytes, pos := 5605, limit := 5605 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code48_seq_48_tail0_decoded
  · rfl

#print axioms code48_decoded

@[cbv_eval] theorem code49_seq_49_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5609, limit := 5616 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5616, limit := 5616 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 5605, limit := 7175 } =
      .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 5616, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5606, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5609, limit := 5616 })
    (bodyFinish := { bytes := artifactBytes, pos := 5616, limit := 5616 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code49_seq_49_tail0_decoded
  · rfl

#print axioms code49_decoded

@[cbv_eval] theorem code50_seq_50_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5620, limit := 5627 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5627, limit := 5627 }) := by
  cbv

theorem code50_decoded :
    code { bytes := artifactBytes, pos := 5616, limit := 7175 } =
      .ok (Cache.raw.codes[50]!, { bytes := artifactBytes, pos := 5627, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5617, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5620, limit := 5627 })
    (bodyFinish := { bytes := artifactBytes, pos := 5627, limit := 5627 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code50_seq_50_tail0_decoded
  · rfl

#print axioms code50_decoded

@[cbv_eval] theorem code51_seq_51_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5631, limit := 5638 } =
      .ok ((((Cache.raw.codes[51]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5638, limit := 5638 }) := by
  cbv

theorem code51_decoded :
    code { bytes := artifactBytes, pos := 5627, limit := 7175 } =
      .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 5638, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5628, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5631, limit := 5638 })
    (bodyFinish := { bytes := artifactBytes, pos := 5638, limit := 5638 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code51_seq_51_tail0_decoded
  · rfl

#print axioms code51_decoded

@[cbv_eval] theorem code52_seq_52_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5642, limit := 5649 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5649, limit := 5649 }) := by
  cbv

theorem code52_decoded :
    code { bytes := artifactBytes, pos := 5638, limit := 7175 } =
      .ok (Cache.raw.codes[52]!, { bytes := artifactBytes, pos := 5649, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5639, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5642, limit := 5649 })
    (bodyFinish := { bytes := artifactBytes, pos := 5649, limit := 5649 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code52_seq_52_tail0_decoded
  · rfl

#print axioms code52_decoded

@[cbv_eval] theorem code53_seq_53_tail0_decoded :
    instructionSequenceAt 37 false { bytes := artifactBytes, pos := 5653, limit := 5690 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5690, limit := 5690 }) := by
  cbv

theorem code53_decoded :
    code { bytes := artifactBytes, pos := 5649, limit := 7175 } =
      .ok (Cache.raw.codes[53]!, { bytes := artifactBytes, pos := 5690, limit := 7175 }) := by
  refine code_eq_of_parts (size := 40)
    (payload := { bytes := artifactBytes, pos := 5650, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5653, limit := 5690 })
    (bodyFinish := { bytes := artifactBytes, pos := 5690, limit := 5690 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code53_seq_53_tail0_decoded
  · rfl

#print axioms code53_decoded

@[cbv_eval] theorem code54_seq_54_43_t_43_t_tail102_decoded :
    instructionSequenceAt 459 true { bytes := artifactBytes, pos := 6141, limit := 6346 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[43]!).childBody false)[43]!).childBody false).drop 102, .otherwise), { bytes := artifactBytes, pos := 6254, limit := 6346 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_43_t_tail61_decoded :
    instructionSequenceAt 500 true { bytes := artifactBytes, pos := 6014, limit := 6346 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[43]!).childBody false)[43]!).childBody false).drop 61, .otherwise), { bytes := artifactBytes, pos := 6254, limit := 6346 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_43_t_tail0_decoded :
    instructionSequenceAt 561 true { bytes := artifactBytes, pos := 5887, limit := 6346 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[43]!).childBody false)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 6254, limit := 6346 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_tail44_decoded :
    instructionSequenceAt 562 true { bytes := artifactBytes, pos := 6293, limit := 6346 } =
      .ok ((((((Cache.raw.codes[54]!).body)[43]!).childBody false).drop 44, .otherwise), { bytes := artifactBytes, pos := 6294, limit := 6346 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_tail43_decoded :
    instructionSequenceAt 563 true { bytes := artifactBytes, pos := 5885, limit := 6346 } =
      .ok ((((((Cache.raw.codes[54]!).body)[43]!).childBody false).drop 43, .otherwise), { bytes := artifactBytes, pos := 6294, limit := 6346 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_tail0_decoded :
    instructionSequenceAt 606 true { bytes := artifactBytes, pos := 5791, limit := 6346 } =
      .ok ((((((Cache.raw.codes[54]!).body)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 6294, limit := 6346 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail44_decoded :
    instructionSequenceAt 607 false { bytes := artifactBytes, pos := 6333, limit := 6346 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 44, .end), { bytes := artifactBytes, pos := 6346, limit := 6346 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail43_decoded :
    instructionSequenceAt 608 false { bytes := artifactBytes, pos := 5789, limit := 6346 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 43, .end), { bytes := artifactBytes, pos := 6346, limit := 6346 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail0_decoded :
    instructionSequenceAt 651 false { bytes := artifactBytes, pos := 5695, limit := 6346 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6346, limit := 6346 }) := by
  cbv

theorem code54_decoded :
    code { bytes := artifactBytes, pos := 5690, limit := 7175 } =
      .ok (Cache.raw.codes[54]!, { bytes := artifactBytes, pos := 6346, limit := 7175 }) := by
  refine code_eq_of_parts (size := 654)
    (payload := { bytes := artifactBytes, pos := 5692, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5695, limit := 6346 })
    (bodyFinish := { bytes := artifactBytes, pos := 6346, limit := 6346 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code54_seq_54_tail0_decoded
  · rfl

#print axioms code54_decoded

@[cbv_eval] theorem code55_seq_55_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 6423, limit := 6713 } =
      .ok ((((((((Cache.raw.codes[55]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 6551, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 6392, limit := 6713 } =
      .ok ((((((((Cache.raw.codes[55]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6551, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_18_t_tail1_decoded :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 6551, limit := 6713 } =
      .ok ((((((Cache.raw.codes[55]!).body)[18]!).childBody false).drop 1, .end), { bytes := artifactBytes, pos := 6552, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 6390, limit := 6713 } =
      .ok ((((((Cache.raw.codes[55]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6552, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_22_t_tail9_decoded :
    instructionSequenceAt 329 true { bytes := artifactBytes, pos := 6576, limit := 6713 } =
      .ok ((((((Cache.raw.codes[55]!).body)[22]!).childBody false).drop 9, .end), { bytes := artifactBytes, pos := 6703, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 6559, limit := 6713 } =
      .ok ((((((Cache.raw.codes[55]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6703, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_tail23_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 6703, limit := 6713 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 23, .end), { bytes := artifactBytes, pos := 6713, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 6557, limit := 6713 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 22, .end), { bytes := artifactBytes, pos := 6713, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_tail19_decoded :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 6552, limit := 6713 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 19, .end), { bytes := artifactBytes, pos := 6713, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 6388, limit := 6713 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 18, .end), { bytes := artifactBytes, pos := 6713, limit := 6713 }) := by
  cbv

@[cbv_eval] theorem code55_seq_55_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 6351, limit := 6713 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6713, limit := 6713 }) := by
  cbv

theorem code55_decoded :
    code { bytes := artifactBytes, pos := 6346, limit := 7175 } =
      .ok (Cache.raw.codes[55]!, { bytes := artifactBytes, pos := 6713, limit := 7175 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 6348, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 6351, limit := 6713 })
    (bodyFinish := { bytes := artifactBytes, pos := 6713, limit := 6713 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code55_seq_55_tail0_decoded
  · rfl

#print axioms code55_decoded


end Project.EulerOutwardFlux.Artifact
