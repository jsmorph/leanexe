import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Artifact.Binary.DataParts

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem data0_chunk0 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 10677, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 0).take 128, { bytes := artifactBytes, pos := 10805, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk128 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 10805, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 128).take 128, { bytes := artifactBytes, pos := 10933, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk256 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 10933, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 256).take 128, { bytes := artifactBytes, pos := 11061, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk384 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 11061, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 384).take 128, { bytes := artifactBytes, pos := 11189, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk512 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 11189, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 512).take 128, { bytes := artifactBytes, pos := 11317, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk640 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 11317, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 640).take 128, { bytes := artifactBytes, pos := 11445, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk768 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 11445, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 768).take 128, { bytes := artifactBytes, pos := 11573, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk896 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 11573, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 896).take 128, { bytes := artifactBytes, pos := 11701, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk1024 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 11701, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 1024).take 128, { bytes := artifactBytes, pos := 11829, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk1152 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 11829, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 1152).take 128, { bytes := artifactBytes, pos := 11957, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk1280 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 11957, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 1280).take 128, { bytes := artifactBytes, pos := 12085, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk1408 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 12085, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 1408).take 128, { bytes := artifactBytes, pos := 12213, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk1536 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 12213, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 1536).take 128, { bytes := artifactBytes, pos := 12341, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk1664 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 12341, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 1664).take 128, { bytes := artifactBytes, pos := 12469, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk1792 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 12469, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 1792).take 128, { bytes := artifactBytes, pos := 12597, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk1920 :
    Parser.readBytes 128 { bytes := artifactBytes, pos := 12597, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 1920).take 128, { bytes := artifactBytes, pos := 12725, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 128 (by cbv)
  cbv

theorem data0_chunk2048 :
    Parser.readBytes 8 { bytes := artifactBytes, pos := 12725, limit := 12733 } =
      .ok (((Cache.raw.data[0]!).bytes.drop 2048).take 8, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 8 (by cbv)
  cbv

theorem data0_tail2056 :
    Parser.readBytes 0 { bytes := artifactBytes, pos := 12733, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 2056, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  apply readBytes_eq_of_vectorLoop 0 (by cbv)
  cbv

theorem data0_tail2048 :
    Parser.readBytes 8 { bytes := artifactBytes, pos := 12725, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 2048, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk2048 data0_tail2056

theorem data0_tail1920 :
    Parser.readBytes 136 { bytes := artifactBytes, pos := 12597, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 1920, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk1920 data0_tail2048

theorem data0_tail1792 :
    Parser.readBytes 264 { bytes := artifactBytes, pos := 12469, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 1792, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk1792 data0_tail1920

theorem data0_tail1664 :
    Parser.readBytes 392 { bytes := artifactBytes, pos := 12341, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 1664, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk1664 data0_tail1792

theorem data0_tail1536 :
    Parser.readBytes 520 { bytes := artifactBytes, pos := 12213, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 1536, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk1536 data0_tail1664

theorem data0_tail1408 :
    Parser.readBytes 648 { bytes := artifactBytes, pos := 12085, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 1408, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk1408 data0_tail1536

theorem data0_tail1280 :
    Parser.readBytes 776 { bytes := artifactBytes, pos := 11957, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 1280, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk1280 data0_tail1408

theorem data0_tail1152 :
    Parser.readBytes 904 { bytes := artifactBytes, pos := 11829, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 1152, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk1152 data0_tail1280

theorem data0_tail1024 :
    Parser.readBytes 1032 { bytes := artifactBytes, pos := 11701, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 1024, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk1024 data0_tail1152

theorem data0_tail896 :
    Parser.readBytes 1160 { bytes := artifactBytes, pos := 11573, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 896, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk896 data0_tail1024

theorem data0_tail768 :
    Parser.readBytes 1288 { bytes := artifactBytes, pos := 11445, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 768, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk768 data0_tail896

theorem data0_tail640 :
    Parser.readBytes 1416 { bytes := artifactBytes, pos := 11317, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 640, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk640 data0_tail768

theorem data0_tail512 :
    Parser.readBytes 1544 { bytes := artifactBytes, pos := 11189, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 512, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk512 data0_tail640

theorem data0_tail384 :
    Parser.readBytes 1672 { bytes := artifactBytes, pos := 11061, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 384, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk384 data0_tail512

theorem data0_tail256 :
    Parser.readBytes 1800 { bytes := artifactBytes, pos := 10933, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 256, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk256 data0_tail384

theorem data0_tail128 :
    Parser.readBytes 1928 { bytes := artifactBytes, pos := 10805, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 128, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk128 data0_tail256

theorem data0_tail0 :
    Parser.readBytes 2056 { bytes := artifactBytes, pos := 10677, limit := 12733 } =
      .ok ((Cache.raw.data[0]!).bytes.drop 0, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact readBytes_eq_split (by cbv)
    data0_chunk0 data0_tail128

theorem data0_decoded :
    dataSegment { bytes := artifactBytes, pos := 10670, limit := 12733 } =
      .ok (Cache.raw.data[0]!, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine dataSegment_eq_of_parts (count := 2056)
    (afterMode := { bytes := artifactBytes, pos := 10671, limit := 12733 })
    (afterOffset := { bytes := artifactBytes, pos := 10675, limit := 12733 })
    (payload := { bytes := artifactBytes, pos := 10677, limit := 12733 }) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · cbv
  · exact data0_tail0

#print axioms data0_decoded

theorem data_tail1 :
    Internal.vectorLoop dataSegment 0 { bytes := artifactBytes, pos := 12733, limit := 12733 } =
      .ok (Cache.raw.data.drop 1, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by rfl

theorem data_tail0 :
    Internal.vectorLoop dataSegment 1 { bytes := artifactBytes, pos := 10670, limit := 12733 } =
      .ok (Cache.raw.data.drop 0, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  exact vectorLoop_eq_cons data0_decoded data_tail1

theorem data_vector_decoded :
    vector dataSegment { bytes := artifactBytes, pos := 10669, limit := 12733 } =
      .ok (Cache.raw.data, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine vector_eq_of_parts (length := 1)
    (itemsStart := { bytes := artifactBytes, pos := 10670, limit := 12733 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact data_tail0

theorem data_section_decoded :
    sized (vector dataSegment) { bytes := artifactBytes, pos := 10667, limit := 12733 } = .ok (Cache.raw.data, { bytes := artifactBytes, pos := 12733, limit := 12733 }) := by
  refine sized_eq_of_parts (size := 2064)
    (payload := { bytes := artifactBytes, pos := 10669, limit := 12733 }) (finish := { bytes := artifactBytes, pos := 12733, limit := 12733 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact data_vector_decoded
  · rfl

#print axioms data_section_decoded

end Project.ExpArm.Artifact
