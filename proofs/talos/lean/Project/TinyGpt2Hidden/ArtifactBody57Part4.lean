import Project.TinyGpt2Hidden.ArtifactBody57Part3

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body57Tail104 : List Instr := ([Wasm.Binary.Instr.localSet 41,
 Wasm.Binary.Instr.localGet 41,
 Wasm.Binary.Instr.localSet 42,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 43,
 Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 44,
 Wasm.Binary.Instr.localGet 2] ++ body57Tail112)

@[cbv_eval] theorem sequence57_tail104 :
    instructionSequenceAt 954 false { bytes := artifactBytes, pos := 6889, limit := 7739 } =
      .ok ((body57Tail104, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 41,
 Wasm.Binary.Instr.localGet 41,
 Wasm.Binary.Instr.localSet 42,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 43,
 Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 44,
 Wasm.Binary.Instr.localGet 2] ++ body57Tail112), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail96 : List Instr := ([Wasm.Binary.Instr.localSet 38,
 Wasm.Binary.Instr.localGet 38,
 Wasm.Binary.Instr.localSet 52,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 40,
 Wasm.Binary.Instr.call 55] ++ body57Tail104)

@[cbv_eval] theorem sequence57_tail96 :
    instructionSequenceAt 962 false { bytes := artifactBytes, pos := 6873, limit := 7739 } =
      .ok ((body57Tail96, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 38,
 Wasm.Binary.Instr.localGet 38,
 Wasm.Binary.Instr.localSet 52,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 40,
 Wasm.Binary.Instr.call 55] ++ body57Tail104), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail88 : List Instr := ([Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.localGet 35,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.call 25] ++ body57Tail96)

@[cbv_eval] theorem sequence57_tail88 :
    instructionSequenceAt 970 false { bytes := artifactBytes, pos := 6857, limit := 7739 } =
      .ok ((body57Tail88, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.localGet 35,
 Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.call 25] ++ body57Tail96), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail80 : List Instr := ([Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 35,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 28,
 Wasm.Binary.Instr.localGet 29] ++ body57Tail88)

@[cbv_eval] theorem sequence57_tail80 :
    instructionSequenceAt 978 false { bytes := artifactBytes, pos := 6841, limit := 7739 } =
      .ok ((body57Tail80, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 35,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localGet 28,
 Wasm.Binary.Instr.localGet 29] ++ body57Tail88), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail72 : List Instr := ([Wasm.Binary.Instr.localGet 30,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 34] ++ body57Tail80)

@[cbv_eval] theorem sequence57_tail72 :
    instructionSequenceAt 986 false { bytes := artifactBytes, pos := 6825, limit := 7739 } =
      .ok ((body57Tail72, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 30,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 34] ++ body57Tail80), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail64 : List Instr := ([Wasm.Binary.Instr.localGet 27,
 Wasm.Binary.Instr.localSet 51,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 28,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 29,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 30] ++ body57Tail72)

@[cbv_eval] theorem sequence57_tail64 :
    instructionSequenceAt 994 false { bytes := artifactBytes, pos := 6809, limit := 7739 } =
      .ok ((body57Tail64, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 27,
 Wasm.Binary.Instr.localSet 51,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 28,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 29,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 30] ++ body57Tail72), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail56 : List Instr := ([Wasm.Binary.Instr.localGet 21,
 Wasm.Binary.Instr.localGet 22,
 Wasm.Binary.Instr.localGet 23,
 Wasm.Binary.Instr.localGet 24,
 Wasm.Binary.Instr.localGet 25,
 Wasm.Binary.Instr.localGet 26,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 27] ++ body57Tail64)

@[cbv_eval] theorem sequence57_tail56 :
    instructionSequenceAt 1002 false { bytes := artifactBytes, pos := 6793, limit := 7739 } =
      .ok ((body57Tail56, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 21,
 Wasm.Binary.Instr.localGet 22,
 Wasm.Binary.Instr.localGet 23,
 Wasm.Binary.Instr.localGet 24,
 Wasm.Binary.Instr.localGet 25,
 Wasm.Binary.Instr.localGet 26,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 27] ++ body57Tail64), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail48 : List Instr := ([Wasm.Binary.Instr.localSet 24,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 25,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 26,
 Wasm.Binary.Instr.localGet 17,
 Wasm.Binary.Instr.localGet 18,
 Wasm.Binary.Instr.localGet 20] ++ body57Tail56)

@[cbv_eval] theorem sequence57_tail48 :
    instructionSequenceAt 1010 false { bytes := artifactBytes, pos := 6777, limit := 7739 } =
      .ok ((body57Tail48, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 24,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 25,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 26,
 Wasm.Binary.Instr.localGet 17,
 Wasm.Binary.Instr.localGet 18,
 Wasm.Binary.Instr.localGet 20] ++ body57Tail56), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail40 : List Instr := ([Wasm.Binary.Instr.localSet 20,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 21,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.localSet 22,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 23,
 Wasm.Binary.Instr.localGet 3] ++ body57Tail48)

@[cbv_eval] theorem sequence57_tail40 :
    instructionSequenceAt 1018 false { bytes := artifactBytes, pos := 6761, limit := 7739 } =
      .ok ((body57Tail40, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 20,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 21,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.localSet 22,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 23,
 Wasm.Binary.Instr.localGet 3] ++ body57Tail48), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail32 : List Instr := ([Wasm.Binary.Instr.localSet 50,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 17,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 18,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 19,
 Wasm.Binary.Instr.localGet 19] ++ body57Tail40)

@[cbv_eval] theorem sequence57_tail32 :
    instructionSequenceAt 1026 false { bytes := artifactBytes, pos := 6745, limit := 7739 } =
      .ok ((body57Tail32, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 50,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 17,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 18,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 19,
 Wasm.Binary.Instr.localGet 19] ++ body57Tail40), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail24 : List Instr := ([Wasm.Binary.Instr.localGet 11,
 Wasm.Binary.Instr.localGet 12,
 Wasm.Binary.Instr.localGet 13,
 Wasm.Binary.Instr.localGet 14,
 Wasm.Binary.Instr.localGet 15,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 16,
 Wasm.Binary.Instr.localGet 16] ++ body57Tail32)

@[cbv_eval] theorem sequence57_tail24 :
    instructionSequenceAt 1034 false { bytes := artifactBytes, pos := 6729, limit := 7739 } =
      .ok ((body57Tail24, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 11,
 Wasm.Binary.Instr.localGet 12,
 Wasm.Binary.Instr.localGet 13,
 Wasm.Binary.Instr.localGet 14,
 Wasm.Binary.Instr.localGet 15,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 16,
 Wasm.Binary.Instr.localGet 16] ++ body57Tail32), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail16 : List Instr := ([Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 14,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 15,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localGet 10] ++ body57Tail24)

@[cbv_eval] theorem sequence57_tail16 :
    instructionSequenceAt 1042 false { bytes := artifactBytes, pos := 6713, limit := 7739 } =
      .ok ((body57Tail16, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 14,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 15,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localGet 10] ++ body57Tail24), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail8 : List Instr := ([Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 10,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 11,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 12,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 13] ++ body57Tail16)

@[cbv_eval] theorem sequence57_tail8 :
    instructionSequenceAt 1050 false { bytes := artifactBytes, pos := 6697, limit := 7739 } =
      .ok ((body57Tail8, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 10,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 11,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 12,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 13] ++ body57Tail16), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail0 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 7,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 8,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 9] ++ body57Tail8)

@[cbv_eval] theorem sequence57_tail0 :
    instructionSequenceAt 1058 false { bytes := artifactBytes, pos := 6681, limit := 7739 } =
      .ok ((body57Tail0, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 7,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 8,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 9] ++ body57Tail8), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
