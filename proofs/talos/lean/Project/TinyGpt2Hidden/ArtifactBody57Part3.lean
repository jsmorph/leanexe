import Project.TinyGpt2Hidden.ArtifactBody57Part2

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body57Tail232 : List Instr := ([Wasm.Binary.Instr.localSet 87,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 88,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 89,
 Wasm.Binary.Instr.localGet 89,
 Wasm.Binary.Instr.localSet 90,
 Wasm.Binary.Instr.i64Const 8] ++ body57Tail240)

@[cbv_eval] theorem sequence57_tail232 :
    instructionSequenceAt 826 false { bytes := artifactBytes, pos := 7145, limit := 7739 } =
      .ok ((body57Tail232, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 87,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 88,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 89,
 Wasm.Binary.Instr.localGet 89,
 Wasm.Binary.Instr.localSet 90,
 Wasm.Binary.Instr.i64Const 8] ++ body57Tail240), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail224 : List Instr := ([Wasm.Binary.Instr.localGet 83,
 Wasm.Binary.Instr.localGet 84,
 Wasm.Binary.Instr.localGet 85,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 86,
 Wasm.Binary.Instr.localGet 86,
 Wasm.Binary.Instr.localSet 100,
 Wasm.Binary.Instr.localGet 0] ++ body57Tail232)

@[cbv_eval] theorem sequence57_tail224 :
    instructionSequenceAt 834 false { bytes := artifactBytes, pos := 7129, limit := 7739 } =
      .ok ((body57Tail224, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 83,
 Wasm.Binary.Instr.localGet 84,
 Wasm.Binary.Instr.localGet 85,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 86,
 Wasm.Binary.Instr.localGet 86,
 Wasm.Binary.Instr.localSet 100,
 Wasm.Binary.Instr.localGet 0] ++ body57Tail232), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail216 : List Instr := ([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 85,
 Wasm.Binary.Instr.localGet 76,
 Wasm.Binary.Instr.localGet 77,
 Wasm.Binary.Instr.localGet 79,
 Wasm.Binary.Instr.localGet 80,
 Wasm.Binary.Instr.localGet 81,
 Wasm.Binary.Instr.localGet 82] ++ body57Tail224)

@[cbv_eval] theorem sequence57_tail216 :
    instructionSequenceAt 842 false { bytes := artifactBytes, pos := 7113, limit := 7739 } =
      .ok ((body57Tail216, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 85,
 Wasm.Binary.Instr.localGet 76,
 Wasm.Binary.Instr.localGet 77,
 Wasm.Binary.Instr.localGet 79,
 Wasm.Binary.Instr.localGet 80,
 Wasm.Binary.Instr.localGet 81,
 Wasm.Binary.Instr.localGet 82] ++ body57Tail224), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail208 : List Instr := ([Wasm.Binary.Instr.i64Const 6,
 Wasm.Binary.Instr.localSet 81,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 82,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 83,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 84] ++ body57Tail216)

@[cbv_eval] theorem sequence57_tail208 :
    instructionSequenceAt 850 false { bytes := artifactBytes, pos := 7097, limit := 7739 } =
      .ok ((body57Tail208, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 6,
 Wasm.Binary.Instr.localSet 81,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 82,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 83,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 84] ++ body57Tail216), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail200 : List Instr := ([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 77,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 78,
 Wasm.Binary.Instr.localGet 78,
 Wasm.Binary.Instr.localSet 79,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 80] ++ body57Tail208)

@[cbv_eval] theorem sequence57_tail200 :
    instructionSequenceAt 858 false { bytes := artifactBytes, pos := 7081, limit := 7739 } =
      .ok ((body57Tail200, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 77,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 78,
 Wasm.Binary.Instr.localGet 78,
 Wasm.Binary.Instr.localSet 79,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 80] ++ body57Tail208), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail192 : List Instr := ([Wasm.Binary.Instr.localGet 73,
 Wasm.Binary.Instr.localGet 74,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 75,
 Wasm.Binary.Instr.localGet 75,
 Wasm.Binary.Instr.localSet 99,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 76] ++ body57Tail200)

@[cbv_eval] theorem sequence57_tail192 :
    instructionSequenceAt 866 false { bytes := artifactBytes, pos := 7065, limit := 7739 } =
      .ok ((body57Tail192, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 73,
 Wasm.Binary.Instr.localGet 74,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 75,
 Wasm.Binary.Instr.localGet 75,
 Wasm.Binary.Instr.localSet 99,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 76] ++ body57Tail200), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail184 : List Instr := ([Wasm.Binary.Instr.localSet 74,
 Wasm.Binary.Instr.localGet 65,
 Wasm.Binary.Instr.localGet 66,
 Wasm.Binary.Instr.localGet 68,
 Wasm.Binary.Instr.localGet 69,
 Wasm.Binary.Instr.localGet 70,
 Wasm.Binary.Instr.localGet 71,
 Wasm.Binary.Instr.localGet 72] ++ body57Tail192)

@[cbv_eval] theorem sequence57_tail184 :
    instructionSequenceAt 874 false { bytes := artifactBytes, pos := 7049, limit := 7739 } =
      .ok ((body57Tail184, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 74,
 Wasm.Binary.Instr.localGet 65,
 Wasm.Binary.Instr.localGet 66,
 Wasm.Binary.Instr.localGet 68,
 Wasm.Binary.Instr.localGet 69,
 Wasm.Binary.Instr.localGet 70,
 Wasm.Binary.Instr.localGet 71,
 Wasm.Binary.Instr.localGet 72] ++ body57Tail192), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail176 : List Instr := ([Wasm.Binary.Instr.localSet 70,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 71,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 72,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 73,
 Wasm.Binary.Instr.localGet 5] ++ body57Tail184)

@[cbv_eval] theorem sequence57_tail176 :
    instructionSequenceAt 882 false { bytes := artifactBytes, pos := 7033, limit := 7739 } =
      .ok ((body57Tail176, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 70,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 71,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 72,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 73,
 Wasm.Binary.Instr.localGet 5] ++ body57Tail184), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail168 : List Instr := ([Wasm.Binary.Instr.localSet 66,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 67,
 Wasm.Binary.Instr.localGet 67,
 Wasm.Binary.Instr.localSet 68,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 69,
 Wasm.Binary.Instr.i64Const 5] ++ body57Tail176)

@[cbv_eval] theorem sequence57_tail168 :
    instructionSequenceAt 890 false { bytes := artifactBytes, pos := 7017, limit := 7739 } =
      .ok ((body57Tail168, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 66,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 67,
 Wasm.Binary.Instr.localGet 67,
 Wasm.Binary.Instr.localSet 68,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 69,
 Wasm.Binary.Instr.i64Const 5] ++ body57Tail176), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail160 : List Instr := ([Wasm.Binary.Instr.localGet 63,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 64,
 Wasm.Binary.Instr.localGet 64,
 Wasm.Binary.Instr.localSet 98,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 65,
 Wasm.Binary.Instr.localGet 1] ++ body57Tail168)

@[cbv_eval] theorem sequence57_tail160 :
    instructionSequenceAt 898 false { bytes := artifactBytes, pos := 7001, limit := 7739 } =
      .ok ((body57Tail160, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 63,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 64,
 Wasm.Binary.Instr.localGet 64,
 Wasm.Binary.Instr.localSet 98,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 65,
 Wasm.Binary.Instr.localGet 1] ++ body57Tail168), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail152 : List Instr := ([Wasm.Binary.Instr.localGet 54,
 Wasm.Binary.Instr.localGet 55,
 Wasm.Binary.Instr.localGet 57,
 Wasm.Binary.Instr.localGet 58,
 Wasm.Binary.Instr.localGet 59,
 Wasm.Binary.Instr.localGet 60,
 Wasm.Binary.Instr.localGet 61,
 Wasm.Binary.Instr.localGet 62] ++ body57Tail160)

@[cbv_eval] theorem sequence57_tail152 :
    instructionSequenceAt 906 false { bytes := artifactBytes, pos := 6985, limit := 7739 } =
      .ok ((body57Tail152, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 54,
 Wasm.Binary.Instr.localGet 55,
 Wasm.Binary.Instr.localGet 57,
 Wasm.Binary.Instr.localGet 58,
 Wasm.Binary.Instr.localGet 59,
 Wasm.Binary.Instr.localGet 60,
 Wasm.Binary.Instr.localGet 61,
 Wasm.Binary.Instr.localGet 62] ++ body57Tail160), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail144 : List Instr := ([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 60,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 61,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 62,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 63] ++ body57Tail152)

@[cbv_eval] theorem sequence57_tail144 :
    instructionSequenceAt 914 false { bytes := artifactBytes, pos := 6969, limit := 7739 } =
      .ok ((body57Tail144, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 60,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 61,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 62,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 63] ++ body57Tail152), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail136 : List Instr := ([Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 56,
 Wasm.Binary.Instr.localGet 56,
 Wasm.Binary.Instr.localSet 57,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 58,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 59] ++ body57Tail144)

@[cbv_eval] theorem sequence57_tail136 :
    instructionSequenceAt 922 false { bytes := artifactBytes, pos := 6953, limit := 7739 } =
      .ok ((body57Tail136, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 56,
 Wasm.Binary.Instr.localGet 56,
 Wasm.Binary.Instr.localSet 57,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 58,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 59] ++ body57Tail144), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail128 : List Instr := ([Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 49,
 Wasm.Binary.Instr.localGet 49,
 Wasm.Binary.Instr.localSet 53,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 54,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 55] ++ body57Tail136)

@[cbv_eval] theorem sequence57_tail128 :
    instructionSequenceAt 930 false { bytes := artifactBytes, pos := 6937, limit := 7739 } =
      .ok ((body57Tail128, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 49,
 Wasm.Binary.Instr.localGet 49,
 Wasm.Binary.Instr.localSet 53,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 54,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 55] ++ body57Tail136), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail120 : List Instr := ([Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.localGet 42,
 Wasm.Binary.Instr.localGet 43,
 Wasm.Binary.Instr.localGet 44,
 Wasm.Binary.Instr.localGet 45,
 Wasm.Binary.Instr.localGet 46,
 Wasm.Binary.Instr.localGet 47,
 Wasm.Binary.Instr.localGet 48] ++ body57Tail128)

@[cbv_eval] theorem sequence57_tail120 :
    instructionSequenceAt 938 false { bytes := artifactBytes, pos := 6921, limit := 7739 } =
      .ok ((body57Tail120, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.localGet 42,
 Wasm.Binary.Instr.localGet 43,
 Wasm.Binary.Instr.localGet 44,
 Wasm.Binary.Instr.localGet 45,
 Wasm.Binary.Instr.localGet 46,
 Wasm.Binary.Instr.localGet 47,
 Wasm.Binary.Instr.localGet 48] ++ body57Tail128), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail112 : List Instr := ([Wasm.Binary.Instr.localSet 45,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 46,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 47,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 48,
 Wasm.Binary.Instr.localGet 39] ++ body57Tail120)

@[cbv_eval] theorem sequence57_tail112 :
    instructionSequenceAt 946 false { bytes := artifactBytes, pos := 6905, limit := 7739 } =
      .ok ((body57Tail112, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 45,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 46,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 47,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 48,
 Wasm.Binary.Instr.localGet 39] ++ body57Tail120), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
