import Project.TinyGpt2Hidden.ArtifactBody74Part14

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail152 : List Instr := ([Wasm.Binary.Instr.localGet 66,
 Wasm.Binary.Instr.localGet 67,
 Wasm.Binary.Instr.localGet 69,
 Wasm.Binary.Instr.localGet 70,
 Wasm.Binary.Instr.localGet 71,
 Wasm.Binary.Instr.localGet 72,
 Wasm.Binary.Instr.localGet 73,
 Wasm.Binary.Instr.call 17] ++ body74Tail160)

@[cbv_eval] theorem sequence74_tail152 :
    instructionSequenceAt 5024 false { bytes := artifactBytes, pos := 10305, limit := 15177 } =
      .ok ((body74Tail152, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 66,
 Wasm.Binary.Instr.localGet 67,
 Wasm.Binary.Instr.localGet 69,
 Wasm.Binary.Instr.localGet 70,
 Wasm.Binary.Instr.localGet 71,
 Wasm.Binary.Instr.localGet 72,
 Wasm.Binary.Instr.localGet 73,
 Wasm.Binary.Instr.call 17] ++ body74Tail160), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail144 : List Instr := ([Wasm.Binary.Instr.localGet 42,
 Wasm.Binary.Instr.localSet 70,
 Wasm.Binary.Instr.localGet 43,
 Wasm.Binary.Instr.localSet 71,
 Wasm.Binary.Instr.localGet 44,
 Wasm.Binary.Instr.localSet 72,
 Wasm.Binary.Instr.localGet 45,
 Wasm.Binary.Instr.localSet 73] ++ body74Tail152)

@[cbv_eval] theorem sequence74_tail144 :
    instructionSequenceAt 5032 false { bytes := artifactBytes, pos := 10289, limit := 15177 } =
      .ok ((body74Tail144, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 42,
 Wasm.Binary.Instr.localSet 70,
 Wasm.Binary.Instr.localGet 43,
 Wasm.Binary.Instr.localSet 71,
 Wasm.Binary.Instr.localGet 44,
 Wasm.Binary.Instr.localSet 72,
 Wasm.Binary.Instr.localGet 45,
 Wasm.Binary.Instr.localSet 73] ++ body74Tail152), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail136 : List Instr := ([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 66,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 67,
 Wasm.Binary.Instr.call 18,
 Wasm.Binary.Instr.localSet 68,
 Wasm.Binary.Instr.localGet 68,
 Wasm.Binary.Instr.localSet 69] ++ body74Tail144)

@[cbv_eval] theorem sequence74_tail136 :
    instructionSequenceAt 5040 false { bytes := artifactBytes, pos := 10273, limit := 15177 } =
      .ok ((body74Tail136, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 66,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 67,
 Wasm.Binary.Instr.call 18,
 Wasm.Binary.Instr.localSet 68,
 Wasm.Binary.Instr.localGet 68,
 Wasm.Binary.Instr.localSet 69] ++ body74Tail144), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail128 : List Instr := ([Wasm.Binary.Instr.localGet 62,
 Wasm.Binary.Instr.localSet 102,
 Wasm.Binary.Instr.localGet 63,
 Wasm.Binary.Instr.localSet 103,
 Wasm.Binary.Instr.localGet 64,
 Wasm.Binary.Instr.localSet 104,
 Wasm.Binary.Instr.localGet 65,
 Wasm.Binary.Instr.localSet 105] ++ body74Tail136)

@[cbv_eval] theorem sequence74_tail128 :
    instructionSequenceAt 5048 false { bytes := artifactBytes, pos := 10257, limit := 15177 } =
      .ok ((body74Tail128, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 62,
 Wasm.Binary.Instr.localSet 102,
 Wasm.Binary.Instr.localGet 63,
 Wasm.Binary.Instr.localSet 103,
 Wasm.Binary.Instr.localGet 64,
 Wasm.Binary.Instr.localSet 104,
 Wasm.Binary.Instr.localGet 65,
 Wasm.Binary.Instr.localSet 105] ++ body74Tail136), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail120 : List Instr := ([Wasm.Binary.Instr.localGet 59,
 Wasm.Binary.Instr.localGet 60,
 Wasm.Binary.Instr.localGet 61,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 65,
 Wasm.Binary.Instr.localSet 64,
 Wasm.Binary.Instr.localSet 63,
 Wasm.Binary.Instr.localSet 62] ++ body74Tail128)

@[cbv_eval] theorem sequence74_tail120 :
    instructionSequenceAt 5056 false { bytes := artifactBytes, pos := 10241, limit := 15177 } =
      .ok ((body74Tail120, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 59,
 Wasm.Binary.Instr.localGet 60,
 Wasm.Binary.Instr.localGet 61,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 65,
 Wasm.Binary.Instr.localSet 64,
 Wasm.Binary.Instr.localSet 63,
 Wasm.Binary.Instr.localSet 62] ++ body74Tail128), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail112 : List Instr := ([Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.localSet 60,
 Wasm.Binary.Instr.localGet 41,
 Wasm.Binary.Instr.localSet 61,
 Wasm.Binary.Instr.localGet 54,
 Wasm.Binary.Instr.localGet 55,
 Wasm.Binary.Instr.localGet 57,
 Wasm.Binary.Instr.localGet 58] ++ body74Tail120)

@[cbv_eval] theorem sequence74_tail112 :
    instructionSequenceAt 5064 false { bytes := artifactBytes, pos := 10225, limit := 15177 } =
      .ok ((body74Tail112, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.localSet 60,
 Wasm.Binary.Instr.localGet 41,
 Wasm.Binary.Instr.localSet 61,
 Wasm.Binary.Instr.localGet 54,
 Wasm.Binary.Instr.localGet 55,
 Wasm.Binary.Instr.localGet 57,
 Wasm.Binary.Instr.localGet 58] ++ body74Tail120), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail104 : List Instr := ([Wasm.Binary.Instr.call 18,
 Wasm.Binary.Instr.localSet 56,
 Wasm.Binary.Instr.localGet 56,
 Wasm.Binary.Instr.localSet 57,
 Wasm.Binary.Instr.localGet 38,
 Wasm.Binary.Instr.localSet 58,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.localSet 59] ++ body74Tail112)

@[cbv_eval] theorem sequence74_tail104 :
    instructionSequenceAt 5072 false { bytes := artifactBytes, pos := 10209, limit := 15177 } =
      .ok ((body74Tail104, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 18,
 Wasm.Binary.Instr.localSet 56,
 Wasm.Binary.Instr.localGet 56,
 Wasm.Binary.Instr.localSet 57,
 Wasm.Binary.Instr.localGet 38,
 Wasm.Binary.Instr.localSet 58,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.localSet 59] ++ body74Tail112), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail96 : List Instr := ([Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localSet 52,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.localSet 53,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 54,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 55] ++ body74Tail104)

@[cbv_eval] theorem sequence74_tail96 :
    instructionSequenceAt 5080 false { bytes := artifactBytes, pos := 10193, limit := 15177 } =
      .ok ((body74Tail96, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 36,
 Wasm.Binary.Instr.localSet 52,
 Wasm.Binary.Instr.localGet 37,
 Wasm.Binary.Instr.localSet 53,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 54,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 55] ++ body74Tail104), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail88 : List Instr := ([Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.localSet 35,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.localSet 50,
 Wasm.Binary.Instr.localGet 35,
 Wasm.Binary.Instr.localSet 51] ++ body74Tail96)

@[cbv_eval] theorem sequence74_tail88 :
    instructionSequenceAt 5088 false { bytes := artifactBytes, pos := 10177, limit := 15177 } =
      .ok ((body74Tail88, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 37,
 Wasm.Binary.Instr.localSet 36,
 Wasm.Binary.Instr.localSet 35,
 Wasm.Binary.Instr.localSet 34,
 Wasm.Binary.Instr.localGet 34,
 Wasm.Binary.Instr.localSet 50,
 Wasm.Binary.Instr.localGet 35,
 Wasm.Binary.Instr.localSet 51] ++ body74Tail96), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail80 : List Instr := ([Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 30,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.call 8] ++ body74Tail88)

@[cbv_eval] theorem sequence74_tail80 :
    instructionSequenceAt 5096 false { bytes := artifactBytes, pos := 10161, limit := 15177 } =
      .ok ((body74Tail80, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 32,
 Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 33,
 Wasm.Binary.Instr.localGet 30,
 Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.localGet 33,
 Wasm.Binary.Instr.call 8] ++ body74Tail88), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail72 : List Instr := ([Wasm.Binary.Instr.localSet 48,
 Wasm.Binary.Instr.localGet 29,
 Wasm.Binary.Instr.localSet 49,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 30,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 4] ++ body74Tail80)

@[cbv_eval] theorem sequence74_tail72 :
    instructionSequenceAt 5104 false { bytes := artifactBytes, pos := 10145, limit := 15177 } =
      .ok ((body74Tail72, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 48,
 Wasm.Binary.Instr.localGet 29,
 Wasm.Binary.Instr.localSet 49,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 30,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 31,
 Wasm.Binary.Instr.localGet 4] ++ body74Tail80), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail64 : List Instr := ([Wasm.Binary.Instr.localSet 28,
 Wasm.Binary.Instr.localSet 27,
 Wasm.Binary.Instr.localSet 26,
 Wasm.Binary.Instr.localGet 26,
 Wasm.Binary.Instr.localSet 46,
 Wasm.Binary.Instr.localGet 27,
 Wasm.Binary.Instr.localSet 47,
 Wasm.Binary.Instr.localGet 28] ++ body74Tail72)

@[cbv_eval] theorem sequence74_tail64 :
    instructionSequenceAt 5112 false { bytes := artifactBytes, pos := 10129, limit := 15177 } =
      .ok ((body74Tail64, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 28,
 Wasm.Binary.Instr.localSet 27,
 Wasm.Binary.Instr.localSet 26,
 Wasm.Binary.Instr.localGet 26,
 Wasm.Binary.Instr.localSet 46,
 Wasm.Binary.Instr.localGet 27,
 Wasm.Binary.Instr.localSet 47,
 Wasm.Binary.Instr.localGet 28] ++ body74Tail72), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail56 : List Instr := ([Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 25,
 Wasm.Binary.Instr.localGet 22,
 Wasm.Binary.Instr.localGet 23,
 Wasm.Binary.Instr.localGet 24,
 Wasm.Binary.Instr.localGet 25,
 Wasm.Binary.Instr.call 8,
 Wasm.Binary.Instr.localSet 29] ++ body74Tail64)

@[cbv_eval] theorem sequence74_tail56 :
    instructionSequenceAt 5120 false { bytes := artifactBytes, pos := 10113, limit := 15177 } =
      .ok ((body74Tail56, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 2,
 Wasm.Binary.Instr.localSet 25,
 Wasm.Binary.Instr.localGet 22,
 Wasm.Binary.Instr.localGet 23,
 Wasm.Binary.Instr.localGet 24,
 Wasm.Binary.Instr.localGet 25,
 Wasm.Binary.Instr.call 8,
 Wasm.Binary.Instr.localSet 29] ++ body74Tail64), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail48 : List Instr := ([Wasm.Binary.Instr.localGet 21,
 Wasm.Binary.Instr.localSet 45,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 22,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 23,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 24] ++ body74Tail56)

@[cbv_eval] theorem sequence74_tail48 :
    instructionSequenceAt 5128 false { bytes := artifactBytes, pos := 10097, limit := 15177 } =
      .ok ((body74Tail48, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 21,
 Wasm.Binary.Instr.localSet 45,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 22,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 23,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 24] ++ body74Tail56), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail40 : List Instr := ([Wasm.Binary.Instr.localSet 19,
 Wasm.Binary.Instr.localSet 18,
 Wasm.Binary.Instr.localGet 18,
 Wasm.Binary.Instr.localSet 42,
 Wasm.Binary.Instr.localGet 19,
 Wasm.Binary.Instr.localSet 43,
 Wasm.Binary.Instr.localGet 20,
 Wasm.Binary.Instr.localSet 44] ++ body74Tail48)

@[cbv_eval] theorem sequence74_tail40 :
    instructionSequenceAt 5136 false { bytes := artifactBytes, pos := 10081, limit := 15177 } =
      .ok ((body74Tail40, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 19,
 Wasm.Binary.Instr.localSet 18,
 Wasm.Binary.Instr.localGet 18,
 Wasm.Binary.Instr.localSet 42,
 Wasm.Binary.Instr.localGet 19,
 Wasm.Binary.Instr.localSet 43,
 Wasm.Binary.Instr.localGet 20,
 Wasm.Binary.Instr.localSet 44] ++ body74Tail48), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail32 : List Instr := ([Wasm.Binary.Instr.localSet 17,
 Wasm.Binary.Instr.localGet 14,
 Wasm.Binary.Instr.localGet 15,
 Wasm.Binary.Instr.localGet 16,
 Wasm.Binary.Instr.localGet 17,
 Wasm.Binary.Instr.call 8,
 Wasm.Binary.Instr.localSet 21,
 Wasm.Binary.Instr.localSet 20] ++ body74Tail40)

@[cbv_eval] theorem sequence74_tail32 :
    instructionSequenceAt 5144 false { bytes := artifactBytes, pos := 10065, limit := 15177 } =
      .ok ((body74Tail32, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 17,
 Wasm.Binary.Instr.localGet 14,
 Wasm.Binary.Instr.localGet 15,
 Wasm.Binary.Instr.localGet 16,
 Wasm.Binary.Instr.localGet 17,
 Wasm.Binary.Instr.call 8,
 Wasm.Binary.Instr.localSet 21,
 Wasm.Binary.Instr.localSet 20] ++ body74Tail40), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
