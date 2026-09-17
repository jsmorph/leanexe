import Project.TinyGpt2Hidden.ArtifactBody74Part15

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail24 : List Instr := ([Wasm.Binary.Instr.localSet 41,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 14,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 15,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 16,
 Wasm.Binary.Instr.i64Const 1] ++ body74Tail32)

@[cbv_eval] theorem sequence74_tail24 :
    instructionSequenceAt 5152 false { bytes := artifactBytes, pos := 10049, limit := 15177 } =
      .ok ((body74Tail24, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 41,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 14,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 15,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 16,
 Wasm.Binary.Instr.i64Const 1] ++ body74Tail32), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail16 : List Instr := ([Wasm.Binary.Instr.localSet 10,
 Wasm.Binary.Instr.localGet 10,
 Wasm.Binary.Instr.localSet 38,
 Wasm.Binary.Instr.localGet 11,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 12,
 Wasm.Binary.Instr.localSet 40,
 Wasm.Binary.Instr.localGet 13] ++ body74Tail24)

@[cbv_eval] theorem sequence74_tail16 :
    instructionSequenceAt 5160 false { bytes := artifactBytes, pos := 10033, limit := 15177 } =
      .ok ((body74Tail16, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 10,
 Wasm.Binary.Instr.localGet 10,
 Wasm.Binary.Instr.localSet 38,
 Wasm.Binary.Instr.localGet 11,
 Wasm.Binary.Instr.localSet 39,
 Wasm.Binary.Instr.localGet 12,
 Wasm.Binary.Instr.localSet 40,
 Wasm.Binary.Instr.localGet 13] ++ body74Tail24), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail8 : List Instr := ([Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.call 8,
 Wasm.Binary.Instr.localSet 13,
 Wasm.Binary.Instr.localSet 12,
 Wasm.Binary.Instr.localSet 11] ++ body74Tail16)

@[cbv_eval] theorem sequence74_tail8 :
    instructionSequenceAt 5168 false { bytes := artifactBytes, pos := 10017, limit := 15177 } =
      .ok ((body74Tail8, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.call 8,
 Wasm.Binary.Instr.localSet 13,
 Wasm.Binary.Instr.localSet 12,
 Wasm.Binary.Instr.localSet 11] ++ body74Tail16), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail0 : List Instr := ([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 7,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 8,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 9] ++ body74Tail8)

@[cbv_eval] theorem sequence74_tail0 :
    instructionSequenceAt 5176 false { bytes := artifactBytes, pos := 10001, limit := 15177 } =
      .ok ((body74Tail0, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 6,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 7,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 8,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 9] ++ body74Tail8), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
