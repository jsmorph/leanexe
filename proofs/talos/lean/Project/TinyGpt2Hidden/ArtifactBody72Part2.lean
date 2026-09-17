import Project.TinyGpt2Hidden.ArtifactBody72Part1

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body72Tail16 : List Instr := ([Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 18,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 19,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 20,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 21] ++ body72Tail24)

@[cbv_eval] theorem sequence72_tail16 :
    instructionSequenceAt 612 false { bytes := artifactBytes, pos := 9387, limit := 9983 } =
      .ok ((body72Tail16, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 18,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 19,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 20,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 21] ++ body72Tail24), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail8 : List Instr := ([Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 14,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 15,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 16,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 17] ++ body72Tail16)

@[cbv_eval] theorem sequence72_tail8 :
    instructionSequenceAt 620 false { bytes := artifactBytes, pos := 9371, limit := 9983 } =
      .ok ((body72Tail8, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 14,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 15,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 16,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 17] ++ body72Tail16), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail0 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 10,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 11,
 Wasm.Binary.Instr.call 70,
 Wasm.Binary.Instr.localSet 12,
 Wasm.Binary.Instr.localGet 12,
 Wasm.Binary.Instr.localSet 13] ++ body72Tail8)

@[cbv_eval] theorem sequence72_tail0 :
    instructionSequenceAt 628 false { bytes := artifactBytes, pos := 9355, limit := 9983 } =
      .ok ((body72Tail0, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 10,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 11,
 Wasm.Binary.Instr.call 70,
 Wasm.Binary.Instr.localSet 12,
 Wasm.Binary.Instr.localGet 12,
 Wasm.Binary.Instr.localSet 13] ++ body72Tail8), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
