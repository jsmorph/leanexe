import Project.Artifact.Binary.InstructionEvaluate
import Project.Artifact.Binary.Equality
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body72Tail268 : List Instr := []

@[cbv_eval] theorem sequence72_tail268 :
    instructionSequenceAt 360 false { bytes := artifactBytes, pos := 9982, limit := 9983 } =
      .ok ((body72Tail268, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok (([], .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail264 : List Instr := ([Wasm.Binary.Instr.localGet 282,
 Wasm.Binary.Instr.localGet 283,
 Wasm.Binary.Instr.localGet 284,
 Wasm.Binary.Instr.localGet 285] ++ body72Tail268)

@[cbv_eval] theorem sequence72_tail264 :
    instructionSequenceAt 364 false { bytes := artifactBytes, pos := 9970, limit := 9983 } =
      .ok ((body72Tail264, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 282,
 Wasm.Binary.Instr.localGet 283,
 Wasm.Binary.Instr.localGet 284,
 Wasm.Binary.Instr.localGet 285] ++ body72Tail268), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail256 : List Instr := ([Wasm.Binary.Instr.localSet 280,
 Wasm.Binary.Instr.localSet 279,
 Wasm.Binary.Instr.localSet 278,
 Wasm.Binary.Instr.localGet 281,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 285] ++ body72Tail264)

@[cbv_eval] theorem sequence72_tail256 :
    instructionSequenceAt 372 false { bytes := artifactBytes, pos := 9952, limit := 9983 } =
      .ok ((body72Tail256, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 280,
 Wasm.Binary.Instr.localSet 279,
 Wasm.Binary.Instr.localSet 278,
 Wasm.Binary.Instr.localGet 281,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 285] ++ body72Tail264), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail248 : List Instr := ([Wasm.Binary.Instr.localSet 276,
 Wasm.Binary.Instr.localGet 276,
 Wasm.Binary.Instr.localSet 277,
 Wasm.Binary.Instr.localGet 274,
 Wasm.Binary.Instr.localGet 275,
 Wasm.Binary.Instr.localGet 277,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 281] ++ body72Tail256)

@[cbv_eval] theorem sequence72_tail248 :
    instructionSequenceAt 380 false { bytes := artifactBytes, pos := 9929, limit := 9983 } =
      .ok ((body72Tail248, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 276,
 Wasm.Binary.Instr.localGet 276,
 Wasm.Binary.Instr.localSet 277,
 Wasm.Binary.Instr.localGet 274,
 Wasm.Binary.Instr.localGet 275,
 Wasm.Binary.Instr.localGet 277,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 281] ++ body72Tail256), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail240 : List Instr := ([Wasm.Binary.Instr.localSet 273,
 Wasm.Binary.Instr.localGet 273,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 274,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 275,
 Wasm.Binary.Instr.call 71] ++ body72Tail248)

@[cbv_eval] theorem sequence72_tail240 :
    instructionSequenceAt 388 false { bytes := artifactBytes, pos := 9910, limit := 9983 } =
      .ok ((body72Tail240, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 273,
 Wasm.Binary.Instr.localGet 273,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 274,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 275,
 Wasm.Binary.Instr.call 71] ++ body72Tail248), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail232 : List Instr := ([Wasm.Binary.Instr.localGet 266,
 Wasm.Binary.Instr.localGet 267,
 Wasm.Binary.Instr.localGet 268,
 Wasm.Binary.Instr.localGet 269,
 Wasm.Binary.Instr.localGet 270,
 Wasm.Binary.Instr.localGet 271,
 Wasm.Binary.Instr.localGet 272,
 Wasm.Binary.Instr.call 69] ++ body72Tail240)

@[cbv_eval] theorem sequence72_tail232 :
    instructionSequenceAt 396 false { bytes := artifactBytes, pos := 9887, limit := 9983 } =
      .ok ((body72Tail232, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 266,
 Wasm.Binary.Instr.localGet 267,
 Wasm.Binary.Instr.localGet 268,
 Wasm.Binary.Instr.localGet 269,
 Wasm.Binary.Instr.localGet 270,
 Wasm.Binary.Instr.localGet 271,
 Wasm.Binary.Instr.localGet 272,
 Wasm.Binary.Instr.call 69] ++ body72Tail240), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail224 : List Instr := ([Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 272,
 Wasm.Binary.Instr.localGet 259,
 Wasm.Binary.Instr.localGet 260,
 Wasm.Binary.Instr.localGet 262,
 Wasm.Binary.Instr.localGet 263,
 Wasm.Binary.Instr.localGet 264,
 Wasm.Binary.Instr.localGet 265] ++ body72Tail232)

@[cbv_eval] theorem sequence72_tail224 :
    instructionSequenceAt 404 false { bytes := artifactBytes, pos := 9864, limit := 9983 } =
      .ok ((body72Tail224, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 272,
 Wasm.Binary.Instr.localGet 259,
 Wasm.Binary.Instr.localGet 260,
 Wasm.Binary.Instr.localGet 262,
 Wasm.Binary.Instr.localGet 263,
 Wasm.Binary.Instr.localGet 264,
 Wasm.Binary.Instr.localGet 265] ++ body72Tail232), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail216 : List Instr := ([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 268,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 269,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 270,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 271] ++ body72Tail224)

@[cbv_eval] theorem sequence72_tail216 :
    instructionSequenceAt 412 false { bytes := artifactBytes, pos := 9844, limit := 9983 } =
      .ok ((body72Tail216, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 268,
 Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 269,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 270,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 271] ++ body72Tail224), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail208 : List Instr := ([Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 264,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 265,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 266,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 267] ++ body72Tail216)

@[cbv_eval] theorem sequence72_tail208 :
    instructionSequenceAt 420 false { bytes := artifactBytes, pos := 9824, limit := 9983 } =
      .ok ((body72Tail208, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 3,
 Wasm.Binary.Instr.localSet 264,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 265,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 266,
 Wasm.Binary.Instr.localGet 4,
 Wasm.Binary.Instr.localSet 267] ++ body72Tail216), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail200 : List Instr := ([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 260,
 Wasm.Binary.Instr.call 70,
 Wasm.Binary.Instr.localSet 261,
 Wasm.Binary.Instr.localGet 261,
 Wasm.Binary.Instr.localSet 262,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 263] ++ body72Tail208)

@[cbv_eval] theorem sequence72_tail200 :
    instructionSequenceAt 428 false { bytes := artifactBytes, pos := 9803, limit := 9983 } =
      .ok ((body72Tail200, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 260,
 Wasm.Binary.Instr.call 70,
 Wasm.Binary.Instr.localSet 261,
 Wasm.Binary.Instr.localGet 261,
 Wasm.Binary.Instr.localSet 262,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 263] ++ body72Tail208), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail192 : List Instr := ([Wasm.Binary.Instr.localSet 210,
 Wasm.Binary.Instr.localGet 212,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 284,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 259] ++ body72Tail200)

@[cbv_eval] theorem sequence72_tail192 :
    instructionSequenceAt 436 false { bytes := artifactBytes, pos := 9786, limit := 9983 } =
      .ok ((body72Tail192, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 210,
 Wasm.Binary.Instr.localGet 212,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 284,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 259] ++ body72Tail200), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail184 : List Instr := ([Wasm.Binary.Instr.localSet 209,
 Wasm.Binary.Instr.localGet 206,
 Wasm.Binary.Instr.localGet 207,
 Wasm.Binary.Instr.localGet 209,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 213,
 Wasm.Binary.Instr.localSet 212,
 Wasm.Binary.Instr.localSet 211] ++ body72Tail192)

@[cbv_eval] theorem sequence72_tail184 :
    instructionSequenceAt 444 false { bytes := artifactBytes, pos := 9763, limit := 9983 } =
      .ok ((body72Tail184, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 209,
 Wasm.Binary.Instr.localGet 206,
 Wasm.Binary.Instr.localGet 207,
 Wasm.Binary.Instr.localGet 209,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 213,
 Wasm.Binary.Instr.localSet 212,
 Wasm.Binary.Instr.localSet 211] ++ body72Tail192), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail176 : List Instr := ([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 206,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 207,
 Wasm.Binary.Instr.call 71,
 Wasm.Binary.Instr.localSet 208,
 Wasm.Binary.Instr.localGet 208] ++ body72Tail184)

@[cbv_eval] theorem sequence72_tail176 :
    instructionSequenceAt 452 false { bytes := artifactBytes, pos := 9744, limit := 9983 } =
      .ok ((body72Tail176, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 206,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 207,
 Wasm.Binary.Instr.call 71,
 Wasm.Binary.Instr.localSet 208,
 Wasm.Binary.Instr.localGet 208] ++ body72Tail184), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail168 : List Instr := ([Wasm.Binary.Instr.localGet 185,
 Wasm.Binary.Instr.localGet 186,
 Wasm.Binary.Instr.localGet 187,
 Wasm.Binary.Instr.localGet 188,
 Wasm.Binary.Instr.localGet 189,
 Wasm.Binary.Instr.call 69,
 Wasm.Binary.Instr.localSet 190,
 Wasm.Binary.Instr.localGet 190] ++ body72Tail176)

@[cbv_eval] theorem sequence72_tail168 :
    instructionSequenceAt 460 false { bytes := artifactBytes, pos := 9721, limit := 9983 } =
      .ok ((body72Tail168, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 185,
 Wasm.Binary.Instr.localGet 186,
 Wasm.Binary.Instr.localGet 187,
 Wasm.Binary.Instr.localGet 188,
 Wasm.Binary.Instr.localGet 189,
 Wasm.Binary.Instr.call 69,
 Wasm.Binary.Instr.localSet 190,
 Wasm.Binary.Instr.localGet 190] ++ body72Tail176), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail160 : List Instr := ([Wasm.Binary.Instr.localGet 176,
 Wasm.Binary.Instr.localGet 177,
 Wasm.Binary.Instr.localGet 179,
 Wasm.Binary.Instr.localGet 180,
 Wasm.Binary.Instr.localGet 181,
 Wasm.Binary.Instr.localGet 182,
 Wasm.Binary.Instr.localGet 183,
 Wasm.Binary.Instr.localGet 184] ++ body72Tail168)

@[cbv_eval] theorem sequence72_tail160 :
    instructionSequenceAt 468 false { bytes := artifactBytes, pos := 9697, limit := 9983 } =
      .ok ((body72Tail160, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 176,
 Wasm.Binary.Instr.localGet 177,
 Wasm.Binary.Instr.localGet 179,
 Wasm.Binary.Instr.localGet 180,
 Wasm.Binary.Instr.localGet 181,
 Wasm.Binary.Instr.localGet 182,
 Wasm.Binary.Instr.localGet 183,
 Wasm.Binary.Instr.localGet 184] ++ body72Tail168), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body72Tail152 : List Instr := ([Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 186,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 187,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 188,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 189] ++ body72Tail160)

@[cbv_eval] theorem sequence72_tail152 :
    instructionSequenceAt 476 false { bytes := artifactBytes, pos := 9677, limit := 9983 } =
      .ok ((body72Tail152, .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 6,
 Wasm.Binary.Instr.localSet 186,
 Wasm.Binary.Instr.localGet 7,
 Wasm.Binary.Instr.localSet 187,
 Wasm.Binary.Instr.localGet 8,
 Wasm.Binary.Instr.localSet 188,
 Wasm.Binary.Instr.localGet 9,
 Wasm.Binary.Instr.localSet 189] ++ body72Tail160), .end), { bytes := artifactBytes, pos := 9983, limit := 9983 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
