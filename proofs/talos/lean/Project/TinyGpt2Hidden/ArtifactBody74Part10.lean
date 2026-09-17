import Project.TinyGpt2Hidden.ArtifactBody74Part9

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail792 : List Instr := ([Wasm.Binary.Instr.localGet 302,
 Wasm.Binary.Instr.localSet 350,
 Wasm.Binary.Instr.localGet 303,
 Wasm.Binary.Instr.localSet 351,
 Wasm.Binary.Instr.localGet 344,
 Wasm.Binary.Instr.localGet 345,
 Wasm.Binary.Instr.localGet 347,
 Wasm.Binary.Instr.localGet 348] ++ body74Tail800)

@[cbv_eval] theorem sequence74_tail792 :
    instructionSequenceAt 4384 false { bytes := artifactBytes, pos := 12011, limit := 15177 } =
      .ok ((body74Tail792, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 302,
 Wasm.Binary.Instr.localSet 350,
 Wasm.Binary.Instr.localGet 303,
 Wasm.Binary.Instr.localSet 351,
 Wasm.Binary.Instr.localGet 344,
 Wasm.Binary.Instr.localGet 345,
 Wasm.Binary.Instr.localGet 347,
 Wasm.Binary.Instr.localGet 348] ++ body74Tail800), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail784 : List Instr := ([Wasm.Binary.Instr.call 53,
 Wasm.Binary.Instr.localSet 346,
 Wasm.Binary.Instr.localGet 346,
 Wasm.Binary.Instr.localSet 347,
 Wasm.Binary.Instr.localGet 300,
 Wasm.Binary.Instr.localSet 348,
 Wasm.Binary.Instr.localGet 301,
 Wasm.Binary.Instr.localSet 349] ++ body74Tail792)

@[cbv_eval] theorem sequence74_tail784 :
    instructionSequenceAt 4392 false { bytes := artifactBytes, pos := 11988, limit := 15177 } =
      .ok ((body74Tail784, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 53,
 Wasm.Binary.Instr.localSet 346,
 Wasm.Binary.Instr.localGet 346,
 Wasm.Binary.Instr.localSet 347,
 Wasm.Binary.Instr.localGet 300,
 Wasm.Binary.Instr.localSet 348,
 Wasm.Binary.Instr.localGet 301,
 Wasm.Binary.Instr.localSet 349] ++ body74Tail792), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail776 : List Instr := ([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 385,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 344,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 345] ++ body74Tail784)

@[cbv_eval] theorem sequence74_tail776 :
    instructionSequenceAt 4400 false { bytes := artifactBytes, pos := 11972, limit := 15177 } =
      .ok ((body74Tail776, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 385,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 344,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 345] ++ body74Tail784), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail768 : List Instr := ([Wasm.Binary.Instr.localGet 337,
 Wasm.Binary.Instr.localGet 339,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 343,
 Wasm.Binary.Instr.localSet 342,
 Wasm.Binary.Instr.localSet 341,
 Wasm.Binary.Instr.localSet 340,
 Wasm.Binary.Instr.localGet 341] ++ body74Tail776)

@[cbv_eval] theorem sequence74_tail768 :
    instructionSequenceAt 4408 false { bytes := artifactBytes, pos := 11949, limit := 15177 } =
      .ok ((body74Tail768, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 337,
 Wasm.Binary.Instr.localGet 339,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 343,
 Wasm.Binary.Instr.localSet 342,
 Wasm.Binary.Instr.localSet 341,
 Wasm.Binary.Instr.localSet 340,
 Wasm.Binary.Instr.localGet 341] ++ body74Tail776), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail760 : List Instr := ([Wasm.Binary.Instr.localSet 336,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 337,
 Wasm.Binary.Instr.call 54,
 Wasm.Binary.Instr.localSet 338,
 Wasm.Binary.Instr.localGet 338,
 Wasm.Binary.Instr.localSet 339,
 Wasm.Binary.Instr.localGet 336] ++ body74Tail768)

@[cbv_eval] theorem sequence74_tail760 :
    instructionSequenceAt 4416 false { bytes := artifactBytes, pos := 11927, limit := 15177 } =
      .ok ((body74Tail760, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 336,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 337,
 Wasm.Binary.Instr.call 54,
 Wasm.Binary.Instr.localSet 338,
 Wasm.Binary.Instr.localGet 338,
 Wasm.Binary.Instr.localSet 339,
 Wasm.Binary.Instr.localGet 336] ++ body74Tail768), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail752 : List Instr := ([Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 335,
 Wasm.Binary.Instr.localSet 334,
 Wasm.Binary.Instr.localSet 333,
 Wasm.Binary.Instr.localSet 332,
 Wasm.Binary.Instr.localGet 333,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail760)

@[cbv_eval] theorem sequence74_tail752 :
    instructionSequenceAt 4424 false { bytes := artifactBytes, pos := 11907, limit := 15177 } =
      .ok ((body74Tail752, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 335,
 Wasm.Binary.Instr.localSet 334,
 Wasm.Binary.Instr.localSet 333,
 Wasm.Binary.Instr.localSet 332,
 Wasm.Binary.Instr.localGet 333,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail760), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail744 : List Instr := ([Wasm.Binary.Instr.localSet 331,
 Wasm.Binary.Instr.localGet 324,
 Wasm.Binary.Instr.localGet 325,
 Wasm.Binary.Instr.localGet 327,
 Wasm.Binary.Instr.localGet 328,
 Wasm.Binary.Instr.localGet 329,
 Wasm.Binary.Instr.localGet 330,
 Wasm.Binary.Instr.localGet 331] ++ body74Tail752)

@[cbv_eval] theorem sequence74_tail744 :
    instructionSequenceAt 4432 false { bytes := artifactBytes, pos := 11883, limit := 15177 } =
      .ok ((body74Tail744, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 331,
 Wasm.Binary.Instr.localGet 324,
 Wasm.Binary.Instr.localGet 325,
 Wasm.Binary.Instr.localGet 327,
 Wasm.Binary.Instr.localGet 328,
 Wasm.Binary.Instr.localGet 329,
 Wasm.Binary.Instr.localGet 330,
 Wasm.Binary.Instr.localGet 331] ++ body74Tail752), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail736 : List Instr := ([Wasm.Binary.Instr.localSet 327,
 Wasm.Binary.Instr.localGet 300,
 Wasm.Binary.Instr.localSet 328,
 Wasm.Binary.Instr.localGet 301,
 Wasm.Binary.Instr.localSet 329,
 Wasm.Binary.Instr.localGet 302,
 Wasm.Binary.Instr.localSet 330,
 Wasm.Binary.Instr.localGet 303] ++ body74Tail744)

@[cbv_eval] theorem sequence74_tail736 :
    instructionSequenceAt 4440 false { bytes := artifactBytes, pos := 11859, limit := 15177 } =
      .ok ((body74Tail736, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 327,
 Wasm.Binary.Instr.localGet 300,
 Wasm.Binary.Instr.localSet 328,
 Wasm.Binary.Instr.localGet 301,
 Wasm.Binary.Instr.localSet 329,
 Wasm.Binary.Instr.localGet 302,
 Wasm.Binary.Instr.localSet 330,
 Wasm.Binary.Instr.localGet 303] ++ body74Tail744), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail728 : List Instr := ([Wasm.Binary.Instr.localSet 384,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 324,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 325,
 Wasm.Binary.Instr.call 53,
 Wasm.Binary.Instr.localSet 326,
 Wasm.Binary.Instr.localGet 326] ++ body74Tail736)

@[cbv_eval] theorem sequence74_tail728 :
    instructionSequenceAt 4448 false { bytes := artifactBytes, pos := 11838, limit := 15177 } =
      .ok ((body74Tail728, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 384,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 324,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 325,
 Wasm.Binary.Instr.call 53,
 Wasm.Binary.Instr.localSet 326,
 Wasm.Binary.Instr.localGet 326] ++ body74Tail736), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail720 : List Instr := ([Wasm.Binary.Instr.localSet 323,
 Wasm.Binary.Instr.localSet 322,
 Wasm.Binary.Instr.localSet 321,
 Wasm.Binary.Instr.localSet 320,
 Wasm.Binary.Instr.localGet 320,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64] ++ body74Tail728)

@[cbv_eval] theorem sequence74_tail720 :
    instructionSequenceAt 4456 false { bytes := artifactBytes, pos := 11820, limit := 15177 } =
      .ok ((body74Tail720, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 323,
 Wasm.Binary.Instr.localSet 322,
 Wasm.Binary.Instr.localSet 321,
 Wasm.Binary.Instr.localSet 320,
 Wasm.Binary.Instr.localGet 320,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64] ++ body74Tail728), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail712 : List Instr := ([Wasm.Binary.Instr.call 54,
 Wasm.Binary.Instr.localSet 318,
 Wasm.Binary.Instr.localGet 318,
 Wasm.Binary.Instr.localSet 319,
 Wasm.Binary.Instr.localGet 316,
 Wasm.Binary.Instr.localGet 317,
 Wasm.Binary.Instr.localGet 319,
 Wasm.Binary.Instr.call 5] ++ body74Tail720)

@[cbv_eval] theorem sequence74_tail712 :
    instructionSequenceAt 4464 false { bytes := artifactBytes, pos := 11798, limit := 15177 } =
      .ok ((body74Tail712, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 54,
 Wasm.Binary.Instr.localSet 318,
 Wasm.Binary.Instr.localGet 318,
 Wasm.Binary.Instr.localSet 319,
 Wasm.Binary.Instr.localGet 316,
 Wasm.Binary.Instr.localGet 317,
 Wasm.Binary.Instr.localGet 319,
 Wasm.Binary.Instr.call 5] ++ body74Tail720), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail704 : List Instr := ([Wasm.Binary.Instr.localSet 313,
 Wasm.Binary.Instr.localSet 312,
 Wasm.Binary.Instr.localGet 312,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 316,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 317] ++ body74Tail712)

@[cbv_eval] theorem sequence74_tail704 :
    instructionSequenceAt 4472 false { bytes := artifactBytes, pos := 11778, limit := 15177 } =
      .ok ((body74Tail704, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 313,
 Wasm.Binary.Instr.localSet 312,
 Wasm.Binary.Instr.localGet 312,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 316,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 317] ++ body74Tail712), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail696 : List Instr := ([Wasm.Binary.Instr.localGet 307,
 Wasm.Binary.Instr.localGet 308,
 Wasm.Binary.Instr.localGet 309,
 Wasm.Binary.Instr.localGet 310,
 Wasm.Binary.Instr.localGet 311,
 Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 315,
 Wasm.Binary.Instr.localSet 314] ++ body74Tail704)

@[cbv_eval] theorem sequence74_tail696 :
    instructionSequenceAt 4480 false { bytes := artifactBytes, pos := 11755, limit := 15177 } =
      .ok ((body74Tail696, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 307,
 Wasm.Binary.Instr.localGet 308,
 Wasm.Binary.Instr.localGet 309,
 Wasm.Binary.Instr.localGet 310,
 Wasm.Binary.Instr.localGet 311,
 Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 315,
 Wasm.Binary.Instr.localSet 314] ++ body74Tail704), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail688 : List Instr := ([Wasm.Binary.Instr.localGet 301,
 Wasm.Binary.Instr.localSet 309,
 Wasm.Binary.Instr.localGet 302,
 Wasm.Binary.Instr.localSet 310,
 Wasm.Binary.Instr.localGet 303,
 Wasm.Binary.Instr.localSet 311,
 Wasm.Binary.Instr.localGet 304,
 Wasm.Binary.Instr.localGet 305] ++ body74Tail696)

@[cbv_eval] theorem sequence74_tail688 :
    instructionSequenceAt 4488 false { bytes := artifactBytes, pos := 11731, limit := 15177 } =
      .ok ((body74Tail688, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 301,
 Wasm.Binary.Instr.localSet 309,
 Wasm.Binary.Instr.localGet 302,
 Wasm.Binary.Instr.localSet 310,
 Wasm.Binary.Instr.localGet 303,
 Wasm.Binary.Instr.localSet 311,
 Wasm.Binary.Instr.localGet 304,
 Wasm.Binary.Instr.localGet 305] ++ body74Tail696), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail680 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 305,
 Wasm.Binary.Instr.call 53,
 Wasm.Binary.Instr.localSet 306,
 Wasm.Binary.Instr.localGet 306,
 Wasm.Binary.Instr.localSet 307,
 Wasm.Binary.Instr.localGet 300,
 Wasm.Binary.Instr.localSet 308] ++ body74Tail688)

@[cbv_eval] theorem sequence74_tail680 :
    instructionSequenceAt 4496 false { bytes := artifactBytes, pos := 11709, limit := 15177 } =
      .ok ((body74Tail680, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 305,
 Wasm.Binary.Instr.call 53,
 Wasm.Binary.Instr.localSet 306,
 Wasm.Binary.Instr.localGet 306,
 Wasm.Binary.Instr.localSet 307,
 Wasm.Binary.Instr.localGet 300,
 Wasm.Binary.Instr.localSet 308] ++ body74Tail688), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail672 : List Instr := ([Wasm.Binary.Instr.localGet 297,
 Wasm.Binary.Instr.localSet 301,
 Wasm.Binary.Instr.localGet 298,
 Wasm.Binary.Instr.localSet 302,
 Wasm.Binary.Instr.localGet 299,
 Wasm.Binary.Instr.localSet 303,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 304] ++ body74Tail680)

@[cbv_eval] theorem sequence74_tail672 :
    instructionSequenceAt 4504 false { bytes := artifactBytes, pos := 11686, limit := 15177 } =
      .ok ((body74Tail672, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 297,
 Wasm.Binary.Instr.localSet 301,
 Wasm.Binary.Instr.localGet 298,
 Wasm.Binary.Instr.localSet 302,
 Wasm.Binary.Instr.localGet 299,
 Wasm.Binary.Instr.localSet 303,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 304] ++ body74Tail680), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
