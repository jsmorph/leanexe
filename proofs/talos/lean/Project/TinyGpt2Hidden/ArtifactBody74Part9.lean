import Project.TinyGpt2Hidden.ArtifactBody74Part8

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail920 : List Instr := ([Wasm.Binary.Instr.localGet 392,
 Wasm.Binary.Instr.localGet 393,
 Wasm.Binary.Instr.localGet 394,
 Wasm.Binary.Instr.localGet 395,
 Wasm.Binary.Instr.localGet 396,
 Wasm.Binary.Instr.localGet 397,
 Wasm.Binary.Instr.localGet 398,
 Wasm.Binary.Instr.localGet 399] ++ body74Tail928)

@[cbv_eval] theorem sequence74_tail920 :
    instructionSequenceAt 4256 false { bytes := artifactBytes, pos := 12349, limit := 15177 } =
      .ok ((body74Tail920, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 392,
 Wasm.Binary.Instr.localGet 393,
 Wasm.Binary.Instr.localGet 394,
 Wasm.Binary.Instr.localGet 395,
 Wasm.Binary.Instr.localGet 396,
 Wasm.Binary.Instr.localGet 397,
 Wasm.Binary.Instr.localGet 398,
 Wasm.Binary.Instr.localGet 399] ++ body74Tail928), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail912 : List Instr := ([Wasm.Binary.Instr.localGet 53,
 Wasm.Binary.Instr.localSet 403,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 404,
 Wasm.Binary.Instr.localGet 388,
 Wasm.Binary.Instr.localGet 389,
 Wasm.Binary.Instr.localGet 390,
 Wasm.Binary.Instr.localGet 391] ++ body74Tail920)

@[cbv_eval] theorem sequence74_tail912 :
    instructionSequenceAt 4264 false { bytes := artifactBytes, pos := 12327, limit := 15177 } =
      .ok ((body74Tail912, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 53,
 Wasm.Binary.Instr.localSet 403,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 404,
 Wasm.Binary.Instr.localGet 388,
 Wasm.Binary.Instr.localGet 389,
 Wasm.Binary.Instr.localGet 390,
 Wasm.Binary.Instr.localGet 391] ++ body74Tail920), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail904 : List Instr := ([Wasm.Binary.Instr.localGet 49,
 Wasm.Binary.Instr.localSet 399,
 Wasm.Binary.Instr.localGet 50,
 Wasm.Binary.Instr.localSet 400,
 Wasm.Binary.Instr.localGet 51,
 Wasm.Binary.Instr.localSet 401,
 Wasm.Binary.Instr.localGet 52,
 Wasm.Binary.Instr.localSet 402] ++ body74Tail912)

@[cbv_eval] theorem sequence74_tail904 :
    instructionSequenceAt 4272 false { bytes := artifactBytes, pos := 12307, limit := 15177 } =
      .ok ((body74Tail904, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 49,
 Wasm.Binary.Instr.localSet 399,
 Wasm.Binary.Instr.localGet 50,
 Wasm.Binary.Instr.localSet 400,
 Wasm.Binary.Instr.localGet 51,
 Wasm.Binary.Instr.localSet 401,
 Wasm.Binary.Instr.localGet 52,
 Wasm.Binary.Instr.localSet 402] ++ body74Tail912), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail896 : List Instr := ([Wasm.Binary.Instr.localGet 45,
 Wasm.Binary.Instr.localSet 395,
 Wasm.Binary.Instr.localGet 46,
 Wasm.Binary.Instr.localSet 396,
 Wasm.Binary.Instr.localGet 47,
 Wasm.Binary.Instr.localSet 397,
 Wasm.Binary.Instr.localGet 48,
 Wasm.Binary.Instr.localSet 398] ++ body74Tail904)

@[cbv_eval] theorem sequence74_tail896 :
    instructionSequenceAt 4280 false { bytes := artifactBytes, pos := 12287, limit := 15177 } =
      .ok ((body74Tail896, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 45,
 Wasm.Binary.Instr.localSet 395,
 Wasm.Binary.Instr.localGet 46,
 Wasm.Binary.Instr.localSet 396,
 Wasm.Binary.Instr.localGet 47,
 Wasm.Binary.Instr.localSet 397,
 Wasm.Binary.Instr.localGet 48,
 Wasm.Binary.Instr.localSet 398] ++ body74Tail904), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail888 : List Instr := ([Wasm.Binary.Instr.localGet 41,
 Wasm.Binary.Instr.localSet 391,
 Wasm.Binary.Instr.localGet 42,
 Wasm.Binary.Instr.localSet 392,
 Wasm.Binary.Instr.localGet 43,
 Wasm.Binary.Instr.localSet 393,
 Wasm.Binary.Instr.localGet 44,
 Wasm.Binary.Instr.localSet 394] ++ body74Tail896)

@[cbv_eval] theorem sequence74_tail888 :
    instructionSequenceAt 4288 false { bytes := artifactBytes, pos := 12267, limit := 15177 } =
      .ok ((body74Tail888, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 41,
 Wasm.Binary.Instr.localSet 391,
 Wasm.Binary.Instr.localGet 42,
 Wasm.Binary.Instr.localSet 392,
 Wasm.Binary.Instr.localGet 43,
 Wasm.Binary.Instr.localSet 393,
 Wasm.Binary.Instr.localGet 44,
 Wasm.Binary.Instr.localSet 394] ++ body74Tail896), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail880 : List Instr := ([Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 387,
 Wasm.Binary.Instr.localGet 38,
 Wasm.Binary.Instr.localSet 388,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.localSet 389,
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.localSet 390] ++ body74Tail888)

@[cbv_eval] theorem sequence74_tail880 :
    instructionSequenceAt 4296 false { bytes := artifactBytes, pos := 12248, limit := 15177 } =
      .ok ((body74Tail880, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 387,
 Wasm.Binary.Instr.localGet 38,
 Wasm.Binary.Instr.localSet 388,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.localSet 389,
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.localSet 390] ++ body74Tail888), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail872 : List Instr := ([Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 383,
 Wasm.Binary.Instr.localSet 382,
 Wasm.Binary.Instr.localSet 381,
 Wasm.Binary.Instr.localSet 380,
 Wasm.Binary.Instr.localGet 383,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add] ++ body74Tail880)

@[cbv_eval] theorem sequence74_tail872 :
    instructionSequenceAt 4304 false { bytes := artifactBytes, pos := 12229, limit := 15177 } =
      .ok ((body74Tail872, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 383,
 Wasm.Binary.Instr.localSet 382,
 Wasm.Binary.Instr.localSet 381,
 Wasm.Binary.Instr.localSet 380,
 Wasm.Binary.Instr.localGet 383,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add] ++ body74Tail880), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail864 : List Instr := ([Wasm.Binary.Instr.localSet 377,
 Wasm.Binary.Instr.call 54,
 Wasm.Binary.Instr.localSet 378,
 Wasm.Binary.Instr.localGet 378,
 Wasm.Binary.Instr.localSet 379,
 Wasm.Binary.Instr.localGet 376,
 Wasm.Binary.Instr.localGet 377,
 Wasm.Binary.Instr.localGet 379] ++ body74Tail872)

@[cbv_eval] theorem sequence74_tail864 :
    instructionSequenceAt 4312 false { bytes := artifactBytes, pos := 12206, limit := 15177 } =
      .ok ((body74Tail864, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 377,
 Wasm.Binary.Instr.call 54,
 Wasm.Binary.Instr.localSet 378,
 Wasm.Binary.Instr.localGet 378,
 Wasm.Binary.Instr.localSet 379,
 Wasm.Binary.Instr.localGet 376,
 Wasm.Binary.Instr.localGet 377,
 Wasm.Binary.Instr.localGet 379] ++ body74Tail872), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail856 : List Instr := ([Wasm.Binary.Instr.localSet 374,
 Wasm.Binary.Instr.localSet 373,
 Wasm.Binary.Instr.localSet 372,
 Wasm.Binary.Instr.localGet 375,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 376,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail864)

@[cbv_eval] theorem sequence74_tail856 :
    instructionSequenceAt 4320 false { bytes := artifactBytes, pos := 12186, limit := 15177 } =
      .ok ((body74Tail856, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 374,
 Wasm.Binary.Instr.localSet 373,
 Wasm.Binary.Instr.localSet 372,
 Wasm.Binary.Instr.localGet 375,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 376,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail864), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail848 : List Instr := ([Wasm.Binary.Instr.localGet 365,
 Wasm.Binary.Instr.localGet 367,
 Wasm.Binary.Instr.localGet 368,
 Wasm.Binary.Instr.localGet 369,
 Wasm.Binary.Instr.localGet 370,
 Wasm.Binary.Instr.localGet 371,
 Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 375] ++ body74Tail856)

@[cbv_eval] theorem sequence74_tail848 :
    instructionSequenceAt 4328 false { bytes := artifactBytes, pos := 12163, limit := 15177 } =
      .ok ((body74Tail848, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 365,
 Wasm.Binary.Instr.localGet 367,
 Wasm.Binary.Instr.localGet 368,
 Wasm.Binary.Instr.localGet 369,
 Wasm.Binary.Instr.localGet 370,
 Wasm.Binary.Instr.localGet 371,
 Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 375] ++ body74Tail856), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail840 : List Instr := ([Wasm.Binary.Instr.localSet 368,
 Wasm.Binary.Instr.localGet 301,
 Wasm.Binary.Instr.localSet 369,
 Wasm.Binary.Instr.localGet 302,
 Wasm.Binary.Instr.localSet 370,
 Wasm.Binary.Instr.localGet 303,
 Wasm.Binary.Instr.localSet 371,
 Wasm.Binary.Instr.localGet 364] ++ body74Tail848)

@[cbv_eval] theorem sequence74_tail840 :
    instructionSequenceAt 4336 false { bytes := artifactBytes, pos := 12139, limit := 15177 } =
      .ok ((body74Tail840, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 368,
 Wasm.Binary.Instr.localGet 301,
 Wasm.Binary.Instr.localSet 369,
 Wasm.Binary.Instr.localGet 302,
 Wasm.Binary.Instr.localSet 370,
 Wasm.Binary.Instr.localGet 303,
 Wasm.Binary.Instr.localSet 371,
 Wasm.Binary.Instr.localGet 364] ++ body74Tail848), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail832 : List Instr := ([Wasm.Binary.Instr.localSet 364,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 365,
 Wasm.Binary.Instr.call 53,
 Wasm.Binary.Instr.localSet 366,
 Wasm.Binary.Instr.localGet 366,
 Wasm.Binary.Instr.localSet 367,
 Wasm.Binary.Instr.localGet 300] ++ body74Tail840)

@[cbv_eval] theorem sequence74_tail832 :
    instructionSequenceAt 4344 false { bytes := artifactBytes, pos := 12117, limit := 15177 } =
      .ok ((body74Tail832, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 364,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 365,
 Wasm.Binary.Instr.call 53,
 Wasm.Binary.Instr.localSet 366,
 Wasm.Binary.Instr.localGet 366,
 Wasm.Binary.Instr.localSet 367,
 Wasm.Binary.Instr.localGet 300] ++ body74Tail840), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail824 : List Instr := ([Wasm.Binary.Instr.localSet 361,
 Wasm.Binary.Instr.localSet 360,
 Wasm.Binary.Instr.localGet 362,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 386,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail832)

@[cbv_eval] theorem sequence74_tail824 :
    instructionSequenceAt 4352 false { bytes := artifactBytes, pos := 12100, limit := 15177 } =
      .ok ((body74Tail824, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 361,
 Wasm.Binary.Instr.localSet 360,
 Wasm.Binary.Instr.localGet 362,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 386,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail832), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail816 : List Instr := ([Wasm.Binary.Instr.localGet 358,
 Wasm.Binary.Instr.localSet 359,
 Wasm.Binary.Instr.localGet 356,
 Wasm.Binary.Instr.localGet 357,
 Wasm.Binary.Instr.localGet 359,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 363,
 Wasm.Binary.Instr.localSet 362] ++ body74Tail824)

@[cbv_eval] theorem sequence74_tail816 :
    instructionSequenceAt 4360 false { bytes := artifactBytes, pos := 12077, limit := 15177 } =
      .ok ((body74Tail816, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 358,
 Wasm.Binary.Instr.localSet 359,
 Wasm.Binary.Instr.localGet 356,
 Wasm.Binary.Instr.localGet 357,
 Wasm.Binary.Instr.localGet 359,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 363,
 Wasm.Binary.Instr.localSet 362] ++ body74Tail824), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail808 : List Instr := ([Wasm.Binary.Instr.localGet 354,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 356,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 357,
 Wasm.Binary.Instr.call 54,
 Wasm.Binary.Instr.localSet 358] ++ body74Tail816)

@[cbv_eval] theorem sequence74_tail808 :
    instructionSequenceAt 4368 false { bytes := artifactBytes, pos := 12058, limit := 15177 } =
      .ok ((body74Tail808, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 354,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 356,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 357,
 Wasm.Binary.Instr.call 54,
 Wasm.Binary.Instr.localSet 358] ++ body74Tail816), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail800 : List Instr := ([Wasm.Binary.Instr.localGet 349,
 Wasm.Binary.Instr.localGet 350,
 Wasm.Binary.Instr.localGet 351,
 Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 355,
 Wasm.Binary.Instr.localSet 354,
 Wasm.Binary.Instr.localSet 353,
 Wasm.Binary.Instr.localSet 352] ++ body74Tail808)

@[cbv_eval] theorem sequence74_tail800 :
    instructionSequenceAt 4376 false { bytes := artifactBytes, pos := 12035, limit := 15177 } =
      .ok ((body74Tail800, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 349,
 Wasm.Binary.Instr.localGet 350,
 Wasm.Binary.Instr.localGet 351,
 Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 355,
 Wasm.Binary.Instr.localSet 354,
 Wasm.Binary.Instr.localSet 353,
 Wasm.Binary.Instr.localSet 352] ++ body74Tail808), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
