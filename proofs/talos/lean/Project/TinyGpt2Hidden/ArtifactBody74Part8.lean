import Project.TinyGpt2Hidden.ArtifactBody74Part7

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail1048 : List Instr := ([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 454,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 455,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 456,
 Wasm.Binary.Instr.localGet 456,
 Wasm.Binary.Instr.localSet 457] ++ body74Tail1056)

@[cbv_eval] theorem sequence74_tail1048 :
    instructionSequenceAt 4128 false { bytes := artifactBytes, pos := 12716, limit := 15177 } =
      .ok ((body74Tail1048, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 454,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 455,
 Wasm.Binary.Instr.call 58,
 Wasm.Binary.Instr.localSet 456,
 Wasm.Binary.Instr.localGet 456,
 Wasm.Binary.Instr.localSet 457] ++ body74Tail1056), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1040 : List Instr := ([Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 450,
 Wasm.Binary.Instr.localGet 450,
 Wasm.Binary.Instr.localSet 451,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 452,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.localSet 453] ++ body74Tail1048)

@[cbv_eval] theorem sequence74_tail1040 :
    instructionSequenceAt 4136 false { bytes := artifactBytes, pos := 12695, limit := 15177 } =
      .ok ((body74Tail1040, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 450,
 Wasm.Binary.Instr.localGet 450,
 Wasm.Binary.Instr.localSet 451,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.localSet 452,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.localSet 453] ++ body74Tail1048), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1032 : List Instr := ([Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 447,
 Wasm.Binary.Instr.localGet 447,
 Wasm.Binary.Instr.localSet 517,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 448,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 449] ++ body74Tail1040)

@[cbv_eval] theorem sequence74_tail1032 :
    instructionSequenceAt 4144 false { bytes := artifactBytes, pos := 12674, limit := 15177 } =
      .ok ((body74Tail1032, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 447,
 Wasm.Binary.Instr.localGet 447,
 Wasm.Binary.Instr.localSet 517,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 448,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 449] ++ body74Tail1040), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1024 : List Instr := ([Wasm.Binary.Instr.localGet 426,
 Wasm.Binary.Instr.localGet 428,
 Wasm.Binary.Instr.localGet 429,
 Wasm.Binary.Instr.localGet 430,
 Wasm.Binary.Instr.localGet 443,
 Wasm.Binary.Instr.localGet 444,
 Wasm.Binary.Instr.localGet 445,
 Wasm.Binary.Instr.localGet 446] ++ body74Tail1032)

@[cbv_eval] theorem sequence74_tail1024 :
    instructionSequenceAt 4152 false { bytes := artifactBytes, pos := 12650, limit := 15177 } =
      .ok ((body74Tail1024, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 426,
 Wasm.Binary.Instr.localGet 428,
 Wasm.Binary.Instr.localGet 429,
 Wasm.Binary.Instr.localGet 430,
 Wasm.Binary.Instr.localGet 443,
 Wasm.Binary.Instr.localGet 444,
 Wasm.Binary.Instr.localGet 445,
 Wasm.Binary.Instr.localGet 446] ++ body74Tail1032), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1016 : List Instr := ([Wasm.Binary.Instr.localSet 443,
 Wasm.Binary.Instr.localGet 440,
 Wasm.Binary.Instr.localSet 444,
 Wasm.Binary.Instr.localGet 441,
 Wasm.Binary.Instr.localSet 445,
 Wasm.Binary.Instr.localGet 442,
 Wasm.Binary.Instr.localSet 446,
 Wasm.Binary.Instr.localGet 425] ++ body74Tail1024)

@[cbv_eval] theorem sequence74_tail1016 :
    instructionSequenceAt 4160 false { bytes := artifactBytes, pos := 12626, limit := 15177 } =
      .ok ((body74Tail1016, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 443,
 Wasm.Binary.Instr.localGet 440,
 Wasm.Binary.Instr.localSet 444,
 Wasm.Binary.Instr.localGet 441,
 Wasm.Binary.Instr.localSet 445,
 Wasm.Binary.Instr.localGet 442,
 Wasm.Binary.Instr.localSet 446,
 Wasm.Binary.Instr.localGet 425] ++ body74Tail1024), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1008 : List Instr := ([Wasm.Binary.Instr.localGet 437,
 Wasm.Binary.Instr.localGet 438,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 442,
 Wasm.Binary.Instr.localSet 441,
 Wasm.Binary.Instr.localSet 440,
 Wasm.Binary.Instr.localSet 439,
 Wasm.Binary.Instr.localGet 439] ++ body74Tail1016)

@[cbv_eval] theorem sequence74_tail1008 :
    instructionSequenceAt 4168 false { bytes := artifactBytes, pos := 12603, limit := 15177 } =
      .ok ((body74Tail1008, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 437,
 Wasm.Binary.Instr.localGet 438,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 442,
 Wasm.Binary.Instr.localSet 441,
 Wasm.Binary.Instr.localSet 440,
 Wasm.Binary.Instr.localSet 439,
 Wasm.Binary.Instr.localGet 439] ++ body74Tail1016), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1000 : List Instr := ([Wasm.Binary.Instr.localSet 437,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 438,
 Wasm.Binary.Instr.localGet 431,
 Wasm.Binary.Instr.localGet 432,
 Wasm.Binary.Instr.localGet 434,
 Wasm.Binary.Instr.localGet 435,
 Wasm.Binary.Instr.localGet 436] ++ body74Tail1008)

@[cbv_eval] theorem sequence74_tail1000 :
    instructionSequenceAt 4176 false { bytes := artifactBytes, pos := 12579, limit := 15177 } =
      .ok ((body74Tail1000, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 437,
 Wasm.Binary.Instr.localGet 424,
 Wasm.Binary.Instr.localSet 438,
 Wasm.Binary.Instr.localGet 431,
 Wasm.Binary.Instr.localGet 432,
 Wasm.Binary.Instr.localGet 434,
 Wasm.Binary.Instr.localGet 435,
 Wasm.Binary.Instr.localGet 436] ++ body74Tail1008), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail992 : List Instr := ([Wasm.Binary.Instr.localSet 433,
 Wasm.Binary.Instr.localGet 433,
 Wasm.Binary.Instr.localSet 434,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 435,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 436,
 Wasm.Binary.Instr.localGet 423] ++ body74Tail1000)

@[cbv_eval] theorem sequence74_tail992 :
    instructionSequenceAt 4184 false { bytes := artifactBytes, pos := 12555, limit := 15177 } =
      .ok ((body74Tail992, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 433,
 Wasm.Binary.Instr.localGet 433,
 Wasm.Binary.Instr.localSet 434,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.localSet 435,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.localSet 436,
 Wasm.Binary.Instr.localGet 423] ++ body74Tail1000), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail984 : List Instr := ([Wasm.Binary.Instr.localSet 429,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 430,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 431,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 432,
 Wasm.Binary.Instr.call 58] ++ body74Tail992)

@[cbv_eval] theorem sequence74_tail984 :
    instructionSequenceAt 4192 false { bytes := artifactBytes, pos := 12535, limit := 15177 } =
      .ok ((body74Tail984, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 429,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 430,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 431,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 432,
 Wasm.Binary.Instr.call 58] ++ body74Tail992), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail976 : List Instr := ([Wasm.Binary.Instr.localSet 425,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 426,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 427,
 Wasm.Binary.Instr.localGet 427,
 Wasm.Binary.Instr.localSet 428,
 Wasm.Binary.Instr.i64Const 8] ++ body74Tail984)

@[cbv_eval] theorem sequence74_tail976 :
    instructionSequenceAt 4200 false { bytes := artifactBytes, pos := 12514, limit := 15177 } =
      .ok ((body74Tail976, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 425,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 426,
 Wasm.Binary.Instr.call 55,
 Wasm.Binary.Instr.localSet 427,
 Wasm.Binary.Instr.localGet 427,
 Wasm.Binary.Instr.localSet 428,
 Wasm.Binary.Instr.i64Const 8] ++ body74Tail984), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail968 : List Instr := ([Wasm.Binary.Instr.localSet 421,
 Wasm.Binary.Instr.localGet 418,
 Wasm.Binary.Instr.localSet 422,
 Wasm.Binary.Instr.localGet 419,
 Wasm.Binary.Instr.localSet 423,
 Wasm.Binary.Instr.localGet 420,
 Wasm.Binary.Instr.localSet 424,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail976)

@[cbv_eval] theorem sequence74_tail968 :
    instructionSequenceAt 4208 false { bytes := artifactBytes, pos := 12491, limit := 15177 } =
      .ok ((body74Tail968, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 421,
 Wasm.Binary.Instr.localGet 418,
 Wasm.Binary.Instr.localSet 422,
 Wasm.Binary.Instr.localGet 419,
 Wasm.Binary.Instr.localSet 423,
 Wasm.Binary.Instr.localGet 420,
 Wasm.Binary.Instr.localSet 424,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail976), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail960 : List Instr := ([Wasm.Binary.Instr.localGet 415,
 Wasm.Binary.Instr.localGet 416,
 Wasm.Binary.Instr.call 4,
 Wasm.Binary.Instr.localSet 420,
 Wasm.Binary.Instr.localSet 419,
 Wasm.Binary.Instr.localSet 418,
 Wasm.Binary.Instr.localSet 417,
 Wasm.Binary.Instr.localGet 417] ++ body74Tail968)

@[cbv_eval] theorem sequence74_tail960 :
    instructionSequenceAt 4216 false { bytes := artifactBytes, pos := 12468, limit := 15177 } =
      .ok ((body74Tail960, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 415,
 Wasm.Binary.Instr.localGet 416,
 Wasm.Binary.Instr.call 4,
 Wasm.Binary.Instr.localSet 420,
 Wasm.Binary.Instr.localSet 419,
 Wasm.Binary.Instr.localSet 418,
 Wasm.Binary.Instr.localSet 417,
 Wasm.Binary.Instr.localGet 417] ++ body74Tail968), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail952 : List Instr := ([Wasm.Binary.Instr.localGet 387,
 Wasm.Binary.Instr.localSet 416,
 Wasm.Binary.Instr.localGet 409,
 Wasm.Binary.Instr.localGet 410,
 Wasm.Binary.Instr.localGet 411,
 Wasm.Binary.Instr.localGet 412,
 Wasm.Binary.Instr.localGet 413,
 Wasm.Binary.Instr.localGet 414] ++ body74Tail960)

@[cbv_eval] theorem sequence74_tail952 :
    instructionSequenceAt 4224 false { bytes := artifactBytes, pos := 12444, limit := 15177 } =
      .ok ((body74Tail952, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 387,
 Wasm.Binary.Instr.localSet 416,
 Wasm.Binary.Instr.localGet 409,
 Wasm.Binary.Instr.localGet 410,
 Wasm.Binary.Instr.localGet 411,
 Wasm.Binary.Instr.localGet 412,
 Wasm.Binary.Instr.localGet 413,
 Wasm.Binary.Instr.localGet 414] ++ body74Tail960), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail944 : List Instr := ([Wasm.Binary.Instr.localGet 408,
 Wasm.Binary.Instr.localSet 412,
 Wasm.Binary.Instr.localGet 384,
 Wasm.Binary.Instr.localSet 413,
 Wasm.Binary.Instr.localGet 385,
 Wasm.Binary.Instr.localSet 414,
 Wasm.Binary.Instr.localGet 386,
 Wasm.Binary.Instr.localSet 415] ++ body74Tail952)

@[cbv_eval] theorem sequence74_tail944 :
    instructionSequenceAt 4232 false { bytes := artifactBytes, pos := 12420, limit := 15177 } =
      .ok ((body74Tail944, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 408,
 Wasm.Binary.Instr.localSet 412,
 Wasm.Binary.Instr.localGet 384,
 Wasm.Binary.Instr.localSet 413,
 Wasm.Binary.Instr.localGet 385,
 Wasm.Binary.Instr.localSet 414,
 Wasm.Binary.Instr.localGet 386,
 Wasm.Binary.Instr.localSet 415] ++ body74Tail952), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail936 : List Instr := ([Wasm.Binary.Instr.localSet 406,
 Wasm.Binary.Instr.localSet 405,
 Wasm.Binary.Instr.localGet 405,
 Wasm.Binary.Instr.localSet 409,
 Wasm.Binary.Instr.localGet 406,
 Wasm.Binary.Instr.localSet 410,
 Wasm.Binary.Instr.localGet 407,
 Wasm.Binary.Instr.localSet 411] ++ body74Tail944)

@[cbv_eval] theorem sequence74_tail936 :
    instructionSequenceAt 4240 false { bytes := artifactBytes, pos := 12396, limit := 15177 } =
      .ok ((body74Tail936, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 406,
 Wasm.Binary.Instr.localSet 405,
 Wasm.Binary.Instr.localGet 405,
 Wasm.Binary.Instr.localSet 409,
 Wasm.Binary.Instr.localGet 406,
 Wasm.Binary.Instr.localSet 410,
 Wasm.Binary.Instr.localGet 407,
 Wasm.Binary.Instr.localSet 411] ++ body74Tail944), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail928 : List Instr := ([Wasm.Binary.Instr.localGet 400,
 Wasm.Binary.Instr.localGet 401,
 Wasm.Binary.Instr.localGet 402,
 Wasm.Binary.Instr.localGet 403,
 Wasm.Binary.Instr.localGet 404,
 Wasm.Binary.Instr.call 28,
 Wasm.Binary.Instr.localSet 408,
 Wasm.Binary.Instr.localSet 407] ++ body74Tail936)

@[cbv_eval] theorem sequence74_tail928 :
    instructionSequenceAt 4248 false { bytes := artifactBytes, pos := 12373, limit := 15177 } =
      .ok ((body74Tail928, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 400,
 Wasm.Binary.Instr.localGet 401,
 Wasm.Binary.Instr.localGet 402,
 Wasm.Binary.Instr.localGet 403,
 Wasm.Binary.Instr.localGet 404,
 Wasm.Binary.Instr.call 28,
 Wasm.Binary.Instr.localSet 408,
 Wasm.Binary.Instr.localSet 407] ++ body74Tail936), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
