import Project.TinyGpt2Hidden.ArtifactBody74Part13

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail280 : List Instr := ([Wasm.Binary.Instr.localGet 116,
 Wasm.Binary.Instr.localSet 136,
 Wasm.Binary.Instr.localGet 117,
 Wasm.Binary.Instr.localSet 137,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 138,
 Wasm.Binary.Instr.localGet 122,
 Wasm.Binary.Instr.localGet 123] ++ body74Tail288)

@[cbv_eval] theorem sequence74_tail280 :
    instructionSequenceAt 4896 false { bytes := artifactBytes, pos := 10569, limit := 15177 } =
      .ok ((body74Tail280, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 116,
 Wasm.Binary.Instr.localSet 136,
 Wasm.Binary.Instr.localGet 117,
 Wasm.Binary.Instr.localSet 137,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 138,
 Wasm.Binary.Instr.localGet 122,
 Wasm.Binary.Instr.localGet 123] ++ body74Tail288), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail272 : List Instr := ([Wasm.Binary.Instr.localGet 112,
 Wasm.Binary.Instr.localSet 132,
 Wasm.Binary.Instr.localGet 113,
 Wasm.Binary.Instr.localSet 133,
 Wasm.Binary.Instr.localGet 114,
 Wasm.Binary.Instr.localSet 134,
 Wasm.Binary.Instr.localGet 115,
 Wasm.Binary.Instr.localSet 135] ++ body74Tail280)

@[cbv_eval] theorem sequence74_tail272 :
    instructionSequenceAt 4904 false { bytes := artifactBytes, pos := 10549, limit := 15177 } =
      .ok ((body74Tail272, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 112,
 Wasm.Binary.Instr.localSet 132,
 Wasm.Binary.Instr.localGet 113,
 Wasm.Binary.Instr.localSet 133,
 Wasm.Binary.Instr.localGet 114,
 Wasm.Binary.Instr.localSet 134,
 Wasm.Binary.Instr.localGet 115,
 Wasm.Binary.Instr.localSet 135] ++ body74Tail280), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail264 : List Instr := ([Wasm.Binary.Instr.localGet 108,
 Wasm.Binary.Instr.localSet 128,
 Wasm.Binary.Instr.localGet 109,
 Wasm.Binary.Instr.localSet 129,
 Wasm.Binary.Instr.localGet 110,
 Wasm.Binary.Instr.localSet 130,
 Wasm.Binary.Instr.localGet 111,
 Wasm.Binary.Instr.localSet 131] ++ body74Tail272)

@[cbv_eval] theorem sequence74_tail264 :
    instructionSequenceAt 4912 false { bytes := artifactBytes, pos := 10529, limit := 15177 } =
      .ok ((body74Tail264, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 108,
 Wasm.Binary.Instr.localSet 128,
 Wasm.Binary.Instr.localGet 109,
 Wasm.Binary.Instr.localSet 129,
 Wasm.Binary.Instr.localGet 110,
 Wasm.Binary.Instr.localSet 130,
 Wasm.Binary.Instr.localGet 111,
 Wasm.Binary.Instr.localSet 131] ++ body74Tail272), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail256 : List Instr := ([Wasm.Binary.Instr.localGet 104,
 Wasm.Binary.Instr.localSet 124,
 Wasm.Binary.Instr.localGet 105,
 Wasm.Binary.Instr.localSet 125,
 Wasm.Binary.Instr.localGet 106,
 Wasm.Binary.Instr.localSet 126,
 Wasm.Binary.Instr.localGet 107,
 Wasm.Binary.Instr.localSet 127] ++ body74Tail264)

@[cbv_eval] theorem sequence74_tail256 :
    instructionSequenceAt 4920 false { bytes := artifactBytes, pos := 10513, limit := 15177 } =
      .ok ((body74Tail256, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 104,
 Wasm.Binary.Instr.localSet 124,
 Wasm.Binary.Instr.localGet 105,
 Wasm.Binary.Instr.localSet 125,
 Wasm.Binary.Instr.localGet 106,
 Wasm.Binary.Instr.localSet 126,
 Wasm.Binary.Instr.localGet 107,
 Wasm.Binary.Instr.localSet 127] ++ body74Tail264), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail248 : List Instr := ([Wasm.Binary.Instr.call 27,
 Wasm.Binary.Instr.localSet 120,
 Wasm.Binary.Instr.localGet 120,
 Wasm.Binary.Instr.localSet 121,
 Wasm.Binary.Instr.localGet 102,
 Wasm.Binary.Instr.localSet 122,
 Wasm.Binary.Instr.localGet 103,
 Wasm.Binary.Instr.localSet 123] ++ body74Tail256)

@[cbv_eval] theorem sequence74_tail248 :
    instructionSequenceAt 4928 false { bytes := artifactBytes, pos := 10497, limit := 15177 } =
      .ok ((body74Tail248, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 27,
 Wasm.Binary.Instr.localSet 120,
 Wasm.Binary.Instr.localGet 120,
 Wasm.Binary.Instr.localSet 121,
 Wasm.Binary.Instr.localGet 102,
 Wasm.Binary.Instr.localSet 122,
 Wasm.Binary.Instr.localGet 103,
 Wasm.Binary.Instr.localSet 123] ++ body74Tail256), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail240 : List Instr := ([Wasm.Binary.Instr.localGet 100,
 Wasm.Binary.Instr.localSet 116,
 Wasm.Binary.Instr.localGet 101,
 Wasm.Binary.Instr.localSet 117,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 118,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 119] ++ body74Tail248)

@[cbv_eval] theorem sequence74_tail240 :
    instructionSequenceAt 4936 false { bytes := artifactBytes, pos := 10481, limit := 15177 } =
      .ok ((body74Tail240, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 100,
 Wasm.Binary.Instr.localSet 116,
 Wasm.Binary.Instr.localGet 101,
 Wasm.Binary.Instr.localSet 117,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 118,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 119] ++ body74Tail248), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail232 : List Instr := ([Wasm.Binary.Instr.localSet 101,
 Wasm.Binary.Instr.localSet 100,
 Wasm.Binary.Instr.localSet 99,
 Wasm.Binary.Instr.localSet 98,
 Wasm.Binary.Instr.localGet 98,
 Wasm.Binary.Instr.localSet 114,
 Wasm.Binary.Instr.localGet 99,
 Wasm.Binary.Instr.localSet 115] ++ body74Tail240)

@[cbv_eval] theorem sequence74_tail232 :
    instructionSequenceAt 4944 false { bytes := artifactBytes, pos := 10465, limit := 15177 } =
      .ok ((body74Tail232, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 101,
 Wasm.Binary.Instr.localSet 100,
 Wasm.Binary.Instr.localSet 99,
 Wasm.Binary.Instr.localSet 98,
 Wasm.Binary.Instr.localGet 98,
 Wasm.Binary.Instr.localSet 114,
 Wasm.Binary.Instr.localGet 99,
 Wasm.Binary.Instr.localSet 115] ++ body74Tail240), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail224 : List Instr := ([Wasm.Binary.Instr.localGet 90,
 Wasm.Binary.Instr.localGet 91,
 Wasm.Binary.Instr.localGet 93,
 Wasm.Binary.Instr.localGet 94,
 Wasm.Binary.Instr.localGet 95,
 Wasm.Binary.Instr.localGet 96,
 Wasm.Binary.Instr.localGet 97,
 Wasm.Binary.Instr.call 17] ++ body74Tail232)

@[cbv_eval] theorem sequence74_tail224 :
    instructionSequenceAt 4952 false { bytes := artifactBytes, pos := 10449, limit := 15177 } =
      .ok ((body74Tail224, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 90,
 Wasm.Binary.Instr.localGet 91,
 Wasm.Binary.Instr.localGet 93,
 Wasm.Binary.Instr.localGet 94,
 Wasm.Binary.Instr.localGet 95,
 Wasm.Binary.Instr.localGet 96,
 Wasm.Binary.Instr.localGet 97,
 Wasm.Binary.Instr.call 17] ++ body74Tail232), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail216 : List Instr := ([Wasm.Binary.Instr.localGet 50,
 Wasm.Binary.Instr.localSet 94,
 Wasm.Binary.Instr.localGet 51,
 Wasm.Binary.Instr.localSet 95,
 Wasm.Binary.Instr.localGet 52,
 Wasm.Binary.Instr.localSet 96,
 Wasm.Binary.Instr.localGet 53,
 Wasm.Binary.Instr.localSet 97] ++ body74Tail224)

@[cbv_eval] theorem sequence74_tail216 :
    instructionSequenceAt 4960 false { bytes := artifactBytes, pos := 10433, limit := 15177 } =
      .ok ((body74Tail216, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 50,
 Wasm.Binary.Instr.localSet 94,
 Wasm.Binary.Instr.localGet 51,
 Wasm.Binary.Instr.localSet 95,
 Wasm.Binary.Instr.localGet 52,
 Wasm.Binary.Instr.localSet 96,
 Wasm.Binary.Instr.localGet 53,
 Wasm.Binary.Instr.localSet 97] ++ body74Tail224), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail208 : List Instr := ([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 90,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 91,
 Wasm.Binary.Instr.call 18,
 Wasm.Binary.Instr.localSet 92,
 Wasm.Binary.Instr.localGet 92,
 Wasm.Binary.Instr.localSet 93] ++ body74Tail216)

@[cbv_eval] theorem sequence74_tail208 :
    instructionSequenceAt 4968 false { bytes := artifactBytes, pos := 10417, limit := 15177 } =
      .ok ((body74Tail208, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 90,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 91,
 Wasm.Binary.Instr.call 18,
 Wasm.Binary.Instr.localSet 92,
 Wasm.Binary.Instr.localGet 92,
 Wasm.Binary.Instr.localSet 93] ++ body74Tail216), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail200 : List Instr := ([Wasm.Binary.Instr.localGet 86,
 Wasm.Binary.Instr.localSet 110,
 Wasm.Binary.Instr.localGet 87,
 Wasm.Binary.Instr.localSet 111,
 Wasm.Binary.Instr.localGet 88,
 Wasm.Binary.Instr.localSet 112,
 Wasm.Binary.Instr.localGet 89,
 Wasm.Binary.Instr.localSet 113] ++ body74Tail208)

@[cbv_eval] theorem sequence74_tail200 :
    instructionSequenceAt 4976 false { bytes := artifactBytes, pos := 10401, limit := 15177 } =
      .ok ((body74Tail200, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 86,
 Wasm.Binary.Instr.localSet 110,
 Wasm.Binary.Instr.localGet 87,
 Wasm.Binary.Instr.localSet 111,
 Wasm.Binary.Instr.localGet 88,
 Wasm.Binary.Instr.localSet 112,
 Wasm.Binary.Instr.localGet 89,
 Wasm.Binary.Instr.localSet 113] ++ body74Tail208), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail192 : List Instr := ([Wasm.Binary.Instr.localGet 83,
 Wasm.Binary.Instr.localGet 84,
 Wasm.Binary.Instr.localGet 85,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 89,
 Wasm.Binary.Instr.localSet 88,
 Wasm.Binary.Instr.localSet 87,
 Wasm.Binary.Instr.localSet 86] ++ body74Tail200)

@[cbv_eval] theorem sequence74_tail192 :
    instructionSequenceAt 4984 false { bytes := artifactBytes, pos := 10385, limit := 15177 } =
      .ok ((body74Tail192, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 83,
 Wasm.Binary.Instr.localGet 84,
 Wasm.Binary.Instr.localGet 85,
 Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 89,
 Wasm.Binary.Instr.localSet 88,
 Wasm.Binary.Instr.localSet 87,
 Wasm.Binary.Instr.localSet 86] ++ body74Tail200), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail184 : List Instr := ([Wasm.Binary.Instr.localGet 48,
 Wasm.Binary.Instr.localSet 84,
 Wasm.Binary.Instr.localGet 49,
 Wasm.Binary.Instr.localSet 85,
 Wasm.Binary.Instr.localGet 78,
 Wasm.Binary.Instr.localGet 79,
 Wasm.Binary.Instr.localGet 81,
 Wasm.Binary.Instr.localGet 82] ++ body74Tail192)

@[cbv_eval] theorem sequence74_tail184 :
    instructionSequenceAt 4992 false { bytes := artifactBytes, pos := 10369, limit := 15177 } =
      .ok ((body74Tail184, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 48,
 Wasm.Binary.Instr.localSet 84,
 Wasm.Binary.Instr.localGet 49,
 Wasm.Binary.Instr.localSet 85,
 Wasm.Binary.Instr.localGet 78,
 Wasm.Binary.Instr.localGet 79,
 Wasm.Binary.Instr.localGet 81,
 Wasm.Binary.Instr.localGet 82] ++ body74Tail192), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail176 : List Instr := ([Wasm.Binary.Instr.call 18,
 Wasm.Binary.Instr.localSet 80,
 Wasm.Binary.Instr.localGet 80,
 Wasm.Binary.Instr.localSet 81,
 Wasm.Binary.Instr.localGet 46,
 Wasm.Binary.Instr.localSet 82,
 Wasm.Binary.Instr.localGet 47,
 Wasm.Binary.Instr.localSet 83] ++ body74Tail184)

@[cbv_eval] theorem sequence74_tail176 :
    instructionSequenceAt 5000 false { bytes := artifactBytes, pos := 10353, limit := 15177 } =
      .ok ((body74Tail176, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 18,
 Wasm.Binary.Instr.localSet 80,
 Wasm.Binary.Instr.localGet 80,
 Wasm.Binary.Instr.localSet 81,
 Wasm.Binary.Instr.localGet 46,
 Wasm.Binary.Instr.localSet 82,
 Wasm.Binary.Instr.localGet 47,
 Wasm.Binary.Instr.localSet 83] ++ body74Tail184), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail168 : List Instr := ([Wasm.Binary.Instr.localGet 76,
 Wasm.Binary.Instr.localSet 108,
 Wasm.Binary.Instr.localGet 77,
 Wasm.Binary.Instr.localSet 109,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 78,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 79] ++ body74Tail176)

@[cbv_eval] theorem sequence74_tail168 :
    instructionSequenceAt 5008 false { bytes := artifactBytes, pos := 10337, limit := 15177 } =
      .ok ((body74Tail168, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 76,
 Wasm.Binary.Instr.localSet 108,
 Wasm.Binary.Instr.localGet 77,
 Wasm.Binary.Instr.localSet 109,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 78,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 79] ++ body74Tail176), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail160 : List Instr := ([Wasm.Binary.Instr.localSet 77,
 Wasm.Binary.Instr.localSet 76,
 Wasm.Binary.Instr.localSet 75,
 Wasm.Binary.Instr.localSet 74,
 Wasm.Binary.Instr.localGet 74,
 Wasm.Binary.Instr.localSet 106,
 Wasm.Binary.Instr.localGet 75,
 Wasm.Binary.Instr.localSet 107] ++ body74Tail168)

@[cbv_eval] theorem sequence74_tail160 :
    instructionSequenceAt 5016 false { bytes := artifactBytes, pos := 10321, limit := 15177 } =
      .ok ((body74Tail160, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 77,
 Wasm.Binary.Instr.localSet 76,
 Wasm.Binary.Instr.localSet 75,
 Wasm.Binary.Instr.localSet 74,
 Wasm.Binary.Instr.localGet 74,
 Wasm.Binary.Instr.localSet 106,
 Wasm.Binary.Instr.localGet 75,
 Wasm.Binary.Instr.localSet 107] ++ body74Tail168), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
