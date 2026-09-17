import Project.TinyGpt2Hidden.ArtifactBody57Part1

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body57Tail360 : List Instr := ([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 135,
 Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 170,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171] ++ body57Tail368)

@[cbv_eval] theorem sequence57_tail360 :
    instructionSequenceAt 698 false { bytes := artifactBytes, pos := 7398, limit := 7739 } =
      .ok ((body57Tail360, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 135,
 Wasm.Binary.Instr.i64Const 1140,
 Wasm.Binary.Instr.localSet 170,
 Wasm.Binary.Instr.i64Const 4,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171] ++ body57Tail368), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail352 : List Instr := ([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 165,
 Wasm.Binary.Instr.localGet 98,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 134] ++ body57Tail360)

@[cbv_eval] theorem sequence57_tail352 :
    instructionSequenceAt 706 false { bytes := artifactBytes, pos := 7384, limit := 7739 } =
      .ok ((body57Tail352, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 165,
 Wasm.Binary.Instr.localGet 98,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 134] ++ body57Tail360), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail344 : List Instr := ([Wasm.Binary.Instr.localGet 127,
 Wasm.Binary.Instr.localGet 129,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 133,
 Wasm.Binary.Instr.localSet 132,
 Wasm.Binary.Instr.localSet 131,
 Wasm.Binary.Instr.localSet 130,
 Wasm.Binary.Instr.localGet 133] ++ body57Tail352)

@[cbv_eval] theorem sequence57_tail344 :
    instructionSequenceAt 714 false { bytes := artifactBytes, pos := 7362, limit := 7739 } =
      .ok ((body57Tail344, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 127,
 Wasm.Binary.Instr.localGet 129,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 133,
 Wasm.Binary.Instr.localSet 132,
 Wasm.Binary.Instr.localSet 131,
 Wasm.Binary.Instr.localSet 130,
 Wasm.Binary.Instr.localGet 133] ++ body57Tail352), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail336 : List Instr := ([Wasm.Binary.Instr.localSet 126,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 127,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 128,
 Wasm.Binary.Instr.localGet 128,
 Wasm.Binary.Instr.localSet 129,
 Wasm.Binary.Instr.localGet 126] ++ body57Tail344)

@[cbv_eval] theorem sequence57_tail336 :
    instructionSequenceAt 722 false { bytes := artifactBytes, pos := 7343, limit := 7739 } =
      .ok ((body57Tail336, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 126,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 127,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 128,
 Wasm.Binary.Instr.localGet 128,
 Wasm.Binary.Instr.localSet 129,
 Wasm.Binary.Instr.localGet 126] ++ body57Tail344), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail328 : List Instr := ([Wasm.Binary.Instr.localGet 124,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 164,
 Wasm.Binary.Instr.localGet 53,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0] ++ body57Tail336)

@[cbv_eval] theorem sequence57_tail328 :
    instructionSequenceAt 730 false { bytes := artifactBytes, pos := 7330, limit := 7739 } =
      .ok ((body57Tail328, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 124,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 164,
 Wasm.Binary.Instr.localGet 53,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0] ++ body57Tail336), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail320 : List Instr := ([Wasm.Binary.Instr.localGet 118,
 Wasm.Binary.Instr.localGet 119,
 Wasm.Binary.Instr.localGet 121,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 125,
 Wasm.Binary.Instr.localSet 124,
 Wasm.Binary.Instr.localSet 123,
 Wasm.Binary.Instr.localSet 122] ++ body57Tail328)

@[cbv_eval] theorem sequence57_tail320 :
    instructionSequenceAt 738 false { bytes := artifactBytes, pos := 7314, limit := 7739 } =
      .ok ((body57Tail320, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 118,
 Wasm.Binary.Instr.localGet 119,
 Wasm.Binary.Instr.localGet 121,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 125,
 Wasm.Binary.Instr.localSet 124,
 Wasm.Binary.Instr.localSet 123,
 Wasm.Binary.Instr.localSet 122] ++ body57Tail328), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail312 : List Instr := ([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 118,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 119,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 120,
 Wasm.Binary.Instr.localGet 120,
 Wasm.Binary.Instr.localSet 121] ++ body57Tail320)

@[cbv_eval] theorem sequence57_tail312 :
    instructionSequenceAt 746 false { bytes := artifactBytes, pos := 7298, limit := 7739 } =
      .ok ((body57Tail312, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 118,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 119,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 120,
 Wasm.Binary.Instr.localGet 120,
 Wasm.Binary.Instr.localSet 121] ++ body57Tail320), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail304 : List Instr := ([Wasm.Binary.Instr.localSet 114,
 Wasm.Binary.Instr.localGet 115,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 163,
 Wasm.Binary.Instr.localGet 52,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body57Tail312)

@[cbv_eval] theorem sequence57_tail304 :
    instructionSequenceAt 754 false { bytes := artifactBytes, pos := 7285, limit := 7739 } =
      .ok ((body57Tail304, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 114,
 Wasm.Binary.Instr.localGet 115,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 163,
 Wasm.Binary.Instr.localGet 52,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body57Tail312), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail296 : List Instr := ([Wasm.Binary.Instr.localSet 113,
 Wasm.Binary.Instr.localGet 110,
 Wasm.Binary.Instr.localGet 111,
 Wasm.Binary.Instr.localGet 113,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 117,
 Wasm.Binary.Instr.localSet 116,
 Wasm.Binary.Instr.localSet 115] ++ body57Tail304)

@[cbv_eval] theorem sequence57_tail296 :
    instructionSequenceAt 762 false { bytes := artifactBytes, pos := 7269, limit := 7739 } =
      .ok ((body57Tail296, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 113,
 Wasm.Binary.Instr.localGet 110,
 Wasm.Binary.Instr.localGet 111,
 Wasm.Binary.Instr.localGet 113,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 117,
 Wasm.Binary.Instr.localSet 116,
 Wasm.Binary.Instr.localSet 115] ++ body57Tail304), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail288 : List Instr := ([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 110,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 111,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 112,
 Wasm.Binary.Instr.localGet 112] ++ body57Tail296)

@[cbv_eval] theorem sequence57_tail288 :
    instructionSequenceAt 770 false { bytes := artifactBytes, pos := 7254, limit := 7739 } =
      .ok ((body57Tail288, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 110,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 111,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 112,
 Wasm.Binary.Instr.localGet 112] ++ body57Tail296), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail280 : List Instr := ([Wasm.Binary.Instr.localSet 107,
 Wasm.Binary.Instr.localSet 106,
 Wasm.Binary.Instr.localGet 106,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 162,
 Wasm.Binary.Instr.localGet 51] ++ body57Tail288)

@[cbv_eval] theorem sequence57_tail280 :
    instructionSequenceAt 778 false { bytes := artifactBytes, pos := 7240, limit := 7739 } =
      .ok ((body57Tail280, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 107,
 Wasm.Binary.Instr.localSet 106,
 Wasm.Binary.Instr.localGet 106,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 162,
 Wasm.Binary.Instr.localGet 51] ++ body57Tail288), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail272 : List Instr := ([Wasm.Binary.Instr.localGet 104,
 Wasm.Binary.Instr.localSet 105,
 Wasm.Binary.Instr.localGet 102,
 Wasm.Binary.Instr.localGet 103,
 Wasm.Binary.Instr.localGet 105,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 109,
 Wasm.Binary.Instr.localSet 108] ++ body57Tail280)

@[cbv_eval] theorem sequence57_tail272 :
    instructionSequenceAt 786 false { bytes := artifactBytes, pos := 7224, limit := 7739 } =
      .ok ((body57Tail272, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 104,
 Wasm.Binary.Instr.localSet 105,
 Wasm.Binary.Instr.localGet 102,
 Wasm.Binary.Instr.localGet 103,
 Wasm.Binary.Instr.localGet 105,
 Wasm.Binary.Instr.call 5,
 Wasm.Binary.Instr.localSet 109,
 Wasm.Binary.Instr.localSet 108] ++ body57Tail280), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail264 : List Instr := ([Wasm.Binary.Instr.localGet 50,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 102,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 103,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 104] ++ body57Tail272)

@[cbv_eval] theorem sequence57_tail264 :
    instructionSequenceAt 794 false { bytes := artifactBytes, pos := 7209, limit := 7739 } =
      .ok ((body57Tail264, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 50,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 102,
 Wasm.Binary.Instr.localGet 1,
 Wasm.Binary.Instr.localSet 103,
 Wasm.Binary.Instr.call 56,
 Wasm.Binary.Instr.localSet 104] ++ body57Tail272), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail256 : List Instr := ([Wasm.Binary.Instr.localGet 93,
 Wasm.Binary.Instr.localGet 94,
 Wasm.Binary.Instr.localGet 95,
 Wasm.Binary.Instr.localGet 96,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 97,
 Wasm.Binary.Instr.localGet 97,
 Wasm.Binary.Instr.localSet 101] ++ body57Tail264)

@[cbv_eval] theorem sequence57_tail256 :
    instructionSequenceAt 802 false { bytes := artifactBytes, pos := 7193, limit := 7739 } =
      .ok ((body57Tail256, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 93,
 Wasm.Binary.Instr.localGet 94,
 Wasm.Binary.Instr.localGet 95,
 Wasm.Binary.Instr.localGet 96,
 Wasm.Binary.Instr.call 25,
 Wasm.Binary.Instr.localSet 97,
 Wasm.Binary.Instr.localGet 97,
 Wasm.Binary.Instr.localSet 101] ++ body57Tail264), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail248 : List Instr := ([Wasm.Binary.Instr.localSet 95,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 96,
 Wasm.Binary.Instr.localGet 87,
 Wasm.Binary.Instr.localGet 88,
 Wasm.Binary.Instr.localGet 90,
 Wasm.Binary.Instr.localGet 91,
 Wasm.Binary.Instr.localGet 92] ++ body57Tail256)

@[cbv_eval] theorem sequence57_tail248 :
    instructionSequenceAt 810 false { bytes := artifactBytes, pos := 7177, limit := 7739 } =
      .ok ((body57Tail248, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 95,
 Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.localSet 96,
 Wasm.Binary.Instr.localGet 87,
 Wasm.Binary.Instr.localGet 88,
 Wasm.Binary.Instr.localGet 90,
 Wasm.Binary.Instr.localGet 91,
 Wasm.Binary.Instr.localGet 92] ++ body57Tail256), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body57Tail240 : List Instr := ([Wasm.Binary.Instr.localSet 91,
 Wasm.Binary.Instr.i64Const 7,
 Wasm.Binary.Instr.localSet 92,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 93,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 94,
 Wasm.Binary.Instr.localGet 4] ++ body57Tail248)

@[cbv_eval] theorem sequence57_tail240 :
    instructionSequenceAt 818 false { bytes := artifactBytes, pos := 7161, limit := 7739 } =
      .ok ((body57Tail240, .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 91,
 Wasm.Binary.Instr.i64Const 7,
 Wasm.Binary.Instr.localSet 92,
 Wasm.Binary.Instr.localGet 2,
 Wasm.Binary.Instr.localSet 93,
 Wasm.Binary.Instr.localGet 3,
 Wasm.Binary.Instr.localSet 94,
 Wasm.Binary.Instr.localGet 4] ++ body57Tail248), .end), { bytes := artifactBytes, pos := 7739, limit := 7739 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
