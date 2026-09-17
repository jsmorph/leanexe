import Project.TinyGpt2Hidden.ArtifactBody74Part12

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail408 : List Instr := ([Wasm.Binary.Instr.localSet 178,
 Wasm.Binary.Instr.localSet 177,
 Wasm.Binary.Instr.localSet 176,
 Wasm.Binary.Instr.localSet 175,
 Wasm.Binary.Instr.localGet 175,
 Wasm.Binary.Instr.localSet 191,
 Wasm.Binary.Instr.localGet 176,
 Wasm.Binary.Instr.localSet 192] ++ body74Tail416)

@[cbv_eval] theorem sequence74_tail408 :
    instructionSequenceAt 4768 false { bytes := artifactBytes, pos := 10919, limit := 15177 } =
      .ok ((body74Tail408, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 178,
 Wasm.Binary.Instr.localSet 177,
 Wasm.Binary.Instr.localSet 176,
 Wasm.Binary.Instr.localSet 175,
 Wasm.Binary.Instr.localGet 175,
 Wasm.Binary.Instr.localSet 191,
 Wasm.Binary.Instr.localGet 176,
 Wasm.Binary.Instr.localSet 192] ++ body74Tail416), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail400 : List Instr := ([Wasm.Binary.Instr.localSet 186,
 Wasm.Binary.Instr.localSet 185,
 Wasm.Binary.Instr.localSet 184,
 Wasm.Binary.Instr.localSet 183,
 Wasm.Binary.Instr.localSet 182,
 Wasm.Binary.Instr.localSet 181,
 Wasm.Binary.Instr.localSet 180,
 Wasm.Binary.Instr.localSet 179] ++ body74Tail408)

@[cbv_eval] theorem sequence74_tail400 :
    instructionSequenceAt 4776 false { bytes := artifactBytes, pos := 10895, limit := 15177 } =
      .ok ((body74Tail400, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 186,
 Wasm.Binary.Instr.localSet 185,
 Wasm.Binary.Instr.localSet 184,
 Wasm.Binary.Instr.localSet 183,
 Wasm.Binary.Instr.localSet 182,
 Wasm.Binary.Instr.localSet 181,
 Wasm.Binary.Instr.localSet 180,
 Wasm.Binary.Instr.localSet 179] ++ body74Tail408), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail392 : List Instr := ([Wasm.Binary.Instr.localGet 172,
 Wasm.Binary.Instr.localGet 173,
 Wasm.Binary.Instr.localGet 174,
 Wasm.Binary.Instr.call 29,
 Wasm.Binary.Instr.localSet 190,
 Wasm.Binary.Instr.localSet 189,
 Wasm.Binary.Instr.localSet 188,
 Wasm.Binary.Instr.localSet 187] ++ body74Tail400)

@[cbv_eval] theorem sequence74_tail392 :
    instructionSequenceAt 4784 false { bytes := artifactBytes, pos := 10872, limit := 15177 } =
      .ok ((body74Tail392, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 172,
 Wasm.Binary.Instr.localGet 173,
 Wasm.Binary.Instr.localGet 174,
 Wasm.Binary.Instr.call 29,
 Wasm.Binary.Instr.localSet 190,
 Wasm.Binary.Instr.localSet 189,
 Wasm.Binary.Instr.localSet 188,
 Wasm.Binary.Instr.localSet 187] ++ body74Tail400), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail384 : List Instr := ([Wasm.Binary.Instr.localGet 164,
 Wasm.Binary.Instr.localGet 165,
 Wasm.Binary.Instr.localGet 166,
 Wasm.Binary.Instr.localGet 167,
 Wasm.Binary.Instr.localGet 168,
 Wasm.Binary.Instr.localGet 169,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171] ++ body74Tail392)

@[cbv_eval] theorem sequence74_tail384 :
    instructionSequenceAt 4792 false { bytes := artifactBytes, pos := 10848, limit := 15177 } =
      .ok ((body74Tail384, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 164,
 Wasm.Binary.Instr.localGet 165,
 Wasm.Binary.Instr.localGet 166,
 Wasm.Binary.Instr.localGet 167,
 Wasm.Binary.Instr.localGet 168,
 Wasm.Binary.Instr.localGet 169,
 Wasm.Binary.Instr.localGet 170,
 Wasm.Binary.Instr.localGet 171] ++ body74Tail392), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail376 : List Instr := ([Wasm.Binary.Instr.localGet 155,
 Wasm.Binary.Instr.localGet 156,
 Wasm.Binary.Instr.localGet 158,
 Wasm.Binary.Instr.localGet 159,
 Wasm.Binary.Instr.localGet 160,
 Wasm.Binary.Instr.localGet 161,
 Wasm.Binary.Instr.localGet 162,
 Wasm.Binary.Instr.localGet 163] ++ body74Tail384)

@[cbv_eval] theorem sequence74_tail376 :
    instructionSequenceAt 4800 false { bytes := artifactBytes, pos := 10824, limit := 15177 } =
      .ok ((body74Tail376, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 155,
 Wasm.Binary.Instr.localGet 156,
 Wasm.Binary.Instr.localGet 158,
 Wasm.Binary.Instr.localGet 159,
 Wasm.Binary.Instr.localGet 160,
 Wasm.Binary.Instr.localGet 161,
 Wasm.Binary.Instr.localGet 162,
 Wasm.Binary.Instr.localGet 163] ++ body74Tail384), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail368 : List Instr := ([Wasm.Binary.Instr.localGet 114,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 115,
 Wasm.Binary.Instr.localSet 172,
 Wasm.Binary.Instr.localGet 116,
 Wasm.Binary.Instr.localSet 173,
 Wasm.Binary.Instr.localGet 117,
 Wasm.Binary.Instr.localSet 174] ++ body74Tail376)

@[cbv_eval] theorem sequence74_tail368 :
    instructionSequenceAt 4808 false { bytes := artifactBytes, pos := 10804, limit := 15177 } =
      .ok ((body74Tail368, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 114,
 Wasm.Binary.Instr.localSet 171,
 Wasm.Binary.Instr.localGet 115,
 Wasm.Binary.Instr.localSet 172,
 Wasm.Binary.Instr.localGet 116,
 Wasm.Binary.Instr.localSet 173,
 Wasm.Binary.Instr.localGet 117,
 Wasm.Binary.Instr.localSet 174] ++ body74Tail376), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail360 : List Instr := ([Wasm.Binary.Instr.localGet 110,
 Wasm.Binary.Instr.localSet 167,
 Wasm.Binary.Instr.localGet 111,
 Wasm.Binary.Instr.localSet 168,
 Wasm.Binary.Instr.localGet 112,
 Wasm.Binary.Instr.localSet 169,
 Wasm.Binary.Instr.localGet 113,
 Wasm.Binary.Instr.localSet 170] ++ body74Tail368)

@[cbv_eval] theorem sequence74_tail360 :
    instructionSequenceAt 4816 false { bytes := artifactBytes, pos := 10784, limit := 15177 } =
      .ok ((body74Tail360, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 110,
 Wasm.Binary.Instr.localSet 167,
 Wasm.Binary.Instr.localGet 111,
 Wasm.Binary.Instr.localSet 168,
 Wasm.Binary.Instr.localGet 112,
 Wasm.Binary.Instr.localSet 169,
 Wasm.Binary.Instr.localGet 113,
 Wasm.Binary.Instr.localSet 170] ++ body74Tail368), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail352 : List Instr := ([Wasm.Binary.Instr.localGet 106,
 Wasm.Binary.Instr.localSet 163,
 Wasm.Binary.Instr.localGet 107,
 Wasm.Binary.Instr.localSet 164,
 Wasm.Binary.Instr.localGet 108,
 Wasm.Binary.Instr.localSet 165,
 Wasm.Binary.Instr.localGet 109,
 Wasm.Binary.Instr.localSet 166] ++ body74Tail360)

@[cbv_eval] theorem sequence74_tail352 :
    instructionSequenceAt 4824 false { bytes := artifactBytes, pos := 10764, limit := 15177 } =
      .ok ((body74Tail352, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 106,
 Wasm.Binary.Instr.localSet 163,
 Wasm.Binary.Instr.localGet 107,
 Wasm.Binary.Instr.localSet 164,
 Wasm.Binary.Instr.localGet 108,
 Wasm.Binary.Instr.localSet 165,
 Wasm.Binary.Instr.localGet 109,
 Wasm.Binary.Instr.localSet 166] ++ body74Tail360), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail344 : List Instr := ([Wasm.Binary.Instr.localGet 102,
 Wasm.Binary.Instr.localSet 159,
 Wasm.Binary.Instr.localGet 103,
 Wasm.Binary.Instr.localSet 160,
 Wasm.Binary.Instr.localGet 104,
 Wasm.Binary.Instr.localSet 161,
 Wasm.Binary.Instr.localGet 105,
 Wasm.Binary.Instr.localSet 162] ++ body74Tail352)

@[cbv_eval] theorem sequence74_tail344 :
    instructionSequenceAt 4832 false { bytes := artifactBytes, pos := 10744, limit := 15177 } =
      .ok ((body74Tail344, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 102,
 Wasm.Binary.Instr.localSet 159,
 Wasm.Binary.Instr.localGet 103,
 Wasm.Binary.Instr.localSet 160,
 Wasm.Binary.Instr.localGet 104,
 Wasm.Binary.Instr.localSet 161,
 Wasm.Binary.Instr.localGet 105,
 Wasm.Binary.Instr.localSet 162] ++ body74Tail352), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail336 : List Instr := ([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 155,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 156,
 Wasm.Binary.Instr.call 30,
 Wasm.Binary.Instr.localSet 157,
 Wasm.Binary.Instr.localGet 157,
 Wasm.Binary.Instr.localSet 158] ++ body74Tail344)

@[cbv_eval] theorem sequence74_tail336 :
    instructionSequenceAt 4840 false { bytes := artifactBytes, pos := 10723, limit := 15177 } =
      .ok ((body74Tail336, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 155,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 156,
 Wasm.Binary.Instr.call 30,
 Wasm.Binary.Instr.localSet 157,
 Wasm.Binary.Instr.localGet 157,
 Wasm.Binary.Instr.localSet 158] ++ body74Tail344), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail328 : List Instr := ([Wasm.Binary.Instr.localGet 147,
 Wasm.Binary.Instr.localSet 151,
 Wasm.Binary.Instr.localGet 148,
 Wasm.Binary.Instr.localSet 152,
 Wasm.Binary.Instr.localGet 149,
 Wasm.Binary.Instr.localSet 153,
 Wasm.Binary.Instr.localGet 150,
 Wasm.Binary.Instr.localSet 154] ++ body74Tail336)

@[cbv_eval] theorem sequence74_tail328 :
    instructionSequenceAt 4848 false { bytes := artifactBytes, pos := 10699, limit := 15177 } =
      .ok ((body74Tail328, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 147,
 Wasm.Binary.Instr.localSet 151,
 Wasm.Binary.Instr.localGet 148,
 Wasm.Binary.Instr.localSet 152,
 Wasm.Binary.Instr.localGet 149,
 Wasm.Binary.Instr.localSet 153,
 Wasm.Binary.Instr.localGet 150,
 Wasm.Binary.Instr.localSet 154] ++ body74Tail336), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail320 : List Instr := ([Wasm.Binary.Instr.localGet 144,
 Wasm.Binary.Instr.localGet 145,
 Wasm.Binary.Instr.localGet 146,
 Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 150,
 Wasm.Binary.Instr.localSet 149,
 Wasm.Binary.Instr.localSet 148,
 Wasm.Binary.Instr.localSet 147] ++ body74Tail328)

@[cbv_eval] theorem sequence74_tail320 :
    instructionSequenceAt 4856 false { bytes := artifactBytes, pos := 10676, limit := 15177 } =
      .ok ((body74Tail320, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 144,
 Wasm.Binary.Instr.localGet 145,
 Wasm.Binary.Instr.localGet 146,
 Wasm.Binary.Instr.call 26,
 Wasm.Binary.Instr.localSet 150,
 Wasm.Binary.Instr.localSet 149,
 Wasm.Binary.Instr.localSet 148,
 Wasm.Binary.Instr.localSet 147] ++ body74Tail328), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail312 : List Instr := ([Wasm.Binary.Instr.localGet 141,
 Wasm.Binary.Instr.localSet 145,
 Wasm.Binary.Instr.localGet 142,
 Wasm.Binary.Instr.localSet 146,
 Wasm.Binary.Instr.localGet 118,
 Wasm.Binary.Instr.localGet 119,
 Wasm.Binary.Instr.localGet 121,
 Wasm.Binary.Instr.localGet 143] ++ body74Tail320)

@[cbv_eval] theorem sequence74_tail312 :
    instructionSequenceAt 4864 false { bytes := artifactBytes, pos := 10655, limit := 15177 } =
      .ok ((body74Tail312, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 141,
 Wasm.Binary.Instr.localSet 145,
 Wasm.Binary.Instr.localGet 142,
 Wasm.Binary.Instr.localSet 146,
 Wasm.Binary.Instr.localGet 118,
 Wasm.Binary.Instr.localGet 119,
 Wasm.Binary.Instr.localGet 121,
 Wasm.Binary.Instr.localGet 143] ++ body74Tail320), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail304 : List Instr := ([Wasm.Binary.Instr.localSet 142,
 Wasm.Binary.Instr.localSet 141,
 Wasm.Binary.Instr.localSet 140,
 Wasm.Binary.Instr.localSet 139,
 Wasm.Binary.Instr.localGet 139,
 Wasm.Binary.Instr.localSet 143,
 Wasm.Binary.Instr.localGet 140,
 Wasm.Binary.Instr.localSet 144] ++ body74Tail312)

@[cbv_eval] theorem sequence74_tail304 :
    instructionSequenceAt 4872 false { bytes := artifactBytes, pos := 10631, limit := 15177 } =
      .ok ((body74Tail304, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 142,
 Wasm.Binary.Instr.localSet 141,
 Wasm.Binary.Instr.localSet 140,
 Wasm.Binary.Instr.localSet 139,
 Wasm.Binary.Instr.localGet 139,
 Wasm.Binary.Instr.localSet 143,
 Wasm.Binary.Instr.localGet 140,
 Wasm.Binary.Instr.localSet 144] ++ body74Tail312), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail296 : List Instr := ([Wasm.Binary.Instr.localGet 132,
 Wasm.Binary.Instr.localGet 133,
 Wasm.Binary.Instr.localGet 134,
 Wasm.Binary.Instr.localGet 135,
 Wasm.Binary.Instr.localGet 136,
 Wasm.Binary.Instr.localGet 137,
 Wasm.Binary.Instr.localGet 138,
 Wasm.Binary.Instr.call 28] ++ body74Tail304)

@[cbv_eval] theorem sequence74_tail296 :
    instructionSequenceAt 4880 false { bytes := artifactBytes, pos := 10608, limit := 15177 } =
      .ok ((body74Tail296, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 132,
 Wasm.Binary.Instr.localGet 133,
 Wasm.Binary.Instr.localGet 134,
 Wasm.Binary.Instr.localGet 135,
 Wasm.Binary.Instr.localGet 136,
 Wasm.Binary.Instr.localGet 137,
 Wasm.Binary.Instr.localGet 138,
 Wasm.Binary.Instr.call 28] ++ body74Tail304), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail288 : List Instr := ([Wasm.Binary.Instr.localGet 124,
 Wasm.Binary.Instr.localGet 125,
 Wasm.Binary.Instr.localGet 126,
 Wasm.Binary.Instr.localGet 127,
 Wasm.Binary.Instr.localGet 128,
 Wasm.Binary.Instr.localGet 129,
 Wasm.Binary.Instr.localGet 130,
 Wasm.Binary.Instr.localGet 131] ++ body74Tail296)

@[cbv_eval] theorem sequence74_tail288 :
    instructionSequenceAt 4888 false { bytes := artifactBytes, pos := 10588, limit := 15177 } =
      .ok ((body74Tail288, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 124,
 Wasm.Binary.Instr.localGet 125,
 Wasm.Binary.Instr.localGet 126,
 Wasm.Binary.Instr.localGet 127,
 Wasm.Binary.Instr.localGet 128,
 Wasm.Binary.Instr.localGet 129,
 Wasm.Binary.Instr.localGet 130,
 Wasm.Binary.Instr.localGet 131] ++ body74Tail296), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
