import Project.TinyGpt2Hidden.ArtifactBody74Part10

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail664 : List Instr := ([Wasm.Binary.Instr.localGet 295,
 Wasm.Binary.Instr.call 52,
 Wasm.Binary.Instr.localSet 299,
 Wasm.Binary.Instr.localSet 298,
 Wasm.Binary.Instr.localSet 297,
 Wasm.Binary.Instr.localSet 296,
 Wasm.Binary.Instr.localGet 296,
 Wasm.Binary.Instr.localSet 300] ++ body74Tail672)

@[cbv_eval] theorem sequence74_tail664 :
    instructionSequenceAt 4512 false { bytes := artifactBytes, pos := 11663, limit := 15177 } =
      .ok ((body74Tail664, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 295,
 Wasm.Binary.Instr.call 52,
 Wasm.Binary.Instr.localSet 299,
 Wasm.Binary.Instr.localSet 298,
 Wasm.Binary.Instr.localSet 297,
 Wasm.Binary.Instr.localSet 296,
 Wasm.Binary.Instr.localGet 296,
 Wasm.Binary.Instr.localSet 300] ++ body74Tail672), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail656 : List Instr := ([Wasm.Binary.Instr.localGet 287,
 Wasm.Binary.Instr.localGet 288,
 Wasm.Binary.Instr.localGet 289,
 Wasm.Binary.Instr.localGet 290,
 Wasm.Binary.Instr.localGet 291,
 Wasm.Binary.Instr.localGet 292,
 Wasm.Binary.Instr.localGet 293,
 Wasm.Binary.Instr.localGet 294] ++ body74Tail664)

@[cbv_eval] theorem sequence74_tail656 :
    instructionSequenceAt 4520 false { bytes := artifactBytes, pos := 11639, limit := 15177 } =
      .ok ((body74Tail656, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 287,
 Wasm.Binary.Instr.localGet 288,
 Wasm.Binary.Instr.localGet 289,
 Wasm.Binary.Instr.localGet 290,
 Wasm.Binary.Instr.localGet 291,
 Wasm.Binary.Instr.localGet 292,
 Wasm.Binary.Instr.localGet 293,
 Wasm.Binary.Instr.localGet 294] ++ body74Tail664), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail648 : List Instr := ([Wasm.Binary.Instr.localGet 279,
 Wasm.Binary.Instr.localGet 280,
 Wasm.Binary.Instr.localGet 281,
 Wasm.Binary.Instr.localGet 282,
 Wasm.Binary.Instr.localGet 283,
 Wasm.Binary.Instr.localGet 284,
 Wasm.Binary.Instr.localGet 285,
 Wasm.Binary.Instr.localGet 286] ++ body74Tail656)

@[cbv_eval] theorem sequence74_tail648 :
    instructionSequenceAt 4528 false { bytes := artifactBytes, pos := 11615, limit := 15177 } =
      .ok ((body74Tail648, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 279,
 Wasm.Binary.Instr.localGet 280,
 Wasm.Binary.Instr.localGet 281,
 Wasm.Binary.Instr.localGet 282,
 Wasm.Binary.Instr.localGet 283,
 Wasm.Binary.Instr.localGet 284,
 Wasm.Binary.Instr.localGet 285,
 Wasm.Binary.Instr.localGet 286] ++ body74Tail656), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail640 : List Instr := ([Wasm.Binary.Instr.localGet 271,
 Wasm.Binary.Instr.localGet 272,
 Wasm.Binary.Instr.localGet 273,
 Wasm.Binary.Instr.localGet 274,
 Wasm.Binary.Instr.localGet 275,
 Wasm.Binary.Instr.localGet 276,
 Wasm.Binary.Instr.localGet 277,
 Wasm.Binary.Instr.localGet 278] ++ body74Tail648)

@[cbv_eval] theorem sequence74_tail640 :
    instructionSequenceAt 4536 false { bytes := artifactBytes, pos := 11591, limit := 15177 } =
      .ok ((body74Tail640, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 271,
 Wasm.Binary.Instr.localGet 272,
 Wasm.Binary.Instr.localGet 273,
 Wasm.Binary.Instr.localGet 274,
 Wasm.Binary.Instr.localGet 275,
 Wasm.Binary.Instr.localGet 276,
 Wasm.Binary.Instr.localGet 277,
 Wasm.Binary.Instr.localGet 278] ++ body74Tail648), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail632 : List Instr := ([Wasm.Binary.Instr.localGet 263,
 Wasm.Binary.Instr.localGet 264,
 Wasm.Binary.Instr.localGet 265,
 Wasm.Binary.Instr.localGet 266,
 Wasm.Binary.Instr.localGet 267,
 Wasm.Binary.Instr.localGet 268,
 Wasm.Binary.Instr.localGet 269,
 Wasm.Binary.Instr.localGet 270] ++ body74Tail640)

@[cbv_eval] theorem sequence74_tail632 :
    instructionSequenceAt 4544 false { bytes := artifactBytes, pos := 11567, limit := 15177 } =
      .ok ((body74Tail632, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 263,
 Wasm.Binary.Instr.localGet 264,
 Wasm.Binary.Instr.localGet 265,
 Wasm.Binary.Instr.localGet 266,
 Wasm.Binary.Instr.localGet 267,
 Wasm.Binary.Instr.localGet 268,
 Wasm.Binary.Instr.localGet 269,
 Wasm.Binary.Instr.localGet 270] ++ body74Tail640), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail624 : List Instr := ([Wasm.Binary.Instr.localGet 257,
 Wasm.Binary.Instr.localSet 294,
 Wasm.Binary.Instr.localGet 258,
 Wasm.Binary.Instr.localSet 295,
 Wasm.Binary.Instr.localGet 259,
 Wasm.Binary.Instr.localGet 260,
 Wasm.Binary.Instr.localGet 261,
 Wasm.Binary.Instr.localGet 262] ++ body74Tail632)

@[cbv_eval] theorem sequence74_tail624 :
    instructionSequenceAt 4552 false { bytes := artifactBytes, pos := 11543, limit := 15177 } =
      .ok ((body74Tail624, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 257,
 Wasm.Binary.Instr.localSet 294,
 Wasm.Binary.Instr.localGet 258,
 Wasm.Binary.Instr.localSet 295,
 Wasm.Binary.Instr.localGet 259,
 Wasm.Binary.Instr.localGet 260,
 Wasm.Binary.Instr.localGet 261,
 Wasm.Binary.Instr.localGet 262] ++ body74Tail632), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail616 : List Instr := ([Wasm.Binary.Instr.localGet 253,
 Wasm.Binary.Instr.localSet 290,
 Wasm.Binary.Instr.localGet 254,
 Wasm.Binary.Instr.localSet 291,
 Wasm.Binary.Instr.localGet 255,
 Wasm.Binary.Instr.localSet 292,
 Wasm.Binary.Instr.localGet 256,
 Wasm.Binary.Instr.localSet 293] ++ body74Tail624)

@[cbv_eval] theorem sequence74_tail616 :
    instructionSequenceAt 4560 false { bytes := artifactBytes, pos := 11519, limit := 15177 } =
      .ok ((body74Tail616, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 253,
 Wasm.Binary.Instr.localSet 290,
 Wasm.Binary.Instr.localGet 254,
 Wasm.Binary.Instr.localSet 291,
 Wasm.Binary.Instr.localGet 255,
 Wasm.Binary.Instr.localSet 292,
 Wasm.Binary.Instr.localGet 256,
 Wasm.Binary.Instr.localSet 293] ++ body74Tail624), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail608 : List Instr := ([Wasm.Binary.Instr.localGet 249,
 Wasm.Binary.Instr.localSet 286,
 Wasm.Binary.Instr.localGet 250,
 Wasm.Binary.Instr.localSet 287,
 Wasm.Binary.Instr.localGet 251,
 Wasm.Binary.Instr.localSet 288,
 Wasm.Binary.Instr.localGet 252,
 Wasm.Binary.Instr.localSet 289] ++ body74Tail616)

@[cbv_eval] theorem sequence74_tail608 :
    instructionSequenceAt 4568 false { bytes := artifactBytes, pos := 11495, limit := 15177 } =
      .ok ((body74Tail608, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 249,
 Wasm.Binary.Instr.localSet 286,
 Wasm.Binary.Instr.localGet 250,
 Wasm.Binary.Instr.localSet 287,
 Wasm.Binary.Instr.localGet 251,
 Wasm.Binary.Instr.localSet 288,
 Wasm.Binary.Instr.localGet 252,
 Wasm.Binary.Instr.localSet 289] ++ body74Tail616), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail600 : List Instr := ([Wasm.Binary.Instr.localGet 245,
 Wasm.Binary.Instr.localSet 282,
 Wasm.Binary.Instr.localGet 246,
 Wasm.Binary.Instr.localSet 283,
 Wasm.Binary.Instr.localGet 247,
 Wasm.Binary.Instr.localSet 284,
 Wasm.Binary.Instr.localGet 248,
 Wasm.Binary.Instr.localSet 285] ++ body74Tail608)

@[cbv_eval] theorem sequence74_tail600 :
    instructionSequenceAt 4576 false { bytes := artifactBytes, pos := 11471, limit := 15177 } =
      .ok ((body74Tail600, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 245,
 Wasm.Binary.Instr.localSet 282,
 Wasm.Binary.Instr.localGet 246,
 Wasm.Binary.Instr.localSet 283,
 Wasm.Binary.Instr.localGet 247,
 Wasm.Binary.Instr.localSet 284,
 Wasm.Binary.Instr.localGet 248,
 Wasm.Binary.Instr.localSet 285] ++ body74Tail608), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail592 : List Instr := ([Wasm.Binary.Instr.localGet 205,
 Wasm.Binary.Instr.localSet 278,
 Wasm.Binary.Instr.localGet 206,
 Wasm.Binary.Instr.localSet 279,
 Wasm.Binary.Instr.localGet 243,
 Wasm.Binary.Instr.localSet 280,
 Wasm.Binary.Instr.localGet 244,
 Wasm.Binary.Instr.localSet 281] ++ body74Tail600)

@[cbv_eval] theorem sequence74_tail592 :
    instructionSequenceAt 4584 false { bytes := artifactBytes, pos := 11447, limit := 15177 } =
      .ok ((body74Tail592, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 205,
 Wasm.Binary.Instr.localSet 278,
 Wasm.Binary.Instr.localGet 206,
 Wasm.Binary.Instr.localSet 279,
 Wasm.Binary.Instr.localGet 243,
 Wasm.Binary.Instr.localSet 280,
 Wasm.Binary.Instr.localGet 244,
 Wasm.Binary.Instr.localSet 281] ++ body74Tail600), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail584 : List Instr := ([Wasm.Binary.Instr.localGet 201,
 Wasm.Binary.Instr.localSet 274,
 Wasm.Binary.Instr.localGet 202,
 Wasm.Binary.Instr.localSet 275,
 Wasm.Binary.Instr.localGet 203,
 Wasm.Binary.Instr.localSet 276,
 Wasm.Binary.Instr.localGet 204,
 Wasm.Binary.Instr.localSet 277] ++ body74Tail592)

@[cbv_eval] theorem sequence74_tail584 :
    instructionSequenceAt 4592 false { bytes := artifactBytes, pos := 11423, limit := 15177 } =
      .ok ((body74Tail584, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 201,
 Wasm.Binary.Instr.localSet 274,
 Wasm.Binary.Instr.localGet 202,
 Wasm.Binary.Instr.localSet 275,
 Wasm.Binary.Instr.localGet 203,
 Wasm.Binary.Instr.localSet 276,
 Wasm.Binary.Instr.localGet 204,
 Wasm.Binary.Instr.localSet 277] ++ body74Tail592), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail576 : List Instr := ([Wasm.Binary.Instr.localGet 197,
 Wasm.Binary.Instr.localSet 270,
 Wasm.Binary.Instr.localGet 198,
 Wasm.Binary.Instr.localSet 271,
 Wasm.Binary.Instr.localGet 199,
 Wasm.Binary.Instr.localSet 272,
 Wasm.Binary.Instr.localGet 200,
 Wasm.Binary.Instr.localSet 273] ++ body74Tail584)

@[cbv_eval] theorem sequence74_tail576 :
    instructionSequenceAt 4600 false { bytes := artifactBytes, pos := 11399, limit := 15177 } =
      .ok ((body74Tail576, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 197,
 Wasm.Binary.Instr.localSet 270,
 Wasm.Binary.Instr.localGet 198,
 Wasm.Binary.Instr.localSet 271,
 Wasm.Binary.Instr.localGet 199,
 Wasm.Binary.Instr.localSet 272,
 Wasm.Binary.Instr.localGet 200,
 Wasm.Binary.Instr.localSet 273] ++ body74Tail584), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail568 : List Instr := ([Wasm.Binary.Instr.localGet 193,
 Wasm.Binary.Instr.localSet 266,
 Wasm.Binary.Instr.localGet 194,
 Wasm.Binary.Instr.localSet 267,
 Wasm.Binary.Instr.localGet 195,
 Wasm.Binary.Instr.localSet 268,
 Wasm.Binary.Instr.localGet 196,
 Wasm.Binary.Instr.localSet 269] ++ body74Tail576)

@[cbv_eval] theorem sequence74_tail568 :
    instructionSequenceAt 4608 false { bytes := artifactBytes, pos := 11375, limit := 15177 } =
      .ok ((body74Tail568, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 193,
 Wasm.Binary.Instr.localSet 266,
 Wasm.Binary.Instr.localGet 194,
 Wasm.Binary.Instr.localSet 267,
 Wasm.Binary.Instr.localGet 195,
 Wasm.Binary.Instr.localSet 268,
 Wasm.Binary.Instr.localGet 196,
 Wasm.Binary.Instr.localSet 269] ++ body74Tail576), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail560 : List Instr := ([Wasm.Binary.Instr.localGet 153,
 Wasm.Binary.Instr.localSet 262,
 Wasm.Binary.Instr.localGet 154,
 Wasm.Binary.Instr.localSet 263,
 Wasm.Binary.Instr.localGet 191,
 Wasm.Binary.Instr.localSet 264,
 Wasm.Binary.Instr.localGet 192,
 Wasm.Binary.Instr.localSet 265] ++ body74Tail568)

@[cbv_eval] theorem sequence74_tail560 :
    instructionSequenceAt 4616 false { bytes := artifactBytes, pos := 11351, limit := 15177 } =
      .ok ((body74Tail560, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 153,
 Wasm.Binary.Instr.localSet 262,
 Wasm.Binary.Instr.localGet 154,
 Wasm.Binary.Instr.localSet 263,
 Wasm.Binary.Instr.localGet 191,
 Wasm.Binary.Instr.localSet 264,
 Wasm.Binary.Instr.localGet 192,
 Wasm.Binary.Instr.localSet 265] ++ body74Tail568), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail552 : List Instr := ([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localSet 259,
 Wasm.Binary.Instr.localGet 151,
 Wasm.Binary.Instr.localSet 260,
 Wasm.Binary.Instr.localGet 152,
 Wasm.Binary.Instr.localSet 261] ++ body74Tail560)

@[cbv_eval] theorem sequence74_tail552 :
    instructionSequenceAt 4624 false { bytes := artifactBytes, pos := 11331, limit := 15177 } =
      .ok ((body74Tail552, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 5,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.localSet 259,
 Wasm.Binary.Instr.localGet 151,
 Wasm.Binary.Instr.localSet 260,
 Wasm.Binary.Instr.localGet 152,
 Wasm.Binary.Instr.localSet 261] ++ body74Tail560), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail544 : List Instr := ([Wasm.Binary.Instr.localGet 239,
 Wasm.Binary.Instr.localSet 255,
 Wasm.Binary.Instr.localGet 240,
 Wasm.Binary.Instr.localSet 256,
 Wasm.Binary.Instr.localGet 241,
 Wasm.Binary.Instr.localSet 257,
 Wasm.Binary.Instr.localGet 242,
 Wasm.Binary.Instr.localSet 258] ++ body74Tail552)

@[cbv_eval] theorem sequence74_tail544 :
    instructionSequenceAt 4632 false { bytes := artifactBytes, pos := 11307, limit := 15177 } =
      .ok ((body74Tail544, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 239,
 Wasm.Binary.Instr.localSet 255,
 Wasm.Binary.Instr.localGet 240,
 Wasm.Binary.Instr.localSet 256,
 Wasm.Binary.Instr.localGet 241,
 Wasm.Binary.Instr.localSet 257,
 Wasm.Binary.Instr.localGet 242,
 Wasm.Binary.Instr.localSet 258] ++ body74Tail552), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
