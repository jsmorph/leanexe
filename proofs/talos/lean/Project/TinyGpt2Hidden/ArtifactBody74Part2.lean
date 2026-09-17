import Project.TinyGpt2Hidden.ArtifactBody74Part1

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail1816 : List Instr := ([Wasm.Binary.Instr.localSet 737,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 738,
 Wasm.Binary.Instr.localGet 701,
 Wasm.Binary.Instr.localSet 739,
 Wasm.Binary.Instr.localGet 702,
 Wasm.Binary.Instr.localSet 740,
 Wasm.Binary.Instr.localGet 703] ++ body74Tail1824)

@[cbv_eval] theorem sequence74_tail1816 :
    instructionSequenceAt 3360 false { bytes := artifactBytes, pos := 14836, limit := 15177 } =
      .ok ((body74Tail1816, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 737,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 738,
 Wasm.Binary.Instr.localGet 701,
 Wasm.Binary.Instr.localSet 739,
 Wasm.Binary.Instr.localGet 702,
 Wasm.Binary.Instr.localSet 740,
 Wasm.Binary.Instr.localGet 703] ++ body74Tail1824), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1808 : List Instr := ([Wasm.Binary.Instr.localGet 734,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 766,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail1816)

@[cbv_eval] theorem sequence74_tail1808 :
    instructionSequenceAt 3368 false { bytes := artifactBytes, pos := 14821, limit := 15177 } =
      .ok ((body74Tail1808, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 734,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 766,
 Wasm.Binary.Instr.localGet 423,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0] ++ body74Tail1816), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1800 : List Instr := ([Wasm.Binary.Instr.localGet 730,
 Wasm.Binary.Instr.localGet 731,
 Wasm.Binary.Instr.localGet 732,
 Wasm.Binary.Instr.call 72,
 Wasm.Binary.Instr.localSet 736,
 Wasm.Binary.Instr.localSet 735,
 Wasm.Binary.Instr.localSet 734,
 Wasm.Binary.Instr.localSet 733] ++ body74Tail1808)

@[cbv_eval] theorem sequence74_tail1800 :
    instructionSequenceAt 3376 false { bytes := artifactBytes, pos := 14798, limit := 15177 } =
      .ok ((body74Tail1800, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 730,
 Wasm.Binary.Instr.localGet 731,
 Wasm.Binary.Instr.localGet 732,
 Wasm.Binary.Instr.call 72,
 Wasm.Binary.Instr.localSet 736,
 Wasm.Binary.Instr.localSet 735,
 Wasm.Binary.Instr.localSet 734,
 Wasm.Binary.Instr.localSet 733] ++ body74Tail1808), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1792 : List Instr := ([Wasm.Binary.Instr.localSet 732,
 Wasm.Binary.Instr.localGet 723,
 Wasm.Binary.Instr.localGet 724,
 Wasm.Binary.Instr.localGet 725,
 Wasm.Binary.Instr.localGet 726,
 Wasm.Binary.Instr.localGet 727,
 Wasm.Binary.Instr.localGet 728,
 Wasm.Binary.Instr.localGet 729] ++ body74Tail1800)

@[cbv_eval] theorem sequence74_tail1792 :
    instructionSequenceAt 3384 false { bytes := artifactBytes, pos := 14774, limit := 15177 } =
      .ok ((body74Tail1792, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 732,
 Wasm.Binary.Instr.localGet 723,
 Wasm.Binary.Instr.localGet 724,
 Wasm.Binary.Instr.localGet 725,
 Wasm.Binary.Instr.localGet 726,
 Wasm.Binary.Instr.localGet 727,
 Wasm.Binary.Instr.localGet 728,
 Wasm.Binary.Instr.localGet 729] ++ body74Tail1800), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1784 : List Instr := ([Wasm.Binary.Instr.localSet 728,
 Wasm.Binary.Instr.localGet 705,
 Wasm.Binary.Instr.localSet 729,
 Wasm.Binary.Instr.localGet 706,
 Wasm.Binary.Instr.localSet 730,
 Wasm.Binary.Instr.localGet 707,
 Wasm.Binary.Instr.localSet 731,
 Wasm.Binary.Instr.localGet 708] ++ body74Tail1792)

@[cbv_eval] theorem sequence74_tail1784 :
    instructionSequenceAt 3392 false { bytes := artifactBytes, pos := 14750, limit := 15177 } =
      .ok ((body74Tail1784, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 728,
 Wasm.Binary.Instr.localGet 705,
 Wasm.Binary.Instr.localSet 729,
 Wasm.Binary.Instr.localGet 706,
 Wasm.Binary.Instr.localSet 730,
 Wasm.Binary.Instr.localGet 707,
 Wasm.Binary.Instr.localSet 731,
 Wasm.Binary.Instr.localGet 708] ++ body74Tail1792), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1776 : List Instr := ([Wasm.Binary.Instr.localSet 724,
 Wasm.Binary.Instr.localGet 701,
 Wasm.Binary.Instr.localSet 725,
 Wasm.Binary.Instr.localGet 702,
 Wasm.Binary.Instr.localSet 726,
 Wasm.Binary.Instr.localGet 703,
 Wasm.Binary.Instr.localSet 727,
 Wasm.Binary.Instr.localGet 704] ++ body74Tail1784)

@[cbv_eval] theorem sequence74_tail1776 :
    instructionSequenceAt 3400 false { bytes := artifactBytes, pos := 14726, limit := 15177 } =
      .ok ((body74Tail1776, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 724,
 Wasm.Binary.Instr.localGet 701,
 Wasm.Binary.Instr.localSet 725,
 Wasm.Binary.Instr.localGet 702,
 Wasm.Binary.Instr.localSet 726,
 Wasm.Binary.Instr.localGet 703,
 Wasm.Binary.Instr.localSet 727,
 Wasm.Binary.Instr.localGet 704] ++ body74Tail1784), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1768 : List Instr := ([Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 765,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 723,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail1776)

@[cbv_eval] theorem sequence74_tail1768 :
    instructionSequenceAt 3408 false { bytes := artifactBytes, pos := 14710, limit := 15177 } =
      .ok ((body74Tail1768, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 765,
 Wasm.Binary.Instr.localGet 422,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 723,
 Wasm.Binary.Instr.localGet 0] ++ body74Tail1776), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1760 : List Instr := ([Wasm.Binary.Instr.localGet 718,
 Wasm.Binary.Instr.call 72,
 Wasm.Binary.Instr.localSet 722,
 Wasm.Binary.Instr.localSet 721,
 Wasm.Binary.Instr.localSet 720,
 Wasm.Binary.Instr.localSet 719,
 Wasm.Binary.Instr.localGet 719,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body74Tail1768)

@[cbv_eval] theorem sequence74_tail1760 :
    instructionSequenceAt 3416 false { bytes := artifactBytes, pos := 14689, limit := 15177 } =
      .ok ((body74Tail1760, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 718,
 Wasm.Binary.Instr.call 72,
 Wasm.Binary.Instr.localSet 722,
 Wasm.Binary.Instr.localSet 721,
 Wasm.Binary.Instr.localSet 720,
 Wasm.Binary.Instr.localSet 719,
 Wasm.Binary.Instr.localGet 719,
 Wasm.Binary.Instr.f64ReinterpretI64] ++ body74Tail1768), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1752 : List Instr := ([Wasm.Binary.Instr.localGet 710,
 Wasm.Binary.Instr.localGet 711,
 Wasm.Binary.Instr.localGet 712,
 Wasm.Binary.Instr.localGet 713,
 Wasm.Binary.Instr.localGet 714,
 Wasm.Binary.Instr.localGet 715,
 Wasm.Binary.Instr.localGet 716,
 Wasm.Binary.Instr.localGet 717] ++ body74Tail1760)

@[cbv_eval] theorem sequence74_tail1752 :
    instructionSequenceAt 3424 false { bytes := artifactBytes, pos := 14665, limit := 15177 } =
      .ok ((body74Tail1752, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 710,
 Wasm.Binary.Instr.localGet 711,
 Wasm.Binary.Instr.localGet 712,
 Wasm.Binary.Instr.localGet 713,
 Wasm.Binary.Instr.localGet 714,
 Wasm.Binary.Instr.localGet 715,
 Wasm.Binary.Instr.localGet 716,
 Wasm.Binary.Instr.localGet 717] ++ body74Tail1760), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1744 : List Instr := ([Wasm.Binary.Instr.localSet 715,
 Wasm.Binary.Instr.localGet 706,
 Wasm.Binary.Instr.localSet 716,
 Wasm.Binary.Instr.localGet 707,
 Wasm.Binary.Instr.localSet 717,
 Wasm.Binary.Instr.localGet 708,
 Wasm.Binary.Instr.localSet 718,
 Wasm.Binary.Instr.localGet 709] ++ body74Tail1752)

@[cbv_eval] theorem sequence74_tail1744 :
    instructionSequenceAt 3432 false { bytes := artifactBytes, pos := 14641, limit := 15177 } =
      .ok ((body74Tail1744, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 715,
 Wasm.Binary.Instr.localGet 706,
 Wasm.Binary.Instr.localSet 716,
 Wasm.Binary.Instr.localGet 707,
 Wasm.Binary.Instr.localSet 717,
 Wasm.Binary.Instr.localGet 708,
 Wasm.Binary.Instr.localSet 718,
 Wasm.Binary.Instr.localGet 709] ++ body74Tail1752), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1736 : List Instr := ([Wasm.Binary.Instr.localSet 711,
 Wasm.Binary.Instr.localGet 702,
 Wasm.Binary.Instr.localSet 712,
 Wasm.Binary.Instr.localGet 703,
 Wasm.Binary.Instr.localSet 713,
 Wasm.Binary.Instr.localGet 704,
 Wasm.Binary.Instr.localSet 714,
 Wasm.Binary.Instr.localGet 705] ++ body74Tail1744)

@[cbv_eval] theorem sequence74_tail1736 :
    instructionSequenceAt 3440 false { bytes := artifactBytes, pos := 14617, limit := 15177 } =
      .ok ((body74Tail1736, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 711,
 Wasm.Binary.Instr.localGet 702,
 Wasm.Binary.Instr.localSet 712,
 Wasm.Binary.Instr.localGet 703,
 Wasm.Binary.Instr.localSet 713,
 Wasm.Binary.Instr.localGet 704,
 Wasm.Binary.Instr.localSet 714,
 Wasm.Binary.Instr.localGet 705] ++ body74Tail1744), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1728 : List Instr := ([Wasm.Binary.Instr.localSet 708,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 709,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 710,
 Wasm.Binary.Instr.localGet 701] ++ body74Tail1736)

@[cbv_eval] theorem sequence74_tail1728 :
    instructionSequenceAt 3448 false { bytes := artifactBytes, pos := 14597, limit := 15177 } =
      .ok ((body74Tail1728, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 708,
 Wasm.Binary.Instr.localGet 421,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 709,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 710,
 Wasm.Binary.Instr.localGet 701] ++ body74Tail1736), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1720 : List Instr := ([Wasm.Binary.Instr.localSet 697,
 Wasm.Binary.Instr.localGet 697,
 Wasm.Binary.Instr.localSet 705,
 Wasm.Binary.Instr.localGet 698,
 Wasm.Binary.Instr.localSet 706,
 Wasm.Binary.Instr.localGet 699,
 Wasm.Binary.Instr.localSet 707,
 Wasm.Binary.Instr.localGet 700] ++ body74Tail1728)

@[cbv_eval] theorem sequence74_tail1720 :
    instructionSequenceAt 3456 false { bytes := artifactBytes, pos := 14573, limit := 15177 } =
      .ok ((body74Tail1720, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 697,
 Wasm.Binary.Instr.localGet 697,
 Wasm.Binary.Instr.localSet 705,
 Wasm.Binary.Instr.localGet 698,
 Wasm.Binary.Instr.localSet 706,
 Wasm.Binary.Instr.localGet 699,
 Wasm.Binary.Instr.localSet 707,
 Wasm.Binary.Instr.localGet 700] ++ body74Tail1728), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1712 : List Instr := ([Wasm.Binary.Instr.localGet 693,
 Wasm.Binary.Instr.localGet 694,
 Wasm.Binary.Instr.localGet 695,
 Wasm.Binary.Instr.localGet 696,
 Wasm.Binary.Instr.call 65,
 Wasm.Binary.Instr.localSet 700,
 Wasm.Binary.Instr.localSet 699,
 Wasm.Binary.Instr.localSet 698] ++ body74Tail1720)

@[cbv_eval] theorem sequence74_tail1712 :
    instructionSequenceAt 3464 false { bytes := artifactBytes, pos := 14550, limit := 15177 } =
      .ok ((body74Tail1712, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 693,
 Wasm.Binary.Instr.localGet 694,
 Wasm.Binary.Instr.localGet 695,
 Wasm.Binary.Instr.localGet 696,
 Wasm.Binary.Instr.call 65,
 Wasm.Binary.Instr.localSet 700,
 Wasm.Binary.Instr.localSet 699,
 Wasm.Binary.Instr.localSet 698] ++ body74Tail1720), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1704 : List Instr := ([Wasm.Binary.Instr.localGet 681,
 Wasm.Binary.Instr.localSet 693,
 Wasm.Binary.Instr.localGet 682,
 Wasm.Binary.Instr.localSet 694,
 Wasm.Binary.Instr.localGet 683,
 Wasm.Binary.Instr.localSet 695,
 Wasm.Binary.Instr.localGet 684,
 Wasm.Binary.Instr.localSet 696] ++ body74Tail1712)

@[cbv_eval] theorem sequence74_tail1704 :
    instructionSequenceAt 3472 false { bytes := artifactBytes, pos := 14526, limit := 15177 } =
      .ok ((body74Tail1704, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 681,
 Wasm.Binary.Instr.localSet 693,
 Wasm.Binary.Instr.localGet 682,
 Wasm.Binary.Instr.localSet 694,
 Wasm.Binary.Instr.localGet 683,
 Wasm.Binary.Instr.localSet 695,
 Wasm.Binary.Instr.localGet 684,
 Wasm.Binary.Instr.localSet 696] ++ body74Tail1712), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1696 : List Instr := ([Wasm.Binary.Instr.localGet 689,
 Wasm.Binary.Instr.localSet 701,
 Wasm.Binary.Instr.localGet 690,
 Wasm.Binary.Instr.localSet 702,
 Wasm.Binary.Instr.localGet 691,
 Wasm.Binary.Instr.localSet 703,
 Wasm.Binary.Instr.localGet 692,
 Wasm.Binary.Instr.localSet 704] ++ body74Tail1704)

@[cbv_eval] theorem sequence74_tail1696 :
    instructionSequenceAt 3480 false { bytes := artifactBytes, pos := 14502, limit := 15177 } =
      .ok ((body74Tail1696, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 689,
 Wasm.Binary.Instr.localSet 701,
 Wasm.Binary.Instr.localGet 690,
 Wasm.Binary.Instr.localSet 702,
 Wasm.Binary.Instr.localGet 691,
 Wasm.Binary.Instr.localSet 703,
 Wasm.Binary.Instr.localGet 692,
 Wasm.Binary.Instr.localSet 704] ++ body74Tail1704), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
