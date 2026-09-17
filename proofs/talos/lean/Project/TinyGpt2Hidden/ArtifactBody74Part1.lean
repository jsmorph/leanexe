import Project.TinyGpt2Hidden.ArtifactBody74Part0

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_opaque] def body74Tail1937 : List Instr := []

@[cbv_eval] theorem sequence74_tail1937 :
    instructionSequenceAt 3239 false { bytes := artifactBytes, pos := 15176, limit := 15177 } =
      .ok ((body74Tail1937, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok (([], .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1936 : List Instr := ([Wasm.Binary.Instr.localGet 784] ++ body74Tail1937)

@[cbv_eval] theorem sequence74_tail1936 :
    instructionSequenceAt 3240 false { bytes := artifactBytes, pos := 15173, limit := 15177 } =
      .ok ((body74Tail1936, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 784] ++ body74Tail1937), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1928 : List Instr := ([Wasm.Binary.Instr.localSet 782,
 Wasm.Binary.Instr.localGet 779,
 Wasm.Binary.Instr.localSet 783,
 Wasm.Binary.Instr.localGet 780,
 Wasm.Binary.Instr.localSet 784,
 Wasm.Binary.Instr.localGet 781,
 Wasm.Binary.Instr.localGet 782,
 Wasm.Binary.Instr.localGet 783] ++ body74Tail1936)

@[cbv_eval] theorem sequence74_tail1928 :
    instructionSequenceAt 3248 false { bytes := artifactBytes, pos := 15149, limit := 15177 } =
      .ok ((body74Tail1928, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 782,
 Wasm.Binary.Instr.localGet 779,
 Wasm.Binary.Instr.localSet 783,
 Wasm.Binary.Instr.localGet 780,
 Wasm.Binary.Instr.localSet 784,
 Wasm.Binary.Instr.localGet 781,
 Wasm.Binary.Instr.localGet 782,
 Wasm.Binary.Instr.localGet 783] ++ body74Tail1936), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1920 : List Instr := ([Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 780,
 Wasm.Binary.Instr.localSet 779,
 Wasm.Binary.Instr.localSet 778,
 Wasm.Binary.Instr.localSet 777,
 Wasm.Binary.Instr.localGet 777,
 Wasm.Binary.Instr.localSet 781,
 Wasm.Binary.Instr.localGet 778] ++ body74Tail1928)

@[cbv_eval] theorem sequence74_tail1920 :
    instructionSequenceAt 3256 false { bytes := artifactBytes, pos := 15126, limit := 15177 } =
      .ok ((body74Tail1920, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.call 17,
 Wasm.Binary.Instr.localSet 780,
 Wasm.Binary.Instr.localSet 779,
 Wasm.Binary.Instr.localSet 778,
 Wasm.Binary.Instr.localSet 777,
 Wasm.Binary.Instr.localGet 777,
 Wasm.Binary.Instr.localSet 781,
 Wasm.Binary.Instr.localGet 778] ++ body74Tail1928), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1912 : List Instr := ([Wasm.Binary.Instr.localSet 776,
 Wasm.Binary.Instr.localGet 769,
 Wasm.Binary.Instr.localGet 770,
 Wasm.Binary.Instr.localGet 772,
 Wasm.Binary.Instr.localGet 773,
 Wasm.Binary.Instr.localGet 774,
 Wasm.Binary.Instr.localGet 775,
 Wasm.Binary.Instr.localGet 776] ++ body74Tail1920)

@[cbv_eval] theorem sequence74_tail1912 :
    instructionSequenceAt 3264 false { bytes := artifactBytes, pos := 15102, limit := 15177 } =
      .ok ((body74Tail1912, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 776,
 Wasm.Binary.Instr.localGet 769,
 Wasm.Binary.Instr.localGet 770,
 Wasm.Binary.Instr.localGet 772,
 Wasm.Binary.Instr.localGet 773,
 Wasm.Binary.Instr.localGet 774,
 Wasm.Binary.Instr.localGet 775,
 Wasm.Binary.Instr.localGet 776] ++ body74Tail1920), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1904 : List Instr := ([Wasm.Binary.Instr.localSet 772,
 Wasm.Binary.Instr.localGet 765,
 Wasm.Binary.Instr.localSet 773,
 Wasm.Binary.Instr.localGet 766,
 Wasm.Binary.Instr.localSet 774,
 Wasm.Binary.Instr.localGet 767,
 Wasm.Binary.Instr.localSet 775,
 Wasm.Binary.Instr.localGet 768] ++ body74Tail1912)

@[cbv_eval] theorem sequence74_tail1904 :
    instructionSequenceAt 3272 false { bytes := artifactBytes, pos := 15078, limit := 15177 } =
      .ok ((body74Tail1904, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 772,
 Wasm.Binary.Instr.localGet 765,
 Wasm.Binary.Instr.localSet 773,
 Wasm.Binary.Instr.localGet 766,
 Wasm.Binary.Instr.localSet 774,
 Wasm.Binary.Instr.localGet 767,
 Wasm.Binary.Instr.localSet 775,
 Wasm.Binary.Instr.localGet 768] ++ body74Tail1912), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1896 : List Instr := ([Wasm.Binary.Instr.localSet 768,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 769,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 770,
 Wasm.Binary.Instr.call 73,
 Wasm.Binary.Instr.localSet 771,
 Wasm.Binary.Instr.localGet 771] ++ body74Tail1904)

@[cbv_eval] theorem sequence74_tail1896 :
    instructionSequenceAt 3280 false { bytes := artifactBytes, pos := 15057, limit := 15177 } =
      .ok ((body74Tail1896, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 768,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 769,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 770,
 Wasm.Binary.Instr.call 73,
 Wasm.Binary.Instr.localSet 771,
 Wasm.Binary.Instr.localGet 771] ++ body74Tail1904), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1888 : List Instr := ([Wasm.Binary.Instr.localSet 764,
 Wasm.Binary.Instr.localSet 763,
 Wasm.Binary.Instr.localSet 762,
 Wasm.Binary.Instr.localSet 761,
 Wasm.Binary.Instr.localGet 764,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64] ++ body74Tail1896)

@[cbv_eval] theorem sequence74_tail1888 :
    instructionSequenceAt 3288 false { bytes := artifactBytes, pos := 15039, limit := 15177 } =
      .ok ((body74Tail1888, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 764,
 Wasm.Binary.Instr.localSet 763,
 Wasm.Binary.Instr.localSet 762,
 Wasm.Binary.Instr.localSet 761,
 Wasm.Binary.Instr.localGet 764,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64] ++ body74Tail1896), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1880 : List Instr := ([Wasm.Binary.Instr.localGet 754,
 Wasm.Binary.Instr.localGet 755,
 Wasm.Binary.Instr.localGet 756,
 Wasm.Binary.Instr.localGet 757,
 Wasm.Binary.Instr.localGet 758,
 Wasm.Binary.Instr.localGet 759,
 Wasm.Binary.Instr.localGet 760,
 Wasm.Binary.Instr.call 72] ++ body74Tail1888)

@[cbv_eval] theorem sequence74_tail1880 :
    instructionSequenceAt 3296 false { bytes := artifactBytes, pos := 15016, limit := 15177 } =
      .ok ((body74Tail1880, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 754,
 Wasm.Binary.Instr.localGet 755,
 Wasm.Binary.Instr.localGet 756,
 Wasm.Binary.Instr.localGet 757,
 Wasm.Binary.Instr.localGet 758,
 Wasm.Binary.Instr.localGet 759,
 Wasm.Binary.Instr.localGet 760,
 Wasm.Binary.Instr.call 72] ++ body74Tail1888), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1872 : List Instr := ([Wasm.Binary.Instr.localSet 758,
 Wasm.Binary.Instr.localGet 707,
 Wasm.Binary.Instr.localSet 759,
 Wasm.Binary.Instr.localGet 708,
 Wasm.Binary.Instr.localSet 760,
 Wasm.Binary.Instr.localGet 751,
 Wasm.Binary.Instr.localGet 752,
 Wasm.Binary.Instr.localGet 753] ++ body74Tail1880)

@[cbv_eval] theorem sequence74_tail1872 :
    instructionSequenceAt 3304 false { bytes := artifactBytes, pos := 14992, limit := 15177 } =
      .ok ((body74Tail1872, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 758,
 Wasm.Binary.Instr.localGet 707,
 Wasm.Binary.Instr.localSet 759,
 Wasm.Binary.Instr.localGet 708,
 Wasm.Binary.Instr.localSet 760,
 Wasm.Binary.Instr.localGet 751,
 Wasm.Binary.Instr.localGet 752,
 Wasm.Binary.Instr.localGet 753] ++ body74Tail1880), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1864 : List Instr := ([Wasm.Binary.Instr.localSet 754,
 Wasm.Binary.Instr.localGet 703,
 Wasm.Binary.Instr.localSet 755,
 Wasm.Binary.Instr.localGet 704,
 Wasm.Binary.Instr.localSet 756,
 Wasm.Binary.Instr.localGet 705,
 Wasm.Binary.Instr.localSet 757,
 Wasm.Binary.Instr.localGet 706] ++ body74Tail1872)

@[cbv_eval] theorem sequence74_tail1864 :
    instructionSequenceAt 3312 false { bytes := artifactBytes, pos := 14968, limit := 15177 } =
      .ok ((body74Tail1864, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 754,
 Wasm.Binary.Instr.localGet 703,
 Wasm.Binary.Instr.localSet 755,
 Wasm.Binary.Instr.localGet 704,
 Wasm.Binary.Instr.localSet 756,
 Wasm.Binary.Instr.localGet 705,
 Wasm.Binary.Instr.localSet 757,
 Wasm.Binary.Instr.localGet 706] ++ body74Tail1872), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1856 : List Instr := ([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 751,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 752,
 Wasm.Binary.Instr.localGet 701,
 Wasm.Binary.Instr.localSet 753,
 Wasm.Binary.Instr.localGet 702] ++ body74Tail1864)

@[cbv_eval] theorem sequence74_tail1856 :
    instructionSequenceAt 3320 false { bytes := artifactBytes, pos := 14948, limit := 15177 } =
      .ok ((body74Tail1856, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.i64Const 0,
 Wasm.Binary.Instr.localSet 751,
 Wasm.Binary.Instr.localGet 0,
 Wasm.Binary.Instr.localSet 752,
 Wasm.Binary.Instr.localGet 701,
 Wasm.Binary.Instr.localSet 753,
 Wasm.Binary.Instr.localGet 702] ++ body74Tail1864), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1848 : List Instr := ([Wasm.Binary.Instr.localSet 748,
 Wasm.Binary.Instr.localSet 747,
 Wasm.Binary.Instr.localGet 749,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 767,
 Wasm.Binary.Instr.localGet 424] ++ body74Tail1856)

@[cbv_eval] theorem sequence74_tail1848 :
    instructionSequenceAt 3328 false { bytes := artifactBytes, pos := 14930, limit := 15177 } =
      .ok ((body74Tail1848, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 748,
 Wasm.Binary.Instr.localSet 747,
 Wasm.Binary.Instr.localGet 749,
 Wasm.Binary.Instr.f64ReinterpretI64,
 Wasm.Binary.Instr.f64Add,
 Wasm.Binary.Instr.i64ReinterpretF64,
 Wasm.Binary.Instr.localSet 767,
 Wasm.Binary.Instr.localGet 424] ++ body74Tail1856), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1840 : List Instr := ([Wasm.Binary.Instr.localGet 742,
 Wasm.Binary.Instr.localGet 743,
 Wasm.Binary.Instr.localGet 744,
 Wasm.Binary.Instr.localGet 745,
 Wasm.Binary.Instr.localGet 746,
 Wasm.Binary.Instr.call 72,
 Wasm.Binary.Instr.localSet 750,
 Wasm.Binary.Instr.localSet 749] ++ body74Tail1848)

@[cbv_eval] theorem sequence74_tail1840 :
    instructionSequenceAt 3336 false { bytes := artifactBytes, pos := 14907, limit := 15177 } =
      .ok ((body74Tail1840, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localGet 742,
 Wasm.Binary.Instr.localGet 743,
 Wasm.Binary.Instr.localGet 744,
 Wasm.Binary.Instr.localGet 745,
 Wasm.Binary.Instr.localGet 746,
 Wasm.Binary.Instr.call 72,
 Wasm.Binary.Instr.localSet 750,
 Wasm.Binary.Instr.localSet 749] ++ body74Tail1848), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1832 : List Instr := ([Wasm.Binary.Instr.localSet 745,
 Wasm.Binary.Instr.localGet 708,
 Wasm.Binary.Instr.localSet 746,
 Wasm.Binary.Instr.localGet 737,
 Wasm.Binary.Instr.localGet 738,
 Wasm.Binary.Instr.localGet 739,
 Wasm.Binary.Instr.localGet 740,
 Wasm.Binary.Instr.localGet 741] ++ body74Tail1840)

@[cbv_eval] theorem sequence74_tail1832 :
    instructionSequenceAt 3344 false { bytes := artifactBytes, pos := 14883, limit := 15177 } =
      .ok ((body74Tail1832, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 745,
 Wasm.Binary.Instr.localGet 708,
 Wasm.Binary.Instr.localSet 746,
 Wasm.Binary.Instr.localGet 737,
 Wasm.Binary.Instr.localGet 738,
 Wasm.Binary.Instr.localGet 739,
 Wasm.Binary.Instr.localGet 740,
 Wasm.Binary.Instr.localGet 741] ++ body74Tail1840), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

@[cbv_opaque] def body74Tail1824 : List Instr := ([Wasm.Binary.Instr.localSet 741,
 Wasm.Binary.Instr.localGet 704,
 Wasm.Binary.Instr.localSet 742,
 Wasm.Binary.Instr.localGet 705,
 Wasm.Binary.Instr.localSet 743,
 Wasm.Binary.Instr.localGet 706,
 Wasm.Binary.Instr.localSet 744,
 Wasm.Binary.Instr.localGet 707] ++ body74Tail1832)

@[cbv_eval] theorem sequence74_tail1824 :
    instructionSequenceAt 3352 false { bytes := artifactBytes, pos := 14859, limit := 15177 } =
      .ok ((body74Tail1824, .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) := by
  change _ = (Except.ok ((([Wasm.Binary.Instr.localSet 741,
 Wasm.Binary.Instr.localGet 704,
 Wasm.Binary.Instr.localSet 742,
 Wasm.Binary.Instr.localGet 705,
 Wasm.Binary.Instr.localSet 743,
 Wasm.Binary.Instr.localGet 706,
 Wasm.Binary.Instr.localSet 744,
 Wasm.Binary.Instr.localGet 707] ++ body74Tail1832), .end), { bytes := artifactBytes, pos := 15177, limit := 15177 }) : Except Error ((List Instr × Terminator) × Cursor))
  cbv

end Project.TinyGpt2Hidden.Artifact
