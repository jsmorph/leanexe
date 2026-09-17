import Project.TinyGpt2Hidden.ArtifactBody69Part6

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_218_e_tail1 :
    instructionSequenceAt 745 false { bytes := artifactBytes, pos := 9033, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9034, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_218_e_tail0 :
    instructionSequenceAt 746 false { bytes := artifactBytes, pos := 9032, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 9034, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_231_t_tail1 :
    instructionSequenceAt 732 true { bytes := artifactBytes, pos := 9061, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9062, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_231_t_tail0 :
    instructionSequenceAt 733 true { bytes := artifactBytes, pos := 9059, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const 0], .otherwise), { bytes := artifactBytes, pos := 9062, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_231_e_tail6 :
    instructionSequenceAt 727 false { bytes := artifactBytes, pos := 9080, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9081, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_231_e_tail0 :
    instructionSequenceAt 733 false { bytes := artifactBytes, pos := 9062, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const (-1),
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64DivU,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])], .end), { bytes := artifactBytes, pos := 9081, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_239_t_tail1 :
    instructionSequenceAt 724 true { bytes := artifactBytes, pos := 9096, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9097, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_239_t_tail0 :
    instructionSequenceAt 725 true { bytes := artifactBytes, pos := 9095, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 9097, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_239_e_tail1 :
    instructionSequenceAt 724 false { bytes := artifactBytes, pos := 9099, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9100, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_239_e_tail0 :
    instructionSequenceAt 725 false { bytes := artifactBytes, pos := 9097, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 38], .end), { bytes := artifactBytes, pos := 9100, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_249_t_tail1 :
    instructionSequenceAt 714 true { bytes := artifactBytes, pos := 9119, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9120, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_249_t_tail0 :
    instructionSequenceAt 715 true { bytes := artifactBytes, pos := 9118, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 9120, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_249_e_tail1 :
    instructionSequenceAt 714 false { bytes := artifactBytes, pos := 9122, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9123, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_249_e_tail0 :
    instructionSequenceAt 715 false { bytes := artifactBytes, pos := 9120, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 35], .end), { bytes := artifactBytes, pos := 9123, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_256_t_tail11 :
    instructionSequenceAt 697 true { bytes := artifactBytes, pos := 9154, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9155, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_256_t_tail8 :
    instructionSequenceAt 700 true { bytes := artifactBytes, pos := 9149, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.i32WrapI64, Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 9155, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
