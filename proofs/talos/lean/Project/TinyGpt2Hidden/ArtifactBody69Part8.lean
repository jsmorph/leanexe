import Project.TinyGpt2Hidden.ArtifactBody69Part7

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_256_t_tail0 :
    instructionSequenceAt 708 true { bytes := artifactBytes, pos := 9136, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 31,
 Wasm.Binary.Instr.localGet 32,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Mul,
 Wasm.Binary.Instr.i64Const 1,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i64Const 8,
 Wasm.Binary.Instr.i64Mul,
 Wasm.Binary.Instr.i64Add,
 Wasm.Binary.Instr.i32WrapI64,
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 9155, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_256_e_tail1 :
    instructionSequenceAt 707 false { bytes := artifactBytes, pos := 9156, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9157, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_256_e_tail0 :
    instructionSequenceAt 708 false { bytes := artifactBytes, pos := 9155, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .end), { bytes := artifactBytes, pos := 9157, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_269_t_tail1 :
    instructionSequenceAt 694 true { bytes := artifactBytes, pos := 9184, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9185, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_269_t_tail0 :
    instructionSequenceAt 695 true { bytes := artifactBytes, pos := 9182, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const 0], .otherwise), { bytes := artifactBytes, pos := 9185, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_269_e_tail6 :
    instructionSequenceAt 689 false { bytes := artifactBytes, pos := 9203, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9204, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_269_e_tail0 :
    instructionSequenceAt 695 false { bytes := artifactBytes, pos := 9185, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Const (-1),
 Wasm.Binary.Instr.localGet 40,
 Wasm.Binary.Instr.i64DivU,
 Wasm.Binary.Instr.localGet 39,
 Wasm.Binary.Instr.i64LtU,
 Wasm.Binary.Instr.iff
   (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))
   [Wasm.Binary.Instr.unreachable]
   (some [Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul])], .end), { bytes := artifactBytes, pos := 9204, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_277_t_tail1 :
    instructionSequenceAt 686 true { bytes := artifactBytes, pos := 9219, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9220, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_277_t_tail0 :
    instructionSequenceAt 687 true { bytes := artifactBytes, pos := 9218, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 9220, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_277_e_tail1 :
    instructionSequenceAt 686 false { bytes := artifactBytes, pos := 9222, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9223, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_277_e_tail0 :
    instructionSequenceAt 687 false { bytes := artifactBytes, pos := 9220, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 38], .end), { bytes := artifactBytes, pos := 9223, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_287_t_tail1 :
    instructionSequenceAt 676 true { bytes := artifactBytes, pos := 9242, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9243, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_287_t_tail0 :
    instructionSequenceAt 677 true { bytes := artifactBytes, pos := 9241, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 9243, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_287_e_tail1 :
    instructionSequenceAt 676 false { bytes := artifactBytes, pos := 9245, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9246, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_287_e_tail0 :
    instructionSequenceAt 677 false { bytes := artifactBytes, pos := 9243, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 35], .end), { bytes := artifactBytes, pos := 9246, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_294_t_tail11 :
    instructionSequenceAt 659 true { bytes := artifactBytes, pos := 9277, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9278, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
