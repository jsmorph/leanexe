import Project.TinyGpt2Hidden.ArtifactBody69Part0

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_231_e_5_t_tail1 :
    instructionSequenceAt 725 true { bytes := artifactBytes, pos := 9073, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9074, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_231_e_5_t_tail0 :
    instructionSequenceAt 726 true { bytes := artifactBytes, pos := 9072, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 9074, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_231_e_5_e_tail3 :
    instructionSequenceAt 723 false { bytes := artifactBytes, pos := 9079, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9080, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_231_e_5_e_tail0 :
    instructionSequenceAt 726 false { bytes := artifactBytes, pos := 9074, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul], .end), { bytes := artifactBytes, pos := 9080, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_269_e_5_t_tail1 :
    instructionSequenceAt 687 true { bytes := artifactBytes, pos := 9196, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 9197, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_269_e_5_t_tail0 :
    instructionSequenceAt 688 true { bytes := artifactBytes, pos := 9195, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 9197, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_269_e_5_e_tail3 :
    instructionSequenceAt 685 false { bytes := artifactBytes, pos := 9202, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 9203, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_269_e_5_e_tail0 :
    instructionSequenceAt 688 false { bytes := artifactBytes, pos := 9197, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul], .end), { bytes := artifactBytes, pos := 9203, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_28_t_tail1 :
    instructionSequenceAt 935 true { bytes := artifactBytes, pos := 8416, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8417, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_28_t_tail0 :
    instructionSequenceAt 936 true { bytes := artifactBytes, pos := 8415, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8417, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_28_e_tail1 :
    instructionSequenceAt 935 false { bytes := artifactBytes, pos := 8419, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8420, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_28_e_tail0 :
    instructionSequenceAt 936 false { bytes := artifactBytes, pos := 8417, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 35], .end), { bytes := artifactBytes, pos := 8420, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_35_t_tail11 :
    instructionSequenceAt 918 true { bytes := artifactBytes, pos := 8451, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8452, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_35_t_tail8 :
    instructionSequenceAt 921 true { bytes := artifactBytes, pos := 8446, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.i64Add, Wasm.Binary.Instr.i32WrapI64, Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8452, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_35_t_tail0 :
    instructionSequenceAt 929 true { bytes := artifactBytes, pos := 8433, limit := 9325 } =
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
 Wasm.Binary.Instr.i64Load { align := 3, offset := 0 }], .otherwise), { bytes := artifactBytes, pos := 8452, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_35_e_tail1 :
    instructionSequenceAt 928 false { bytes := artifactBytes, pos := 8453, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8454, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
