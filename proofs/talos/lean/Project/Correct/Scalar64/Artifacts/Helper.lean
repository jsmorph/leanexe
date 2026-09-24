import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Gcd

namespace Project.Correct.Scalar64.Pilots
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def helperBytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 13, 2, 96, 2, 126, 126, 1, 126, 96, 2, 126, 126, 1, 126, 3, 3, 2, 0, 1, 7, 10, 1, 6, 104, 101, 108, 112, 101, 114, 0, 1, 10, 36, 2, 10, 0, 32, 0, 66, 5, 126, 32, 1, 124, 11, 23, 1, 1, 126, 32, 0, 66, 1, 124, 32, 1, 66, 2, 126, 16, 0, 33, 2, 32, 2, 32, 0, 124, 11]
private def helperRaw : RawModule := { sections := [Wasm.Binary.SectionId.type,                Wasm.Binary.SectionId.function,                Wasm.Binary.SectionId.export,                Wasm.Binary.SectionId.code],   types := [{ params := [Wasm.Binary.ValType.i64, Wasm.Binary.ValType.i64], results := [Wasm.Binary.ValType.i64] },             { params := [Wasm.Binary.ValType.i64, Wasm.Binary.ValType.i64], results := [Wasm.Binary.ValType.i64] }],   functionTypeIndices := [0, 1],   memories := [],   globals := [],   exports := [{ name := { bytes := [104, 101, 108, 112, 101, 114], text := "helper" },                 desc := Wasm.Binary.ExportDesc.func 1 }],   codes := [{ locals := [],               body := [Wasm.Binary.Instr.localGet 0,                        Wasm.Binary.Instr.i64Const 5,                        Wasm.Binary.Instr.i64Mul,                        Wasm.Binary.Instr.localGet 1,                        Wasm.Binary.Instr.i64Add] },             { locals := [{ count := 1, type := Wasm.Binary.ValType.i64 }],               body := [Wasm.Binary.Instr.localGet 0,                        Wasm.Binary.Instr.i64Const 1,                        Wasm.Binary.Instr.i64Add,                        Wasm.Binary.Instr.localGet 1,                        Wasm.Binary.Instr.i64Const 2,                        Wasm.Binary.Instr.i64Mul,                        Wasm.Binary.Instr.call 0,                        Wasm.Binary.Instr.localSet 2,                        Wasm.Binary.Instr.localGet 2,                        Wasm.Binary.Instr.localGet 0,                        Wasm.Binary.Instr.i64Add] }] }
private theorem helperDecoded : decode helperBytes = .ok helperRaw := by cbv
private theorem helperValidated : Validator.validateRaw helperRaw = .ok () := by rfl
private theorem helperTranslated : Translation.module helperRaw = helperCertificate.module := by rfl

theorem helperClosed : Artifact helperCertificate helperBytes :=
  Artifact.of_parts _ helperDecoded helperValidated helperTranslated

#print axioms helperClosed
end Project.Correct.Scalar64.Pilots
