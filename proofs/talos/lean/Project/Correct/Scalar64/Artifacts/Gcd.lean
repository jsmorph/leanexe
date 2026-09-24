import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Gcd

namespace Project.Correct.Scalar64.Pilots
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def gcdBytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 126, 126, 1, 126, 3, 2, 1, 0, 7, 7, 1, 3, 103, 99, 100, 0, 0, 10, 58, 1, 56, 1, 3, 126, 2, 64, 3, 64, 32, 1, 66, 0, 82, 69, 13, 1, 32, 0, 33, 3, 32, 1, 33, 4, 32, 4, 66, 0, 81, 4, 126, 32, 3, 5, 32, 3, 32, 4, 130, 11, 33, 2, 32, 1, 33, 0, 32, 2, 33, 1, 12, 0, 11, 11, 32, 0, 11]
private def gcdRaw : RawModule := { sections := [Wasm.Binary.SectionId.type,                Wasm.Binary.SectionId.function,                Wasm.Binary.SectionId.export,                Wasm.Binary.SectionId.code],   types := [{ params := [Wasm.Binary.ValType.i64, Wasm.Binary.ValType.i64], results := [Wasm.Binary.ValType.i64] }],   functionTypeIndices := [0],   memories := [],   globals := [],   exports := [{ name := { bytes := [103, 99, 100], text := "gcd" }, desc := Wasm.Binary.ExportDesc.func 0 }],   codes := [{ locals := [{ count := 3, type := Wasm.Binary.ValType.i64 }],               body := [Wasm.Binary.Instr.block                          (Wasm.Binary.BlockType.empty)                          [Wasm.Binary.Instr.loop                             (Wasm.Binary.BlockType.empty)                             [Wasm.Binary.Instr.localGet 1,                              Wasm.Binary.Instr.i64Const 0,                              Wasm.Binary.Instr.i64Ne,                              Wasm.Binary.Instr.i32Eqz,                              Wasm.Binary.Instr.brIf 1,                              Wasm.Binary.Instr.localGet 0,                              Wasm.Binary.Instr.localSet 3,                              Wasm.Binary.Instr.localGet 1,                              Wasm.Binary.Instr.localSet 4,                              Wasm.Binary.Instr.localGet 4,                              Wasm.Binary.Instr.i64Const 0,                              Wasm.Binary.Instr.i64Eq,                              Wasm.Binary.Instr.iff                                (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))                                [Wasm.Binary.Instr.localGet 3]                                (some [Wasm.Binary.Instr.localGet 3,                                  Wasm.Binary.Instr.localGet 4,                                  Wasm.Binary.Instr.i64RemU]),                              Wasm.Binary.Instr.localSet 2,                              Wasm.Binary.Instr.localGet 1,                              Wasm.Binary.Instr.localSet 0,                              Wasm.Binary.Instr.localGet 2,                              Wasm.Binary.Instr.localSet 1,                              Wasm.Binary.Instr.br 0]],                        Wasm.Binary.Instr.localGet 0] }] }
private theorem gcdDecoded : decode gcdBytes = .ok gcdRaw := by cbv
private theorem gcdValidated : Validator.validateRaw gcdRaw = .ok () := by rfl
private theorem gcdTranslated : Translation.module gcdRaw = gcdCertificate.module := by rfl

theorem gcdClosed : Artifact gcdCertificate gcdBytes :=
  Artifact.of_parts _ gcdDecoded gcdValidated gcdTranslated

#print axioms gcdClosed
end Project.Correct.Scalar64.Pilots
