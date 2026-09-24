import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Gcd

namespace Project.Correct.Scalar64.Pilots
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def chooseBytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 126, 126, 1, 126, 3, 2, 1, 0, 7, 10, 1, 6, 99, 104, 111, 111, 115, 101, 0, 0, 10, 23, 1, 21, 0, 32, 0, 66, 0, 81, 4, 126, 32, 1, 66, 1, 124, 5, 32, 0, 32, 1, 124, 11, 11]
private def chooseRaw : RawModule := { sections := [Wasm.Binary.SectionId.type,                Wasm.Binary.SectionId.function,                Wasm.Binary.SectionId.export,                Wasm.Binary.SectionId.code],   types := [{ params := [Wasm.Binary.ValType.i64, Wasm.Binary.ValType.i64], results := [Wasm.Binary.ValType.i64] }],   functionTypeIndices := [0],   memories := [],   globals := [],   exports := [{ name := { bytes := [99, 104, 111, 111, 115, 101], text := "choose" },                 desc := Wasm.Binary.ExportDesc.func 0 }],   codes := [{ locals := [],               body := [Wasm.Binary.Instr.localGet 0,                        Wasm.Binary.Instr.i64Const 0,                        Wasm.Binary.Instr.i64Eq,                        Wasm.Binary.Instr.iff                          (Wasm.Binary.BlockType.value (Wasm.Binary.ValType.i64))                          [Wasm.Binary.Instr.localGet 1, Wasm.Binary.Instr.i64Const 1, Wasm.Binary.Instr.i64Add]                          (some [Wasm.Binary.Instr.localGet 0,                            Wasm.Binary.Instr.localGet 1,                            Wasm.Binary.Instr.i64Add])] }] }
private theorem chooseDecoded : decode chooseBytes = .ok chooseRaw := by cbv
private theorem chooseValidated : Validator.validateRaw chooseRaw = .ok () := by rfl
private theorem chooseTranslated : Translation.module chooseRaw = chooseCertificate.module := by rfl

theorem chooseClosed : Artifact chooseCertificate chooseBytes :=
  Artifact.of_parts _ chooseDecoded chooseValidated chooseTranslated

#print axioms chooseClosed
end Project.Correct.Scalar64.Pilots
