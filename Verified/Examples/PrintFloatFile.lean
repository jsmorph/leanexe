import Verified.Examples.PrintFloatBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `build/verified/printfloat.wasm` is written by `tools/Emit.lean`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/PrintFloatFile.lean`: the file holds
`encode PrintFloat.compiled.module`, so it decodes to the module of the four byte theorems of
`PrintFloatBytes`. -/

namespace Verified.Examples.PrintFloatFile

set_option maxRecDepth 100000 in
/-- `build/verified/printfloat.wasm` holds `encode PrintFloat.compiled.module`. -/
theorem print_file :
    Wasm.Encoding.encode PrintFloat.compiled.module =
      .ok (binary_file% "../../build/verified/printfloat.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/printfloat.wasm` decodes to the module of the printers' byte theorems. -/
theorem print_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/printfloat.wasm") =
      .ok PrintFloat.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := PrintFloatBytes.print64_bytes_accuracy
  have _h64e := PrintFloatBytes.print64Ecma_bytes_accuracy
  have _h32 := PrintFloatBytes.print32_bytes_accuracy
  have _h32e := PrintFloatBytes.print32Ecma_bytes_accuracy
  have h : binary_file% "../../build/verified/printfloat.wasm" = bytes :=
    Except.ok.inj (print_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms print_file
#print axioms print_file_decode

end Verified.Examples.PrintFloatFile
