import Verified.Examples.ParseFloatBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `build/verified/parsefloat.wasm` is written by `tools/Emit.lean`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/ParseFloatFile.lean`: the file holds
`encode ParseFloat.compiled.module`, so it decodes to the module of
`ParseFloatBytes.parse64_bytes_accuracy` and `ParseFloatBytes.parse32_bytes_accuracy`. -/

namespace Verified.Examples.ParseFloatFile

set_option maxRecDepth 100000 in
/-- `build/verified/parsefloat.wasm` holds `encode ParseFloat.compiled.module`. -/
theorem parse_file :
    Wasm.Encoding.encode ParseFloat.compiled.module =
      .ok (binary_file% "../../build/verified/parsefloat.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/parsefloat.wasm` decodes to the module of the parsers' byte theorems. -/
theorem parse_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/parsefloat.wasm") =
      .ok ParseFloat.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := ParseFloatBytes.parse64_bytes_accuracy
  have _h32 := ParseFloatBytes.parse32_bytes_accuracy
  have h : binary_file% "../../build/verified/parsefloat.wasm" = bytes :=
    Except.ok.inj (parse_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms parse_file
#print axioms parse_file_decode

end Verified.Examples.ParseFloatFile
