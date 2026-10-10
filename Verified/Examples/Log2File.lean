import Verified.Examples.Log2Theorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/log2.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/Log2File.lean`: the file holds
`encode Log2.compiled.module`, so it decodes to the module of `Log2Theorem.log2_bytes_accuracy`. -/

namespace Verified.Examples.Log2File

set_option maxRecDepth 100000 in
/-- `build/verified/log2.wasm` holds `encode Log2.compiled.module`. -/
theorem log2_file :
    Wasm.Encoding.encode Log2.compiled.module =
      .ok (binary_file% "../../build/verified/log2.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/log2.wasm` decodes to the module of `Log2Theorem.log2_bytes_accuracy`. -/
theorem log2_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/log2.wasm") =
      .ok Log2.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := Log2Theorem.log2_bytes_accuracy
  have h : binary_file% "../../build/verified/log2.wasm" = bytes :=
    Except.ok.inj (log2_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms log2_file
#print axioms log2_file_decode

end Verified.Examples.Log2File
