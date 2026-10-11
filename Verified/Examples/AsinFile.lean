import Verified.Examples.AsinBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/asin.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/AsinFile.lean`: the file holds
`encode Asin.compiled.module`, so it decodes to the module of
`AsinBytes.asin_module_accuracy`. -/

namespace Verified.Examples.AsinFile

set_option maxRecDepth 100000 in
/-- `build/verified/asin.wasm` holds `encode Asin.compiled.module`. -/
theorem asin_file :
    Wasm.Encoding.encode Asin.compiled.module =
      .ok (binary_file% "../../build/verified/asin.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/asin.wasm` decodes to the module of `AsinBytes.asin_module_accuracy`. -/
theorem asin_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/asin.wasm") =
      .ok Asin.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _⟩ := AsinBytes.asin_module_accuracy
  have h : binary_file% "../../build/verified/asin.wasm" = bytes :=
    Except.ok.inj (asin_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms asin_file
#print axioms asin_file_decode

end Verified.Examples.AsinFile
