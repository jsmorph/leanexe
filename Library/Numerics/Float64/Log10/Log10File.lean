import Library.Numerics.Float64.Log10.Log10Theorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/log10.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/Log10File.lean`: the file holds
`encode Log10.compiled.module`, so it decodes to the module of `Log10Theorem.log10_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Log10.Log10File

set_option maxRecDepth 100000 in
/-- `build/verified/log10.wasm` holds `encode Log10.compiled.module`. -/
theorem log10_file :
    Wasm.Encoding.encode Log10.compiled.module =
      .ok (binary_file% "../../../../build/verified/log10.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/log10.wasm` decodes to the module of `Log10Theorem.log10_bytes_accuracy`. -/
theorem log10_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/log10.wasm") =
      .ok Log10.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := Log10Theorem.log10_bytes_accuracy
  have h : binary_file% "../../../../build/verified/log10.wasm" = bytes :=
    Except.ok.inj (log10_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms log10_file
#print axioms log10_file_decode

end Library.Numerics.Float64.Log10.Log10File
