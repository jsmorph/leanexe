import Library.Numerics.Float64.Sinh.SinhBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sinh.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/SinhFile.lean`: the file holds
`encode Sinh.compiled.module`, so it decodes to the module of `SinhBytes.sinh_module_accuracy`,
which states the byte theorems of both `sinh` and `cosh`. -/

namespace Library.Numerics.Float64.Sinh.SinhFile

set_option maxRecDepth 100000 in
/-- `build/verified/sinh.wasm` holds `encode Sinh.compiled.module`. -/
theorem sinh_file :
    Wasm.Encoding.encode Sinh.compiled.module =
      .ok (binary_file% "../../../../build/verified/sinh.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/sinh.wasm` decodes to the module of `SinhBytes.sinh_module_accuracy`. -/
theorem sinh_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/sinh.wasm") =
      .ok Sinh.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _⟩ := SinhBytes.sinh_module_accuracy
  have h : binary_file% "../../../../build/verified/sinh.wasm" = bytes :=
    Except.ok.inj (sinh_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms sinh_file
#print axioms sinh_file_decode

end Library.Numerics.Float64.Sinh.SinhFile
