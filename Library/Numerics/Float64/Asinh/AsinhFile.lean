import Library.Numerics.Float64.Asinh.AsinhBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/asinh.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Asinh/AsinhFile.lean`: the file holds
`encode Asinh.compiled.module`, so it decodes to the module of
`AsinhBytes.asinh_module_accuracy`, which states the byte theorems of `atanh`, `asinh`, and
`acosh`. -/

namespace Library.Numerics.Float64.Asinh.AsinhFile

set_option maxRecDepth 100000 in
/-- `build/verified/asinh.wasm` holds `encode Asinh.compiled.module`. -/
theorem asinh_file :
    Wasm.Encoding.encode Asinh.compiled.module =
      .ok (binary_file% "../../../../build/verified/asinh.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/asinh.wasm` decodes to the module of `AsinhBytes.asinh_module_accuracy`. -/
theorem asinh_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/asinh.wasm") =
      .ok Asinh.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _, _⟩ := AsinhBytes.asinh_module_accuracy
  have h : binary_file% "../../../../build/verified/asinh.wasm" = bytes :=
    Except.ok.inj (asinh_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms asinh_file
#print axioms asinh_file_decode

end Library.Numerics.Float64.Asinh.AsinhFile
