import Verified.Examples.TanhBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tanh.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/TanhFile.lean`: the file holds
`encode Tanh.compiled.module`, so it decodes to the module of `TanhBytes.tanh_module_accuracy`,
which states the byte theorems of both `expm1` and `tanh`. -/

namespace Verified.Examples.TanhFile

set_option maxRecDepth 100000 in
/-- `build/verified/tanh.wasm` holds `encode Tanh.compiled.module`. -/
theorem tanh_file :
    Wasm.Encoding.encode Tanh.compiled.module =
      .ok (binary_file% "../../build/verified/tanh.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/tanh.wasm` decodes to the module of `TanhBytes.tanh_module_accuracy`. -/
theorem tanh_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/tanh.wasm") =
      .ok Tanh.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _⟩ := TanhBytes.tanh_module_accuracy
  have h : binary_file% "../../build/verified/tanh.wasm" = bytes :=
    Except.ok.inj (tanh_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms tanh_file
#print axioms tanh_file_decode

end Verified.Examples.TanhFile
