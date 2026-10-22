import Library.Numerics.Float64.Exp2.Exp2Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/exp2.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/Exp2File.lean`: the file holds
`encode Exp2.compiled.module`, so it decodes to the module of `Exp2Bytes.exp2_module_accuracy`,
which states the byte theorems of both `exp2` and `exp10`. -/

namespace Library.Numerics.Float64.Exp2.Exp2File

set_option maxRecDepth 100000 in
/-- `build/verified/exp2.wasm` holds `encode Exp2.compiled.module`. -/
theorem exp2_file :
    Wasm.Encoding.encode Exp2.compiled.module =
      .ok (binary_file% "../../../../build/verified/exp2.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/exp2.wasm` decodes to the module of `Exp2Bytes.exp2_module_accuracy`. -/
theorem exp2_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/exp2.wasm") =
      .ok Exp2.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _⟩ := Exp2Bytes.exp2_module_accuracy
  have h : binary_file% "../../../../build/verified/exp2.wasm" = bytes :=
    Except.ok.inj (exp2_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms exp2_file
#print axioms exp2_file_decode

end Library.Numerics.Float64.Exp2.Exp2File
