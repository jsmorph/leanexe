import Library.Numerics.Float64.Atan.AtanBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/atan.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/AtanFile.lean`: the file holds
`encode Atan.compiled.module`, so it decodes to the module of `AtanBytes.atan_module_accuracy`,
which states the byte theorems of both `atan` and `atan2`. -/

namespace Library.Numerics.Float64.Atan.AtanFile

set_option maxRecDepth 100000 in
/-- `build/verified/atan.wasm` holds `encode Atan.compiled.module`. -/
theorem atan_file :
    Wasm.Encoding.encode Atan.compiled.module =
      .ok (binary_file% "../../../../build/verified/atan.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/atan.wasm` decodes to the module of `AtanBytes.atan_module_accuracy`. -/
theorem atan_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/atan.wasm") =
      .ok Atan.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _⟩ := AtanBytes.atan_module_accuracy
  have h : binary_file% "../../../../build/verified/atan.wasm" = bytes :=
    Except.ok.inj (atan_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms atan_file
#print axioms atan_file_decode

end Library.Numerics.Float64.Atan.AtanFile
