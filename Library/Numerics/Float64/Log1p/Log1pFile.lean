import Library.Numerics.Float64.Log1p.Log1pBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/log1p.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Log1p/Log1pFile.lean`: the file holds
`encode Log1p.compiled.module`, so it decodes to the module of
`Log1pBytes.log1p_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Log1p.Log1pFile

set_option maxRecDepth 100000 in
/-- `build/verified/log1p.wasm` holds `encode Log1p.compiled.module`. -/
theorem log1p_file :
    Wasm.Encoding.encode Log1p.compiled.module =
      .ok (binary_file% "../../../../build/verified/log1p.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/log1p.wasm` decodes to the module of `Log1pBytes.log1p_bytes_accuracy`. -/
theorem log1p_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/log1p.wasm") =
      .ok Log1p.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := Log1pBytes.log1p_bytes_accuracy
  have h : binary_file% "../../../../build/verified/log1p.wasm" = bytes :=
    Except.ok.inj (log1p_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms log1p_file
#print axioms log1p_file_decode

end Library.Numerics.Float64.Log1p.Log1pFile
