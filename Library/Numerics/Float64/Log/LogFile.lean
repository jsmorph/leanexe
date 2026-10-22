import Library.Numerics.Float64.Log.LogTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/log.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/LogFile.lean`: the file holds
`encode Log.compiled.module`, so it decodes to the module of `LogTheorem.log_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Log.LogFile

set_option maxRecDepth 100000 in
/-- `build/verified/log.wasm` holds `encode Log.compiled.module`. -/
theorem log_file :
    Wasm.Encoding.encode Log.compiled.module =
      .ok (binary_file% "../../../../build/verified/log.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/log.wasm` decodes to the module of `LogTheorem.log_bytes_accuracy`. -/
theorem log_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/log.wasm") =
      .ok Log.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := LogTheorem.log_bytes_accuracy
  have h : binary_file% "../../../../build/verified/log.wasm" = bytes :=
    Except.ok.inj (log_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms log_file
#print axioms log_file_decode

end Library.Numerics.Float64.Log.LogFile
