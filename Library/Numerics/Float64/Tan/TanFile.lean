import Library.Numerics.Float64.Tan.TanTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tan.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/TanFile.lean`: the file holds
`encode Tan.compiled.module`, so it decodes to the module of `TanTheorem.tan_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Tan.TanFile

set_option maxRecDepth 100000 in
/-- `build/verified/tan.wasm` holds `encode Tan.compiled.module`. -/
theorem tan_file :
    Wasm.Encoding.encode Tan.compiled.module =
      .ok (binary_file% "../../../../build/verified/tan.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/tan.wasm` decodes to the module of `TanTheorem.tan_bytes_accuracy`.  The
proof takes the bytes from that theorem, so its axiom report covers it. -/
theorem tan_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/tan.wasm") =
      .ok Tan.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := TanTheorem.tan_bytes_accuracy
  have h : binary_file% "../../../../build/verified/tan.wasm" = bytes :=
    Except.ok.inj (tan_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms tan_file
#print axioms tan_file_decode

end Library.Numerics.Float64.Tan.TanFile
