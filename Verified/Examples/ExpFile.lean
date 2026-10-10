import Verified.Examples.ExpTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/exp.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/ExpFile.lean`: the file holds
`encode Exp.compiled.module`, so it decodes to the module of `ExpTheorem.exp_bytes_accuracy`. -/

namespace Verified.Examples.ExpFile

set_option maxRecDepth 100000 in
/-- `build/verified/exp.wasm` holds `encode Exp.compiled.module`. -/
theorem exp_file :
    Wasm.Encoding.encode Exp.compiled.module =
      .ok (binary_file% "../../build/verified/exp.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/exp.wasm` decodes to the module of `ExpTheorem.exp_bytes_accuracy`. -/
theorem exp_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/exp.wasm") =
      .ok Exp.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := ExpTheorem.exp_bytes_accuracy
  have h : binary_file% "../../build/verified/exp.wasm" = bytes :=
    Except.ok.inj (exp_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms exp_file
#print axioms exp_file_decode

end Verified.Examples.ExpFile
