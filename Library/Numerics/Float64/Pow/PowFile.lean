import Library.Numerics.Float64.Pow.PowBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/pow.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/PowFile.lean`: the file holds
`encode Pow.compiled.module`, so it decodes to the module of `PowBytes.pow_bytes_accuracy`.
The kernel takes its recursion limit from `maxRecDepth`, and its check of the 11,156-byte literal
exceeds the default limit, so both theorems raise it. -/

namespace Library.Numerics.Float64.Pow.PowFile

set_option maxRecDepth 100000 in
/-- `build/verified/pow.wasm` holds `encode Pow.compiled.module`. -/
theorem pow_file :
    Wasm.Encoding.encode Pow.compiled.module =
      .ok (binary_file% "../../../../build/verified/pow.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/pow.wasm` decodes to the module of `PowBytes.pow_bytes_accuracy`. -/
theorem pow_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/pow.wasm") =
      .ok Pow.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := PowBytes.pow_bytes_accuracy
  have h : binary_file% "../../../../build/verified/pow.wasm" = bytes :=
    Except.ok.inj (pow_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms pow_file
#print axioms pow_file_decode

end Library.Numerics.Float64.Pow.PowFile
