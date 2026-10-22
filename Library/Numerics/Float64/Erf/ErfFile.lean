import Library.Numerics.Float64.Erf.ErfTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/erf.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/ErfFile.lean`: the file holds
`encode Erf.compiled.module`, so it decodes to the module of `ErfTheorem.erf_module_accuracy`,
which depends on every byte theorem of the module. -/

namespace Library.Numerics.Float64.Erf.ErfFile

set_option maxRecDepth 100000 in
/-- `build/verified/erf.wasm` holds `encode Erf.compiled.module`. -/
theorem erf_file :
    Wasm.Encoding.encode Erf.compiled.module =
      .ok (binary_file% "../../../../build/verified/erf.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/erf.wasm` decodes to the module of `ErfTheorem.erf_module_accuracy`. -/
theorem erf_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/erf.wasm") =
      .ok Erf.compiled.module := by
  obtain ⟨bytes, henc, hdec⟩ := ErfTheorem.erf_module_accuracy
  have h : binary_file% "../../../../build/verified/erf.wasm" = bytes :=
    Except.ok.inj (erf_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms erf_file
#print axioms erf_file_decode

end Library.Numerics.Float64.Erf.ErfFile
