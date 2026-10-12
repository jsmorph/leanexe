import Verified.Examples.SinpiTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sinpi.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/SinpiFile.lean`: the file holds
`encode Sinpi.compiled.module`, so it decodes to the module of
`SinpiTheorem.sinpi_bytes_accuracy`, `SinpiTheorem.cospi_bytes_accuracy`, and
`SinpiTheorem.tanpi_bytes_accuracy`. -/

namespace Verified.Examples.SinpiFile

set_option maxRecDepth 100000 in
/-- `build/verified/sinpi.wasm` holds `encode Sinpi.compiled.module`. -/
theorem sinpi_file :
    Wasm.Encoding.encode Sinpi.compiled.module =
      .ok (binary_file% "../../build/verified/sinpi.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/sinpi.wasm` decodes to the module of the three byte theorems.  The proof
takes the bytes from the three theorems together, so its axiom report covers all three. -/
theorem sinpi_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/sinpi.wasm") =
      .ok Sinpi.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _, _⟩ :=
    And.intro SinpiTheorem.sinpi_bytes_accuracy
      (And.intro SinpiTheorem.cospi_bytes_accuracy SinpiTheorem.tanpi_bytes_accuracy)
  have h : binary_file% "../../build/verified/sinpi.wasm" = bytes :=
    Except.ok.inj (sinpi_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms sinpi_file
#print axioms sinpi_file_decode

end Verified.Examples.SinpiFile
