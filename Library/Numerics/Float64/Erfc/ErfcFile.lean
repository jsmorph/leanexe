import Library.Numerics.Float64.Erfc.ErfcBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/erfc.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Erfc/ErfcFile.lean`: the file holds
`encode Erfc.compiled.module`, which `Erfc.compiled.encoded` states as literal bytes, so it
decodes to the module of `ErfcBytes.erfc_bytes_accuracy`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Numerics.Float64.Erfc.ErfcFile

set_option maxRecDepth 100000 in
/-- `build/verified/erfc.wasm` holds `encode Erfc.compiled.module`. -/
theorem erfc_file :
    Wasm.Encoding.encode Erfc.compiled.module =
      .ok (binary_file% "../../../../build/verified/erfc.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding Erfc.compiled.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/erfc.wasm` decodes to the module of `ErfcBytes.erfc_bytes_accuracy`. -/
theorem erfc_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/erfc.wasm") =
      .ok Erfc.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := ErfcBytes.erfc_bytes_accuracy
  have h : binary_file% "../../../../build/verified/erfc.wasm" = bytes :=
    Except.ok.inj (erfc_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms erfc_file
#print axioms erfc_file_decode

end Library.Numerics.Float64.Erfc.ErfcFile
