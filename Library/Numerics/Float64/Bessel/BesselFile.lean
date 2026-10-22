import Library.Numerics.Float64.Bessel.BesselBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/bessel.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Bessel/BesselFile.lean`: the file holds
`encode Bessel.compiled.module`, which `Bessel.compiled.encoded` states as literal bytes, so it
decodes to the module of `BesselBytes.bessel_module_accuracy`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Numerics.Float64.Bessel.BesselFile

set_option maxRecDepth 100000 in
/-- `build/verified/bessel.wasm` holds `encode Bessel.compiled.module`. -/
theorem bessel_file :
    Wasm.Encoding.encode Bessel.compiled.module =
      .ok (binary_file% "../../../../build/verified/bessel.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding Bessel.compiled.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/bessel.wasm` decodes to the module of `BesselBytes.bessel_module_accuracy`. -/
theorem bessel_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/bessel.wasm") =
      .ok Bessel.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _⟩ := BesselBytes.bessel_module_accuracy
  have h : binary_file% "../../../../build/verified/bessel.wasm" = bytes :=
    Except.ok.inj (bessel_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms bessel_file
#print axioms bessel_file_decode

end Library.Numerics.Float64.Bessel.BesselFile
