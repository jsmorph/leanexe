import Library.Numerics.Float64.Tgamma.TgammaBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tgamma.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/TgammaFile.lean`: the file holds
`encode Tgamma.compiled.module`, which `Tgamma.compiled.encoded` states as literal bytes, so it
decodes to the module of `TgammaBytes.tgamma_bytes_accuracy`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Numerics.Float64.Tgamma.TgammaFile

set_option maxRecDepth 100000 in
/-- `build/verified/tgamma.wasm` holds `encode Tgamma.compiled.module`. -/
theorem tgamma_file :
    Wasm.Encoding.encode Tgamma.compiled.module =
      .ok (binary_file% "../../../../build/verified/tgamma.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding Tgamma.compiled.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/tgamma.wasm` decodes to the module of
`TgammaBytes.tgamma_bytes_accuracy`. -/
theorem tgamma_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/tgamma.wasm") =
      .ok Tgamma.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := TgammaBytes.tgamma_bytes_accuracy
  have h : binary_file% "../../../../build/verified/tgamma.wasm" = bytes :=
    Except.ok.inj (tgamma_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms tgamma_file
#print axioms tgamma_file_decode

end Library.Numerics.Float64.Tgamma.TgammaFile
