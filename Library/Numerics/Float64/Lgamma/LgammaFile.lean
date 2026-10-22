import Library.Numerics.Float64.Lgamma.LgammaBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/lgamma.wasm`, with
`tools/leanrun --timeout 10m lake env lean Verified/Examples/LgammaFile.lean`: the file holds
`encode Lgamma.compiled.module`, which `Lgamma.compiled.encoded` states as literal bytes, so it
decodes to the module of `LgammaBytes.lgamma_bytes_accuracy`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Numerics.Float64.Lgamma.LgammaFile

set_option maxRecDepth 100000 in
/-- `build/verified/lgamma.wasm` holds `encode Lgamma.compiled.module`. -/
theorem lgamma_file :
    Wasm.Encoding.encode Lgamma.compiled.module =
      .ok (binary_file% "../../../../build/verified/lgamma.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding Lgamma.compiled.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/lgamma.wasm` decodes to the module of
`LgammaBytes.lgamma_bytes_accuracy`. -/
theorem lgamma_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/lgamma.wasm") =
      .ok Lgamma.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := LgammaBytes.lgamma_bytes_accuracy
  have h : binary_file% "../../../../build/verified/lgamma.wasm" = bytes :=
    Except.ok.inj (lgamma_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms lgamma_file
#print axioms lgamma_file_decode

end Library.Numerics.Float64.Lgamma.LgammaFile
