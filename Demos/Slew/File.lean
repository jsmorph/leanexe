import Demos.Slew.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/slew.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Slew/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module whose `plan` export `compiled.plan.implements` describes.  The file's bytes are a term
nested as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Demos.Slew.File

open Demos.Slew.Verified

set_option maxRecDepth 100000 in
/-- `build/verified/slew.wasm` holds `encode compiled.module`. -/
theorem slew_file :
    Wasm.Encoding.encode compiled.module = .ok (binary_file% "../../build/verified/slew.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding compiled.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/slew.wasm` decodes to the module of `compiled.plan.implements`. -/
theorem slew_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/slew.wasm") =
      .ok compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  have h : binary_file% "../../build/verified/slew.wasm" = bytes :=
    Except.ok.inj (slew_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms slew_file
#print axioms slew_file_decode

end Demos.Slew.File
