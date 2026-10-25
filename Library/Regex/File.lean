import Library.Regex.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/regex.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Regex/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of the call theorem of `Library.Regex.Bytes`.  The file's bytes are a term nested as deep
as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Regex.File

set_option maxRecDepth 100000 in
/-- `build/verified/regex.wasm` holds `encode compiled.module`. -/
theorem regex_file :
    Wasm.Encoding.encode compiled.module = .ok (binary_file% "../../build/verified/regex.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding compiled.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/regex.wasm` decodes to the module of `matchWith_call`. -/
theorem regex_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/regex.wasm") =
      .ok compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  have h : binary_file% "../../build/verified/regex.wasm" = bytes :=
    Except.ok.inj (regex_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms regex_file
#print axioms regex_file_decode

end Library.Regex.File
