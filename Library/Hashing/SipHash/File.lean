import Library.Hashing.SipHash.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/siphash.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/SipHash/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of the call theorems of `Library.Hashing.SipHash.Bytes`.  The file's bytes are a term
nested as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.SipHash.File

set_option maxRecDepth 100000 in
/-- `build/verified/siphash.wasm` holds `encode compiled.module`. -/
theorem siphash_file :
    Wasm.Encoding.encode compiled.module =
      .ok (binary_file% "../../../build/verified/siphash.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding compiled.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/siphash.wasm` decodes to the module of the call theorems. -/
theorem siphash_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../build/verified/siphash.wasm") =
      .ok compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  have h : binary_file% "../../../build/verified/siphash.wasm" = bytes :=
    Except.ok.inj (siphash_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms siphash_file
#print axioms siphash_file_decode

end Library.Hashing.SipHash.File
