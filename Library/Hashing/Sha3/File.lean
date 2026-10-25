import Library.Hashing.Sha3.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sha3.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Sha3/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of the call theorems of `Library.Hashing.Sha3.Bytes`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.Sha3.File

set_option maxRecDepth 100000 in
/-- `build/verified/sha3.wasm` holds `encode compiled.module`. -/
theorem sha3_file :
    Wasm.Encoding.encode compiled.module =
      .ok (binary_file% "../../../build/verified/sha3.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding compiled.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/sha3.wasm` decodes to the module of the call theorems. -/
theorem sha3_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../build/verified/sha3.wasm") =
      .ok compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  have h : binary_file% "../../../build/verified/sha3.wasm" = bytes :=
    Except.ok.inj (sha3_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms sha3_file
#print axioms sha3_file_decode

end Library.Hashing.Sha3.File
