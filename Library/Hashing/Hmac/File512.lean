import Library.Hashing.Hmac.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/hmac_sha512.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Hmac/File512.lean`: the file holds
`encode compiled512.module`, which `compiled512.encoded` states as literal bytes, so it decodes to
the module of `hmacSha512_module` and of `hmacSha512_call`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.Hmac.File512

open Library.Hashing.Hmac

set_option maxRecDepth 100000 in
/-- `build/verified/hmac_sha512.wasm` holds `encode compiled512.module`. -/
theorem hmacSha512_file :
    Wasm.Encoding.encode compiled512.module =
      .ok (binary_file% "../../../build/verified/hmac_sha512.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding compiled512.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/hmac_sha512.wasm` decodes to the module of `hmacSha512_module`. -/
theorem hmacSha512_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../build/verified/hmac_sha512.wasm") =
      .ok compiled512.module := by
  obtain ⟨⟨bytes, henc, hdec⟩, _⟩ := hmacSha512_module
  have h : binary_file% "../../../build/verified/hmac_sha512.wasm" = bytes :=
    Except.ok.inj (hmacSha512_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms hmacSha512_file
#print axioms hmacSha512_file_decode

end Library.Hashing.Hmac.File512
