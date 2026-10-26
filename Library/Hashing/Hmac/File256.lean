import Library.Hashing.Hmac.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/hmac_sha256.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Hmac/File256.lean`: the file holds
`encode compiled256.module`, which `compiled256.encoded` states as literal bytes, so it decodes to
the module of `hmacSha256_module` and of `hmacSha256_call`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.Hmac.File256

open Library.Hashing.Hmac

set_option maxRecDepth 100000 in
/-- `build/verified/hmac_sha256.wasm` holds `encode compiled256.module`. -/
theorem hmacSha256_file :
    Wasm.Encoding.encode compiled256.module =
      .ok (binary_file% "../../../build/verified/hmac_sha256.wasm") :=
  LeanExe.Pipeline.encode_eq_of_encoding compiled256.encoded.1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `build/verified/hmac_sha256.wasm` decodes to the module of `hmacSha256_module`. -/
theorem hmacSha256_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../build/verified/hmac_sha256.wasm") =
      .ok compiled256.module := by
  obtain ⟨⟨bytes, henc, hdec⟩, _⟩ := hmacSha256_module
  have h : binary_file% "../../../build/verified/hmac_sha256.wasm" = bytes :=
    Except.ok.inj (hmacSha256_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms hmacSha256_file
#print axioms hmacSha256_file_decode

end Library.Hashing.Hmac.File256
