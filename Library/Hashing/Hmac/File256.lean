import Library.Hashing.Hmac.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/hmac_sha256.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Hmac/File256.lean`: the file holds
`encode compiled256.module`, which `compiled256.encoded` states as literal bytes, so it decodes to
the module of `hmacSha256_module` and of `hmacSha256_call`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.Hmac.File256

open Library.Hashing.Hmac

file_theorems hmacSha256 compiled256 "../../../build/verified/hmac_sha256.wasm"
  from hmacSha256_module

end Library.Hashing.Hmac.File256
