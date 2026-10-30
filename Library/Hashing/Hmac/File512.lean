import Library.Hashing.Hmac.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/hmac_sha512.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Hmac/File512.lean`: the file holds
`encode compiled512.module`, which `compiled512.encoded` states as literal bytes, so it decodes to
the module of `hmacSha512_module` and of `hmacSha512_call`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.Hmac.File512

open Library.Hashing.Hmac

file_theorems hmacSha512 compiled512 "../../../build/verified/hmac_sha512.wasm"
  from hmacSha512_module

end Library.Hashing.Hmac.File512
