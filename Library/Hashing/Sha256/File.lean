import Library.Hashing.Sha256.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sha256.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Sha256/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of `sha256_module` and of the call theorems of `Library.Hashing.Sha256.Bytes`.  The file's
bytes are a term nested as deep as the file is long, which the kernel checks under a raised
`maxRecDepth`. -/

namespace Library.Hashing.Sha256.File

file_theorems sha256 compiled "../../../build/verified/sha256.wasm" from sha256_module

end Library.Hashing.Sha256.File
