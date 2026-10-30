import Library.Hashing.Sha512.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sha512.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Sha512/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of `sha512_module` and of the call theorems of `Library.Hashing.Sha512.Bytes`.  The file's
bytes are a term nested as deep as the file is long, which the kernel checks under a raised
`maxRecDepth`. -/

namespace Library.Hashing.Sha512.File

file_theorems sha512 compiled "../../../build/verified/sha512.wasm" from sha512_module

end Library.Hashing.Sha512.File
