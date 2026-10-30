import Library.Hashing.Sha3.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sha3.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Sha3/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of the call theorems of `Library.Hashing.Sha3.Bytes`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.Sha3.File

file_theorems sha3 compiled "../../../build/verified/sha3.wasm" from compiled.bytes

end Library.Hashing.Sha3.File
