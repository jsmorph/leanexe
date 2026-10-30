import Library.Hashing.Crc.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/crc.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/Crc/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of the call theorems of `Library.Hashing.Crc.Bytes`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.Crc.File

file_theorems crc compiled "../../../build/verified/crc.wasm" from compiled.bytes

end Library.Hashing.Crc.File
