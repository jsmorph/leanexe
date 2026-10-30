import Library.Hashing.SipHash.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/siphash.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Hashing/SipHash/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of the call theorems of `Library.Hashing.SipHash.Bytes`.  The file's bytes are a term
nested as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Hashing.SipHash.File

file_theorems siphash compiled "../../../build/verified/siphash.wasm" from compiled.bytes

end Library.Hashing.SipHash.File
