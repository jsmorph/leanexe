import Library.Regex.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/regex.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Regex/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module of the call theorem of `Library.Regex.Bytes`.  The file's bytes are a term nested as deep
as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Regex.File

file_theorems regex compiled "../../build/verified/regex.wasm" from compiled.bytes

end Library.Regex.File
