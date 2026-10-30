import Library.Lists.Word.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/liblists.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Lists.Word.File

file_theorems liblists compiled "../../../build/verified/liblists.wasm" from compiled.bytes

end Library.Lists.Word.File
