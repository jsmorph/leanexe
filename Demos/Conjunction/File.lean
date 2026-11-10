import Demos.Conjunction.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/conjunction.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Conjunction/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Conjunction.File

open Demos.Conjunction

file_theorems conjunction compiled "../../build/verified/conjunction.wasm" from compiled.bytes

end Demos.Conjunction.File
