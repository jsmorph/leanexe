import Demos.PassiveSafety.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/passivesafety.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/PassiveSafety/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.PassiveSafety.File

open Demos.PassiveSafety

file_theorems passivesafety compiled "../../build/verified/passivesafety.wasm" from compiled.bytes

end Demos.PassiveSafety.File
