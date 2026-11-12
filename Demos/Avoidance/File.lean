import Demos.Avoidance.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/avoidance.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Avoidance/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Avoidance.File

open Demos.Avoidance

file_theorems avoidance compiled "../../build/verified/avoidance.wasm" from compiled.bytes

end Demos.Avoidance.File
