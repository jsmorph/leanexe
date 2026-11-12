import Demos.Events.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/events.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Events/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Events.File

open Demos.Events

file_theorems events compiled "../../build/verified/events.wasm" from compiled.bytes

end Demos.Events.File
