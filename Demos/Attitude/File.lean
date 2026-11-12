import Demos.Attitude.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/attitude.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Attitude/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Attitude.File

open Demos.Attitude

file_theorems attitude compiled "../../build/verified/attitude.wasm" from compiled.bytes

end Demos.Attitude.File
