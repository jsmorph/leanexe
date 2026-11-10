import Demos.Sgp4.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sgp4.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Sgp4/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Sgp4.File

open Demos.Sgp4

file_theorems sgp4 compiled "../../build/verified/sgp4.wasm" from compiled.bytes

end Demos.Sgp4.File
