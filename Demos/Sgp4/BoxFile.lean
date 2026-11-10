import Demos.Sgp4.BoxVerified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sgp4box.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Sgp4/BoxFile.lean`: the file holds
`encode boxCompiled.module`, and it decodes to the module of `boxCompiled.bytes`. -/

namespace Demos.Sgp4.BoxFile

open Demos.Sgp4

file_theorems sgp4box boxCompiled "../../build/verified/sgp4box.wasm" from boxCompiled.bytes

end Demos.Sgp4.BoxFile
