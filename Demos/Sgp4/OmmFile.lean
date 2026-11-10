import Demos.Sgp4.OmmVerified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sgp4omm.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Sgp4/OmmFile.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Sgp4.Omm.File

open Demos.Sgp4.Omm

file_theorems sgp4omm compiled "../../build/verified/sgp4omm.wasm" from compiled.bytes

end Demos.Sgp4.Omm.File
