import Demos.Drone.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/drone.wasm`: the file holds
`encode Verified.compiled.module`, and it decodes to the module of `Verified.compiled.bytes`. -/

namespace Demos.Drone.File

file_theorems drone Verified.compiled "../../build/verified/drone.wasm" from Verified.compiled.bytes

end Demos.Drone.File
