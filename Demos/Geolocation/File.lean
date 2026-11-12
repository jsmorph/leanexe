import Demos.Geolocation.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/geolocation.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Geolocation/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Geolocation.File

open Demos.Geolocation

file_theorems geolocation compiled "../../build/verified/geolocation.wasm" from compiled.bytes

end Demos.Geolocation.File
