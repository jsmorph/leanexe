import Demos.Energy.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/energy.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Energy/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module whose `authorize` export `compiled.authorize.implements` describes. -/

namespace Demos.Energy.File

open Demos.Energy.Verified

file_theorems energy compiled "../../build/verified/energy.wasm" from compiled.bytes

end Demos.Energy.File
