import Demos.Energy.Verified
import LeanExe.Pipeline.FileBytes

/-! The file theorems of `build/verified/energy.wasm`, which `tests/verified/run.sh` checks with
`tools/leanrun --timeout 10m lake env lean Demos/Energy/File.lean` after it writes the file.  The
file holds `encode compiled.module`, which `compiled.encoded` states as literal bytes, so it
decodes to the module whose `authorize` export `compiled.authorize.implements` describes. -/

namespace Demos.Energy.File

open Demos.Energy.Verified

file_theorems energy compiled "../../build/verified/energy.wasm" from compiled.bytes

end Demos.Energy.File
