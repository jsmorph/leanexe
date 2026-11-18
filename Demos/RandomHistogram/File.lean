import Demos.RandomHistogram.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/randomHistogram.wasm`: the file
holds `encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.RandomHistogram.File

open Demos.RandomHistogram

file_theorems randomHistogram compiled "../../build/verified/randomHistogram.wasm" from compiled.bytes

end Demos.RandomHistogram.File
