import Demos.RandomChoice.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/randomChoice.wasm`: the file
holds `encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.RandomChoice.File

open Demos.RandomChoice

file_theorems randomChoice compiled "../../build/verified/randomChoice.wasm" from compiled.bytes

end Demos.RandomChoice.File
