import Examples.SumArray.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/folds.wasm`: the file holds
`encode compiledFolds.module`, and it decodes to the module of `compiledFolds.bytes`. -/

namespace Examples.SumArray.FileFolds

file_theorems folds compiledFolds "../../build/verified/folds.wasm" from compiledFolds.bytes

end Examples.SumArray.FileFolds
