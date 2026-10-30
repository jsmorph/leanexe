import Library.Numerics.Float64.Asin.AsinBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/asin.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Asin/AsinFile.lean`: the file holds
`encode Asin.compiled.module`, so it decodes to the module of
`AsinBytes.asin_module_accuracy`. -/

namespace Library.Numerics.Float64.Asin.AsinFile

file_theorems asin Asin.compiled "../../../../build/verified/asin.wasm"
  from AsinBytes.asin_module_accuracy

end Library.Numerics.Float64.Asin.AsinFile
