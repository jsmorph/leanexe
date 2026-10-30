import Library.Numerics.Decimal.ParseFloat.ParseFloatBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `build/verified/parsefloat.wasm` is written by `tools/Emit.lean`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Decimal/ParseFloat/ParseFloatFile.lean`: the file holds
`encode ParseFloat.compiled.module`, so it decodes to the module of
`ParseFloatBytes.parse64_bytes_accuracy` and `ParseFloatBytes.parse32_bytes_accuracy`. -/

namespace Library.Numerics.Decimal.ParseFloat.ParseFloatFile

file_theorems parse ParseFloat.compiled "../../../../build/verified/parsefloat.wasm"
  from ParseFloatBytes.parse64_bytes_accuracy, ParseFloatBytes.parse32_bytes_accuracy

end Library.Numerics.Decimal.ParseFloat.ParseFloatFile
