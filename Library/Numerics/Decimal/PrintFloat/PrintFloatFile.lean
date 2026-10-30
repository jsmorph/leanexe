import Library.Numerics.Decimal.PrintFloat.PrintFloatBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `build/verified/printfloat.wasm` is written by `tools/Emit.lean`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Decimal/PrintFloat/PrintFloatFile.lean`: the file holds
`encode PrintFloat.compiled.module`, so it decodes to the module of the four byte theorems of
`PrintFloatBytes`. -/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloatFile

file_theorems print PrintFloat.compiled "../../../../build/verified/printfloat.wasm"
  from PrintFloatBytes.print64_bytes_accuracy, PrintFloatBytes.print64Ecma_bytes_accuracy,
    PrintFloatBytes.print32_bytes_accuracy, PrintFloatBytes.print32Ecma_bytes_accuracy

end Library.Numerics.Decimal.PrintFloat.PrintFloatFile
