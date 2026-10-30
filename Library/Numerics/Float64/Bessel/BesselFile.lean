import Library.Numerics.Float64.Bessel.BesselBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/bessel.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Bessel/BesselFile.lean`: the file holds
`encode Bessel.compiled.module`, which `Bessel.compiled.encoded` states as literal bytes, so it
decodes to the module of `BesselBytes.bessel_module_accuracy`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Numerics.Float64.Bessel.BesselFile

file_theorems bessel Bessel.compiled "../../../../build/verified/bessel.wasm"
  from BesselBytes.bessel_module_accuracy

end Library.Numerics.Float64.Bessel.BesselFile
