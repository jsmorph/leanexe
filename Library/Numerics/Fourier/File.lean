import Library.Numerics.Fourier.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/fourier.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Fourier.File

file_theorems fourier compiled "../../../build/verified/fourier.wasm" from compiled.bytes

end Library.Numerics.Fourier.File
