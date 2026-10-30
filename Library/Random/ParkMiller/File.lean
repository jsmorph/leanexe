import Library.Random.ParkMiller.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/parkmiller.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Random.ParkMiller.File

file_theorems parkmiller compiled "../../../build/verified/parkmiller.wasm" from compiled.bytes

end Library.Random.ParkMiller.File
