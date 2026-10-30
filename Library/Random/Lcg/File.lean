import Library.Random.Lcg.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/lcg.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Random.Lcg.File

file_theorems lcg compiled "../../../build/verified/lcg.wasm" from compiled.bytes

end Library.Random.Lcg.File
