import Library.Hashing.Crc.Bitwise.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/crcBitwise.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Hashing.Crc.Bitwise.File

file_theorems crcBitwise compiled "../../../../build/verified/crcBitwise.wasm" from compiled.bytes

end Library.Hashing.Crc.Bitwise.File
