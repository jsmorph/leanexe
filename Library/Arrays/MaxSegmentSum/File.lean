module

public import Library.Arrays.MaxSegmentSum.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/libmss.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Arrays.MaxSegmentSum.File

file_theorems libmss compiled "../../../build/verified/libmss.wasm" from compiled.bytes

end Library.Arrays.MaxSegmentSum.File
