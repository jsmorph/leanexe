import Library.Queues.BinaryHeap.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/heapQueue.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Queues.BinaryHeap.File

file_theorems heapQueue compiled "../../../build/verified/heapQueue.wasm" from compiled.bytes

end Library.Queues.BinaryHeap.File
