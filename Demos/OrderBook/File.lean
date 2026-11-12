import Demos.OrderBook.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/orderbook.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/OrderBook/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.OrderBook.File

open Demos.OrderBook.Verified

file_theorems orderbook compiled "../../build/verified/orderbook.wasm" from compiled.bytes

end Demos.OrderBook.File
