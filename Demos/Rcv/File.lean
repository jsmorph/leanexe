import Demos.Rcv.Compiled
import LeanExe.Pipeline.FileBytes

/-! The file theorems of `build/verified/rcvCount.wasm`, which `tests/verified/run.sh` checks after
it writes the file: the file holds `encode compiled.module`, and it decodes to the module of
`compiled.bytes`, whose export `count` `Demos/Rcv/VerifiedCall.lean` describes. -/

namespace Demos.Rcv.File

open Demos.Rcv.Program

file_theorems rcvCount compiled "../../build/verified/rcvCount.wasm" from compiled.bytes

end Demos.Rcv.File
