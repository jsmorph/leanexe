import Demos.Rcv.Tabulate
import LeanExe.Pipeline.FileBytes

/-! The file theorems of `build/verified/rcvTabulate.wasm`, which `tests/verified/run.sh` checks
after it writes the file: the file holds `encode compiled.module`, and it decodes to the module of
`compiled.bytes`, whose export `tabulate` `Demos/Rcv/TabulateCall.lean` describes. -/

namespace Demos.Rcv.TabulateFile

open Demos.Rcv.TabulateProgram

file_theorems rcvTabulate compiled "../../build/verified/rcvTabulate.wasm" from compiled.bytes

end Demos.Rcv.TabulateFile
