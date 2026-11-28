module

public import Demos.Rcv.Maine.Tabulate
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! The file theorems of `build/verified/rcvMaine.wasm`, which `tests/verified/run.sh` checks after
it writes the file: the file holds `encode compiled.module`, and it decodes to the module of
`compiled.bytes`, whose exports `Demos/Rcv/Maine/TabulateCall.lean` describes. -/

namespace Demos.Rcv.Maine.TabulateFile

open Demos.Rcv.Maine.TabulateProgram

file_theorems rcvMaine compiled "../../../build/verified/rcvMaine.wasm" from compiled.bytes

end Demos.Rcv.Maine.TabulateFile
