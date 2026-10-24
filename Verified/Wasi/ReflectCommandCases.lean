import Verified.Wasi.ReflectCommand
import Verified.Wasi.ReflectProgramCases

namespace Verified.Wasi.ReflectCommandCases

open Verified.Wasi.ReflectProgramCases

verified_compile_wasi callable :=
  [lookup, boundLookup, pureByte, helper, caller, main, borrowBytes, ownBytes, packetHelper, argumentCaller]

verified_compile_wasi command (main := main) :=
  [lookup, boundLookup, pureByte, helper, caller, main, borrowBytes, ownBytes, packetHelper, argumentCaller]

#guard callable.module.exports.map Wasm.Export.name =
  ["alloc", "release", "helper", "caller", "main", "borrowBytes", "ownBytes", "packetHelper", "argumentCaller"]
#guard command.module.exports.map Wasm.Export.name = ["_start"]
#guard callable.literalPool.base = 4128
#guard callable.literalPool.values = [[9, 8], [65, 0, 255]]

end Verified.Wasi.ReflectCommandCases
