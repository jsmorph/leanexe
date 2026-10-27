import LeanExe.Runtime.Defs

namespace Verified.Bytes

open Wasm

def buildLoopCode (count destination index : Nat) (element : Program) : Program :=
  [.constI64 0, .localSet index,
   .block 0 0 [.loop 0 0
     ([.localGet index, .localGet count, .geUI64, .br_if 1,
       .localGet destination, .localGet index, .addI64, .wrapI64] ++
      element ++ [.wrapI64, .store8 0,
        .localGet index, .constI64 1, .addI64, .localSet index, .br 0])]]

def buildCode (count destination index : Nat) (element : Program) : Program :=
  [.localGet count, .constI64 4294967296, .geUI64,
   .iff 0 0 [.unreachable] [],
   .localGet count, .constI64 0, .eqI64,
   .iff 0 1 [.constI64 0]
     ([.localGet count, .call 0, .localSet destination] ++
      buildLoopCode count destination index element ++ [.localGet destination]) [] [.i64],
   .localGet count]

end Verified.Bytes
