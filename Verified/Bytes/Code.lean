import LeanExe.Runtime.Defs

namespace Verified.Bytes

open Wasm

def getCode (root length index : Nat) : Program :=
  [.localGet index, .localGet length, .ltUI64,
   .iff 0 1
     [.localGet root, .localGet index, .addI64, .wrapI64, .load8U 0, .extendUI32]
     [.constI64 0]]

def copyByteCode (source destination index : Nat) : Program :=
  [.localGet destination, .localGet index, .addI64, .wrapI64,
   .localGet source, .localGet index, .addI64, .wrapI64, .load8U 0, .store8 0]

def copyCode (source destination count index : Nat) : Program :=
  [.constI64 0, .localSet index,
   .block 0 0 [.loop 0 0
     ([.localGet index, .localGet count, .geUI64, .br_if 1] ++
      copyByteCode source destination index ++
      [.localGet index, .constI64 1, .addI64, .localSet index, .br 0])]]

def copyOwnedCode (source length base : Nat) : Program :=
  [.localGet length, .constI64 0, .eqI64,
   .iff 0 2 [.constI64 0, .constI64 0]
     ([.localGet length, .call 0, .localSet base] ++
      copyCode source base length (base + 1) ++ [.localGet base, .localGet length])]

end Verified.Bytes
