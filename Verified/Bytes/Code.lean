import LeanExe.Runtime.Defs

namespace Verified.Bytes

open Wasm

def getCode (root length index : Nat) : Program :=
  [.localGet index, .localGet length, .ltUI64,
   .iff 0 1
     [.localGet root, .localGet index, .addI64, .wrapI64, .load8U 0, .extendUI32]
     [.constI64 0] [] [.i64]]

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
   .iff 0 1 [.constI64 0]
     ([.localGet length, .call 0, .localSet base] ++
      copyCode source base length (base + 1) ++ [.localGet base]) [] [.i64],
   .localGet length]

/-- Code that releases the object of the buffer whose root and length are in the locals `root`
and `length` when its length is 0, and then sets the root to 0, so that the root of an empty
buffer is 0. -/
def normalizeCode (root length : Nat) : Program :=
  [.localGet length, .eqzI64, .iff 0 0 [.localGet root, .call 1, .constI64 0, .localSet root] []]

end Verified.Bytes
