import Verified.Bytes.Code

namespace Verified.Bytes

open Wasm

def literalCode (source : UInt64) (bytes : List UInt8) (base : Nat) : Program :=
  [.constI64 source, .localSet base,
   .constI64 (UInt64.ofNat bytes.length), .localSet (base + 1)] ++
    copyOwnedCode base (base + 1) (base + 2)

end Verified.Bytes
