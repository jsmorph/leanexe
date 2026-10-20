import Verified.Tree
import LeanExe.Runtime.Defs

namespace Verified

open Wasm LeanExe.Runtime

def treeHeaderCopyCode (shape : TreeShape) (base : Nat) : Program :=
  [.constI64 (UInt64.ofNat (8 * shape.fields.length)), .call 0, .localSet base] ++
    headerStore base 24 [.constI64 1] ++
    headerStore base 16 [.constI64 (UInt64.ofNat shape.fields.length)] ++ [.localGet base]

end Verified
