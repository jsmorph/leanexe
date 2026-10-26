import Verified.Tree
import LeanExe.Runtime.Defs

namespace Verified

open Wasm LeanExe.Runtime

def treeHeaderCopyCode (shape : TreeShape) (r : Fin shape.records) (base : Nat) : Program :=
  [.constI64 (UInt64.ofNat (8 * shape.width r)), .call 0, .localSet base] ++
    headerStore base 24 [.constI64 1] ++
    headerStore base 16 [.constI64 (UInt64.ofNat (shape.width r))] ++ [.localGet base]

end Verified
