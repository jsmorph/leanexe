import LeanExe.Examples.Trees
import Project.Pipeline.Slotted

namespace Project.Trees

open Wasm LeanExe.Examples.Trees Project.Pipeline

/-- `KeyTree` as records: `leaf` is the null pointer, and `node l k r` a record of three slots,
the pointer to `l`, the word `k`, and the pointer to `r`. -/
def encode : KeyTree → Node
  | .leaf => .null
  | .node l k r => .record [.child (encode l), .word k, .child (encode r)]

instance : Encode KeyTree := ⟨encode⟩

theorem encode_slotted : ∀ t : KeyTree, (encode t).Slotted
  | .leaf => trivial
  | .node l _ r => ⟨List.cons_ne_nil _ _, encode_slotted l, encode_slotted r, trivial⟩

instance : EncodeSlotted KeyTree := ⟨encode_slotted⟩

end Project.Trees
