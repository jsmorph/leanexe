import Library.Trees.Avl.Program
import LeanExe.Pipeline.Slotted

namespace Library.Trees.Avl

open Wasm LeanExe.Pipeline

/-- `AvlTree` as records: `leaf` is the null pointer, and `node l k b r` a record of four slots,
the pointer to `l`, the words `k` and `b`, and the pointer to `r`. -/
def encode : AvlTree → Node
  | .leaf => .null
  | .node l k b r => .record [.child (encode l), .word k, .word b, .child (encode r)]

instance : Encode AvlTree := ⟨encode⟩

theorem encode_slotted : ∀ t : AvlTree, (encode t).Slotted
  | .leaf => trivial
  | .node l _ _ r => ⟨List.cons_ne_nil _ _, encode_slotted l, encode_slotted r, trivial⟩

instance : EncodeSlotted AvlTree := ⟨encode_slotted⟩

theorem encode_wellFormed : ∀ t : AvlTree, (encode t).WellFormed
  | .leaf => trivial
  | .node l _ _ r => ⟨by simp, trivial, encode_wellFormed l, encode_wellFormed r, trivial⟩

instance : EncodeWellFormed AvlTree := ⟨encode_wellFormed⟩

end Library.Trees.Avl
