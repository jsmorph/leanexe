import Library.Trees.WordTree.Program
import LeanExe.Pipeline.Slotted

namespace Library.Trees.WordTree

open Wasm Library.Trees.WordTree LeanExe.Pipeline

/-- `KeyTree` as records: `leaf` is the null pointer, and `node l k r` a record of three slots,
the pointer to `l`, the word `k`, and the pointer to `r`. -/
def encode : Library.Trees.WordTree.KeyTree → Node
  | .leaf => .null
  | .node l k r => .record [.child (encode l), .word k, .child (encode r)]

instance : Encode Library.Trees.WordTree.KeyTree := ⟨encode⟩

theorem encode_slotted : ∀ t : Library.Trees.WordTree.KeyTree, (encode t).Slotted
  | .leaf => trivial
  | .node l _ r => ⟨List.cons_ne_nil _ _, encode_slotted l, encode_slotted r, trivial⟩

instance : EncodeSlotted Library.Trees.WordTree.KeyTree := ⟨encode_slotted⟩

theorem encode_wellFormed : ∀ t : Library.Trees.WordTree.KeyTree, (encode t).WellFormed
  | .leaf => trivial
  | .node l _ r => ⟨by simp, trivial, encode_wellFormed l, encode_wellFormed r, trivial⟩

instance : EncodeWellFormed Library.Trees.WordTree.KeyTree := ⟨encode_wellFormed⟩

end Library.Trees.WordTree
