import Examples.Words.Program
import Project.Pipeline.Slotted

namespace Examples.Words

open Examples.Words Project.Pipeline

/-- `Words` as records, the layout of `List UInt64`: `nil` is the null pointer, and `cons x w`
a record of two slots, the word `x` and the pointer to `w`. -/
def encode : Words → Node
  | .nil => .null
  | .cons x w => .record [.word x, .child (encode w)]

instance : Encode Words := ⟨encode⟩

theorem encode_slotted : ∀ w : Words, (encode w).Slotted
  | .nil => trivial
  | .cons _ w => ⟨List.cons_ne_nil _ _, encode_slotted w, trivial⟩

instance : EncodeSlotted Words := ⟨encode_slotted⟩

end Examples.Words
