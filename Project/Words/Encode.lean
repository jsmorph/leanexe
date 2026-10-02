import LeanExe.Examples.Words
import Project.Pipeline.Implements

namespace Project.Words

open LeanExe.Examples.Words Project.Pipeline

/-- `Words` as records, the layout of `List UInt64`: `nil` is the null pointer, and `cons x w`
a record of two slots, the word `x` and the pointer to `w`. -/
def encode : Words → Node
  | .nil => .null
  | .cons x w => .record [.word x, .child (encode w)]

instance : Encode Words := ⟨encode⟩

end Project.Words
