import LeanExe.Examples.Trees
import Project.Pipeline.Implements

namespace Project.Trees

open LeanExe.Examples.Trees Project.Pipeline

/-- `Tree` as records: `leaf` is the null pointer, and `node l k r` a record of three slots,
the pointer to `l`, the word `k`, and the pointer to `r`. -/
def encode : Tree → Node
  | .leaf => .null
  | .node l k r => .record [.child (encode l), .word k, .child (encode r)]

instance : Encode Tree := ⟨encode⟩

end Project.Trees
