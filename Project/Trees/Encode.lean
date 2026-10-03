import LeanExe.Examples.Trees
import Project.Pipeline.Implements

namespace Project.Trees

open Wasm LeanExe.Examples.Trees Project.Pipeline

/-- `KeyTree` as records: `leaf` is the null pointer, and `node l k r` a record of three slots,
the pointer to `l`, the word `k`, and the pointer to `r`. -/
def encode : KeyTree → Node
  | .leaf => .null
  | .node l k r => .record [.child (encode l), .word k, .child (encode r)]

instance : Encode KeyTree := ⟨encode⟩

/-- The positivity premise for `KeyTree`: every record has three slots. -/
theorem slotRegions_pos (store : Store Unit) :
    ∀ (t : KeyTree) (p : UInt64), ∀ b ∈ Node.slotRegions store p (encode t), 0 < b.2
  | .leaf, _, b, hb => nomatch hb
  | .node l k r, p, b, hb => by
      simp only [encode, Node.slotRegions, slotsRegions, List.length_cons, List.length_nil,
        List.append_nil, List.mem_cons, List.mem_append] at hb
      rcases hb with rfl | hb | hb
      · show 0 < 8 * (0 + 1 + 1 + 1); decide
      · exact slotRegions_pos store l _ b hb
      · exact slotRegions_pos store r _ b hb

end Project.Trees
