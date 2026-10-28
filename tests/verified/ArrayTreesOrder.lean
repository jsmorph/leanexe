import Verified.Reflect.Command

/-! `verified_recursive_type` rejects an `Encode` instance that places an array slot of a record
before a word or child slot, and the error names the field.  The record layout of the verified
compiler holds a record's word and child slots first and its array slots after them. -/

namespace Verified.Tests.ArrayTreesOrder

open LeanExe.Pipeline

inductive Mixed where
  | leaf
  | node (left : Mixed) (items : Array UInt64) (key : UInt64)

def Mixed.encode : Mixed → Node
  | .leaf => .null
  | .node l xs k => .record [.child l.encode, .array xs, .word k]

instance : Encode Mixed := ⟨Mixed.encode⟩

/--
error: verified_recursive_type: the `Encode` instance of Verified.Tests.ArrayTreesOrder.Mixed places the array field `items` of Verified.Tests.ArrayTreesOrder.Mixed.node before a word or child slot; a record holds its word and child slots first and then its array slots, each group in the order of the fields
-/
#guard_msgs in
verified_recursive_type Mixed

end Verified.Tests.ArrayTreesOrder
